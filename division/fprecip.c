#include <stdint.h>

typedef union {
	struct {
		uint32_t mantissa_rep : 23;
		uint32_t exponent_rep : 8;
		uint32_t sign : 1;
	};
	uint32_t rep;
	float value;
} float_rep;

static inline
int32_t float_exponent_decode (uint32_t exponent_rep)
{
	return ((int32_t) exponent_rep) - 127;
}

static inline
uint32_t float_exponent_encode (int32_t exponent)
{
	return (uint32_t) (exponent + 127);
}

static inline
float float_value_with_mantissa (float_rep xrep, uint32_t mantissa_rep)
{
	xrep.mantissa_rep = mantissa_rep;
	return xrep.value;
}

float normalized_reciprocal_mantissa_search (float x, float_rep yrep, uint32_t low, uint32_t high)
{
	if (low == high) {
		yrep.mantissa_rep = low;
		return yrep.value;
	}

	uint32_t mid = low + (high - low + 1) / 2;
	float y = float_value_with_mantissa (yrep, mid);
	if (x * y < 1.0f)
		return normalized_reciprocal_mantissa_search (x, yrep, mid + 1, high);
	if (x * y > 1.0f)
		return normalized_reciprocal_mantissa_search (x, yrep, low, mid - 1);
	yrep.mantissa_rep = mid;
	return yrep.value;
}

float normalized_reciprocal (float x)
{
	float_rep xrep = {.value = x};
	float_rep yrep = {.sign = xrep.sign};

	if (xrep.mantissa_rep == 0) { // mantissa == 1
		yrep.exponent_rep = float_exponent_encode (-float_exponent_decode (xrep.exponent_rep));
		yrep.mantissa_rep = 0;
		return yrep.value;
	}

	yrep.exponent_rep = float_exponent_encode (-float_exponent_decode (xrep.exponent_rep) - 1);
	return normalized_reciprocal_mantissa_search (x, yrep, 0, (1 << 23) - 1);
}


#include <stdio.h>

void format_binary (uint32_t value, char* begin, char* end)
{
	*end = '\0';
	while (end != begin)
	{
		--end;
		*end = ((value & 1) ? '1' : '0');
		value >>= 1;
	}
}

void printrep (float x)
{
	float_rep xrep = {.value = x};
	char buffer [24];
	printf ("%f ", x);
	format_binary (xrep.sign, buffer, buffer + 1);
	printf ("%s ", buffer);
	format_binary (xrep.exponent_rep, buffer, buffer + 8);
	printf ("%s ", buffer);
	format_binary (xrep.mantissa_rep, buffer, buffer + 23);
	printf ("%s", buffer);
}

void test (float x)
{
	printf ("x: ");
	printrep (x);
	printf ("; 1/x: ");
	printrep (1/x);
	printf ("; normrecip: ");
	printrep (normalized_reciprocal (x));
	printf ("\n");
}

int main (void)
{
	for (float x = 0.2f; x < 2.0f; x *= 1.5f)
		test (x);
	for (float x = -0.2f; x > -2.0f; x *= 1.5f)
		test (x);
}
