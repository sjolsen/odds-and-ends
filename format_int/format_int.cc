#include "format_int.hh"

static inline constexpr
char clookup (std::uint_fast8_t digit)
{
	return (digit < 10) ? ('0' + digit) : ('A' + (digit - 10));
}

char* format_uint_2special (char* buffer_end, std::uintmax_t value, std::uint_fast8_t base_power)
{
	std::uintmax_t mask = 0;
	--mask;
	mask >>= (sizeof (std::uintmax_t) * CHAR_BIT) - base_power;

	char* cursor = buffer_end - 1;
	*cursor = '\0';

	do
	{
		--cursor;
		*cursor = clookup (value & mask);
		value >>= base_power;
	}
	while (value != 0);

	return cursor;
}

char* format_uint_generic (char* buffer_end, std::uintmax_t value, std::uint_fast8_t base)
{
	char* cursor = buffer_end - 1;
	*cursor = '\0';

	do
	{
		--cursor;
		*cursor = clookup (value % base);
		value /= base;
	}
	while (value != 0);

	return cursor;
}
