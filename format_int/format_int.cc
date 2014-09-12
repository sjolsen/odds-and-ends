#include "format_int.hh"

static inline constexpr
char clookup (std::uint_fast8_t digit)
{
	return (digit < 10) ? ('0' + digit) : ('A' + (digit - 10));
}

std::size_t format_uint_2special (char* buffer, std::uintmax_t value, std::uint_fast8_t base_power)
{
	std::uintmax_t mask = 0;
	--mask;
	mask >>= (sizeof (std::uintmax_t) * CHAR_BIT) - base_power;

	char* cursor = buffer;
	do
	{
		*cursor = clookup (value & mask);
		value >>= base_power;
		++cursor;
	}
	while (value != 0);

	std::reverse (buffer, cursor);
	*cursor = '\0';
	return cursor - buffer;
}

std::size_t format_uint_generic (char* buffer, std::uintmax_t value, std::uint_fast8_t base)
{
	char* cursor = buffer;
	do
	{
		*cursor = clookup (value % base);
		value /= base;
		++cursor;
	}
	while (value != 0);

	std::reverse (buffer, cursor);
	*cursor = '\0';
	return cursor - buffer;
}
