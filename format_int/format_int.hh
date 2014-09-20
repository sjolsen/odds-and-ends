#ifndef FORMAT_INT_HH
#define FORMAT_INT_HH

#include <type_traits>
#include <limits>
#include <climits>
#include <cstdint>
#include <algorithm>

#define requires(boolean_constant_expression) \
	typename = typename std::enable_if <boolean_constant_expression>::type
#define specialization_requires(boolean_constant_expression) \
	typename std::enable_if <boolean_constant_expression>::type

template <std::size_t, typename = void> struct unsigned_type_impl;
template <> struct unsigned_type_impl <8>  { using type = std::uint_least8_t;  };
template <> struct unsigned_type_impl <16> { using type = std::uint_least16_t; };
template <> struct unsigned_type_impl <32> { using type = std::uint_least32_t; };
template <> struct unsigned_type_impl <64> { using type = std::uint_least64_t; };
template <std::size_t Bits> using unsigned_type = typename unsigned_type_impl <Bits>::type;
template <std::size_t Bits> struct unsigned_type_impl <Bits, specialization_requires (Bits < 8)>               { using type = unsigned_type <8>;  };
template <std::size_t Bits> struct unsigned_type_impl <Bits, specialization_requires (8 < Bits && Bits < 16)>  { using type = unsigned_type <16>; };
template <std::size_t Bits> struct unsigned_type_impl <Bits, specialization_requires (16 < Bits && Bits < 32)> { using type = unsigned_type <32>; };
template <std::size_t Bits> struct unsigned_type_impl <Bits, specialization_requires (32 < Bits && Bits < 64)> { using type = unsigned_type <64>; };
template <std::size_t Bits> struct unsigned_type_impl <Bits, specialization_requires (64 < Bits && Bits <= (sizeof (std::uintmax_t) * CHAR_BIT))> { using type = std::uintmax_t; };

template <typename SInt>
static inline constexpr
std::uintmax_t safe_abs_impl (SInt value, std::true_type is_signed)
{
	return (value >= 0) ? value : (std::uintmax_t {1} + (SInt {-1} - value));
}

template <typename UInt>
static inline constexpr
std::uintmax_t safe_abs_impl (UInt value, std::false_type is_signed)
{
	return value;
}

template <typename Int, requires (std::is_integral <Int>::value)>
static inline constexpr
std::uintmax_t safe_abs (Int value)
{
	return safe_abs_impl (value, std::is_signed <Int> {});
}

static inline constexpr
std::uintmax_t cmax (std::uintmax_t a, std::uintmax_t b)
{
	return (b > a) ? b : a;
}

template <typename Integral>
static inline constexpr
std::uintmax_t max_abs ()
{
	return cmax (safe_abs (std::numeric_limits <Integral>::min ()),
	             safe_abs (std::numeric_limits <Integral>::max ()));
}



static inline constexpr
std::uintmax_t ceil_log_of_oneplus (std::uintmax_t value, std::uintmax_t base, std::uintmax_t acc = 0)
{
	return (value == 0) ? acc : ceil_log_of_oneplus (value / base, base, acc + 1);
}

static inline constexpr
std::uintmax_t ceil_log (std::uintmax_t value, std::uintmax_t base)
{
	return (value == 0) ? 0 : ceil_log_of_oneplus (value - 1, base);
}

template <std::size_t Chars>
struct format_buffer
{
	unsigned_type <ceil_log (Chars, 2)> length;
	char buffer [Chars];
};

std::size_t format_uint_2special (char* buffer, std::uintmax_t value, std::uint_fast8_t base_power);
std::size_t format_uint_generic (char* buffer, std::uintmax_t value, std::uint_fast8_t base);

template <std::uint_fast8_t Base, typename UInt>
static inline
auto format_impl (UInt value, std::false_type is_signed)
{
	// ceil(log) characters for text, one for \0 terminator
	format_buffer <ceil_log_of_oneplus (max_abs <UInt> (), Base) + 1> buffer;

	switch (Base)
	{
	case 2:  buffer.length = format_uint_2special (buffer.buffer, value, 1);    break;
	case 4:  buffer.length = format_uint_2special (buffer.buffer, value, 2);    break;
	case 8:  buffer.length = format_uint_2special (buffer.buffer, value, 3);    break;
	case 16: buffer.length = format_uint_2special (buffer.buffer, value, 4);    break;
	default: buffer.length = format_uint_generic  (buffer.buffer, value, Base); break;
	}

	return buffer;
}

template <std::uint_fast8_t Base, typename SInt>
static inline
auto format_impl (SInt value, std::true_type is_signed)
{
	// one for negative sign, ceil(log) characters for text, one for \0 terminator
	format_buffer <1 + ceil_log_of_oneplus (max_abs <SInt> (), Base) + 1> buffer;
	char* bstart = buffer.buffer;

	buffer.length = 0;
	if (value < 0)
	{
		*bstart++ = '-';
		++buffer.length;
	}

	switch (Base)
	{
	case 2:  buffer.length += format_uint_2special (bstart, safe_abs (value), 1);    break;
	case 4:  buffer.length += format_uint_2special (bstart, safe_abs (value), 2);    break;
	case 8:  buffer.length += format_uint_2special (bstart, safe_abs (value), 3);    break;
	case 16: buffer.length += format_uint_2special (bstart, safe_abs (value), 4);    break;
	default: buffer.length += format_uint_generic  (bstart, safe_abs (value), Base); break;
	}

	return buffer;
}

template <std::uint_fast8_t Base = 10, typename Int, requires (2 <= Base && Base <= 16)>
static inline
auto format (Int value)
{
	return format_impl <Base> (value, std::is_signed <Int> {});
}

#endif
