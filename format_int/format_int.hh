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

template <typename Int, std::uint_fast8_t Base>
static inline constexpr
std::size_t buffer_length ()
{
	// ceil(log) characters for text, one for \0 terminator, one for negative sign
	return ceil_log_of_oneplus (max_abs <Int> (), Base) + 1 + (std::is_signed <Int>::value ? 1 : 0);
}

template <std::size_t Chars>
struct format_buffer
{
	unsigned_type <ceil_log (Chars, 2)> begin_index;
	char buffer [Chars];

	auto begin ()       { return buffer + begin_index; }
	auto begin () const { return buffer + begin_index; }
	auto end ()         { return buffer + Chars - 1; }
	auto end () const   { return buffer + Chars - 1; }
};

char* format_uint_2special (char* buffer_end, std::uintmax_t value, std::uint_fast8_t base_power);
char* format_uint_generic (char* buffer_end, std::uintmax_t value, std::uint_fast8_t base);

template <std::uint_fast8_t Base = 10, typename Int>
static inline
auto format (Int value)
{
	format_buffer <buffer_length <Int, Base> ()> buffer;
	auto buffer_end = buffer.buffer + buffer_length <Int, Base> ();

	char* begin;
	switch (Base)
	{
	case 2:  begin = format_uint_2special (buffer_end, safe_abs (value), 1);    break;
	case 4:  begin = format_uint_2special (buffer_end, safe_abs (value), 2);    break;
	case 8:  begin = format_uint_2special (buffer_end, safe_abs (value), 3);    break;
	case 16: begin = format_uint_2special (buffer_end, safe_abs (value), 4);    break;
	default: begin = format_uint_generic  (buffer_end, safe_abs (value), Base); break;
	}

	if (value < 0)
		*--begin = '-';
	buffer.begin_index = begin - buffer.buffer;

	return buffer;
}

#endif
