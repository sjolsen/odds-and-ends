struct zero {};


#include <cstdint>

template <std::uint32_t m, std::uint32_t n, std::uint32_t c>
struct addc_unit {
	static const std::uint64_t m64 = m;
	static const std::uint64_t n64 = n;
	static const std::uint64_t c64 = c;
	static const std::uint32_t lo  = (m64 + n64 + c64) & 0xFFFFFFFF;
	static const std::uint32_t hi  = (m64 + n64 + c64) >> 32;
};

template <typename m, typename n, std::uint32_t c>
struct addc;

template <typename m, typename n, std::uint32_t c>
struct addc_reduce {
	using value = addc <m, n, c>;
};

template <>
struct addc_reduce <zero, zero, 0> {
	using value = zero;
};

template <std::uint32_t c>
struct addc <zero, zero, c> {
	static const std::uint32_t lsw = c;
	using rest = zero;
};

template <typename n, std::uint32_t c>
struct addc <zero, n, c> {
	using x = addc_unit <0, n::lsw, c>;
	static const std::uint32_t lsw = x::lo;
	using rest = typename addc_reduce <zero, typename n::rest, x::hi>::value;
};

template <typename m, std::uint32_t c>
struct addc <m, zero, c> {
	using x = addc_unit <m::lsw, 0, c>;
	static const std::uint32_t lsw = x::lo;
	using rest = typename addc_reduce <typename m::rest, zero, x::hi>::value;
};

template <typename m, typename n, std::uint32_t c>
struct addc {
	using x = addc_unit <m::lsw, n::lsw, c>;
	static const std::uint32_t lsw = x::lo;
	using rest = typename addc_reduce <typename m::rest, typename n::rest, x::hi>::value;
};


template <typename m, typename n>
using add = addc <m, n, 0>;



template <std::uint32_t m, std::uint32_t n, std::uint32_t c>
struct mul_unit {
	static const std::uint64_t m64 = m;
	static const std::uint64_t n64 = n;
	static const std::uint32_t lo  = (m64 * n64 + c) & 0xFFFFFFFF;
	static const std::uint32_t hi  = (m64 * n64 + c) >> 32;
};

template <std::uint32_t m, typename n, std::uint32_t c>
struct mul_row {
	using x = mul_unit <m, n::lsw, c>;
	static const std::uint32_t lsw = x::lo;
	using rest = mul_row <m, typename n::rest, x::hi>;
};

template <std::uint32_t m, std::uint32_t c>
struct mul_row <m, zero, c> {
	static const std::uint32_t lsw = c;
	using rest = zero;
};

template <typename n, std::uint32_t c>
struct mul_row <0, n, c> {
	static const std::uint32_t lsw = c;
	using rest = zero;
};

template <typename m, typename n>
struct mul_nz;

template <typename m, typename n>
struct mul_impl {
	using value = mul_nz <m, n>;
};

template <typename n>
struct mul_impl <zero, n> {
	using value = zero;
};

template <typename m, typename n>
using mul = typename mul_impl <m, n>::value;

template <typename m, typename n>
struct mul_nz {
	using x = mul_row <m::lsw, n, 0>;
	static const std::uint32_t lsw = x::lsw;
	using rest = add <mul <typename m::rest, n>, typename x::rest>;
};


#include <limits>

template <std::uintmax_t n>
struct integer_impl;

template <std::uintmax_t n>
using integer = typename integer_impl <n>::value;

template <std::uintmax_t n>
struct integer_impl2 {
	static const std::uint32_t lsw = n & 0xFFFFFFFF;
	using rest = integer <(n >> 32)>;
};

template <std::uintmax_t n>
struct integer_impl {
	using value = integer_impl2 <n>;
};

template <>
struct integer_impl <0> {
	using value = zero;
};


#include <gmpxx.h>

template <typename n>
struct from_integer {
	static mpz_class value () {
		return (from_integer <typename n::rest>::value () << 32) + n::lsw;
	}
};

template <>
struct from_integer <zero> {
	static mpz_class value () {
		return 0;
	}
};


#include <iostream>

using five        = integer <5>;
using twenty_five = mul <five, five>;
using biggest     = integer <std::numeric_limits <std::uint32_t>::max ()>;
using biggest2    = add <biggest, biggest>;
using bigbig      = mul <biggest, biggest>;
using bbbbig      = mul <bigbig, bigbig>;

int main ()
{
	std::cout << from_integer <zero>::value ()        << std::endl;
	std::cout << from_integer <twenty_five>::value () << std::endl;
	std::cout << from_integer <five>::value ()        << std::endl;
	std::cout << from_integer <biggest>::value ()     << std::endl;
	std::cout << from_integer <biggest2>::value ()    << std::endl;
	std::cout << from_integer <bigbig>::value ()      << std::endl;
	std::cout << from_integer <bbbbig>::value ()      << std::endl;
}
