#include "mpz.hh"
#include <type_traits>

template <std::uint32_t n>
struct pred_unit {
	static const std::uint32_t lo = n - 1;
	static const bool carry = (n == 0);
};

template <typename n>
struct pred_nonnormal;

template <typename n>
using pred = normalize <pred_nonnormal <n> >;

template <bool carry, typename n>
struct pred_nonnormal_rest {
	using value = typename n::rest;
};

template <typename n>
struct pred_nonnormal_rest <true, n> {
	using value = pred <typename n::rest>;
};

template <typename n>
struct pred_nonnormal {
	using x = pred_unit <n::lsw>;
	static const std::uint32_t lsw = x::lo;
	using rest = typename pred_nonnormal_rest <x::carry, n>::value;
};

template <>
struct pred_nonnormal <zero>;



template <std::uint32_t n>
struct suc_unit {
	static const std::uint32_t lo = n + 1;
	static const bool carry = (lo == 0);
};

template <typename n>
struct suc {
	using x = suc_unit <n::lsw>;
	static const std::uint32_t lsw = x::lo;
	using rest = typename std::conditional <x::carry,
	                                        suc <typename n::rest>,
	                                        typename n::rest>::type;
};

template <>
struct suc <zero> {
	static const std::uint32_t lsw = 1;
	using rest = zero;
};



template <typename n>
struct factorial_impl;

template <typename n>
using factorial = typename factorial_impl <n>::value;

template <typename n>
struct factorial_impl {
	using value = mul <n, factorial <pred <n> > >;
};

template <>
struct factorial_impl <zero> {
	using value = suc <zero>;
};


#include <iostream>

using one   = suc <zero>;
using two   = suc <one>;
using three = suc <two>;
using four  = suc <three>;
using five  = suc <four>;

int main ()
{
	std::cout << from_integer <factorial <zero> >::value ()  << std::endl;
	std::cout << from_integer <factorial <one> >::value ()   << std::endl;
	std::cout << from_integer <factorial <two> >::value ()   << std::endl;
	std::cout << from_integer <factorial <three> >::value () << std::endl;
	std::cout << from_integer <factorial <four> >::value ()  << std::endl;
	std::cout << from_integer <factorial <five> >::value ()  << std::endl;

}
