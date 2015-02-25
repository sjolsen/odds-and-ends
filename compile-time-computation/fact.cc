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
#include <memory>

struct nil {};

template <typename n>
struct alln_n {
	using car = n;
	using cdr = alln_n <suc <n>>;
};

using alln = alln_n <zero>;



template <typename n, typename l>
struct take_impl;

template <typename n, typename l>
using take = typename take_impl <n, l>::value;

template <typename n, typename l>
struct take_impl {
	struct value {
		using car = typename l::car;
		using cdr = take <pred <n>, typename l::cdr>;
	};
};

template <typename l>
struct take_impl <zero, l> {
	using value = nil;
};



struct node;
using list = std::unique_ptr <node>;

struct node {
	mpz_class car;
	list cdr;

	node (mpz_class car, list cdr)
		: car (std::move (car)),
		  cdr (std::move (cdr))
	{
	}
};

template <typename l>
struct from_list {
	static list value () {
		auto car = from_integer <typename l::car>::value ();
		using cdr = typename l::cdr;
		return std::make_unique <node> (std::move (car), from_list <cdr>::value ());
	}
};

template <>
struct from_list <nil> {
	static list value () {
		return nullptr;
	}
};



template <template <typename> class f, typename l>
struct map_impl;

template <template <typename> class f, typename l>
using map = typename map_impl <f, l>::value;

template <template <typename> class f, typename l>
struct map_impl {
	struct value {
		using car = f <typename l::car>;
		using cdr = map <f, typename l::cdr>;
	};
};

template <template <typename> class f>
struct map_impl <f, nil> {
	using value = nil;
};



std::ostream& operator << (std::ostream& os, const list& l)
{
	if (l)
		os << l->car << " : " << l->cdr;
	else
		os << "[]";
	return os;
}

int main ()
{
	std::cout << from_list <take <integer <20>, map <factorial, alln>>>::value () << std::endl;
}
