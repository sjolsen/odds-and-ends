#include "mpz.hh"
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
	std::cout << from_integer <five>::value ()        << std::endl;
	std::cout << from_integer <twenty_five>::value () << std::endl;
	std::cout << from_integer <biggest>::value ()     << std::endl;
	std::cout << from_integer <biggest2>::value ()    << std::endl;
	std::cout << from_integer <bigbig>::value ()      << std::endl;
	std::cout << from_integer <bbbbig>::value ()      << std::endl;
}
