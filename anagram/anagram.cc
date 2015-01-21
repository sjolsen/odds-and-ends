#include "anagram.hh"
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <iterator>

struct line
	: std::string
{
};

std::istream& operator >> (std::istream& is, line& l)
{
	return std::getline (is, l);
}

int main (int argc, const char* const* argv)
{
	if (argc != 3) {
		const char* prog = argv [0] ? argv [0] : "anagram";
		std::cerr << "Usage: " << prog << " key dictfile\n";
		return EXIT_FAILURE;
	}

	std::string   key {argv [1]};
	std::ifstream fin {argv [2]};

	anagrams (std::istream_iterator <line> {fin}, {},
	          std::ostream_iterator <line> {std::cout, "\n"},
	          key);

	std::cout.flush ();
	return EXIT_SUCCESS;
}
