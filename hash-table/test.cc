#include "ordered_bucket.hh"
#include "unordered_bucket.hh"
#include "hash_table.hh"
#include <cassert>
#include <chrono>
#include <iostream>

void test_unordered (int limit)
{
	hash_table <int, int, std::hash <int>, unordered_bucket <int, int>, std::ratio <20, 1> > t;
	for (int i = 0; i < limit; ++i)
		t.insert (t.search (i).where, i, i);
}

void test_ordered (int limit)
{
	hash_table <int, int, std::hash <int>, ordered_bucket <int, int>, std::ratio <20, 1> > t;
	for (int i = 0; i < limit; ++i)
		t.insert (t.search (i).where, i, i);
}

template <typename Thunk>
std::chrono::milliseconds time (Thunk thunk)
{
	auto start = std::chrono::steady_clock::now ();
	thunk ();
	auto stop = std::chrono::steady_clock::now ();
	return std::chrono::duration_cast <std::chrono::milliseconds> (stop - start);
}

int main ()
{
	for (int i = 0; i <= 10000000; i += 100000)
		std::cout << i << "," << time ([i] {test_unordered (i);}).count () << std::endl;
	for (int i = 0; i <= 10000000; i += 100000)
		std::cout << i << "," << time ([i] {test_ordered (i);}).count () << std::endl;
}
