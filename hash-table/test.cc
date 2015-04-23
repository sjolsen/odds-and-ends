#include "ordered_bucket.hh"
#include "unordered_bucket.hh"
#include "hash_table.hh"
#include <cassert>

template <template <typename, typename, typename...> class Bucket>
void test ()
{
	Bucket <int, int> b;

	auto r = b.search (0);
	assert (!r.found);
	assert (b.insert (r.where, 0, 0) == 0);
	r = b.search (0);
	assert (r.found);

	for (int i : {8, 6, 5, 3, 9}) {
		r = b.search (i);
		assert (!r.found);
		assert (b.insert (r.where, i, 2 * i) == 2 * i);
		r = b.search (i);
		assert (r.found);
	}

	for (int i : {8, 6, 5, 3, 0, 9}) {
		r = b.search (i);
		assert (r.found);
		assert (b.access (r.where) == 2 * i);
	}
}

int main ()
{
	test <ordered_bucket> ();
	test <unordered_bucket> ();
	test <hash_table> ();
}
