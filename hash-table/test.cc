#include "ordered_bucket.hh"
#include "unordered_bucket.hh"
#include "hash_table.hh"
#include <cassert>
#include <vector>
#include "../cl-format/format.hh"

template <typename K, typename V>
struct kv_ref
{
	const K& k;
	const V& v;
};

template <typename K, typename V>
std::ostream& operator << (std::ostream& os, kv_ref <K, V> pair)
{
	return os << pair.k << " => " << pair.v;
}

template <template <typename, typename, typename...> class Bucket, typename Key, typename Value>
std::vector <kv_ref <Key, Value> >
to_vector (const Bucket <Key, Value>& b)
{
	std::vector <kv_ref <Key, Value> > v;
	b.for_each ([&v] (const Key& key, const Value& value) {
		v.push_back (kv_ref <Key, Value> {key, value});
	});
	return v;
}

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

	tprintf ("[~{~A~^, ~}]~%", to_vector (b));
}

void test2 (int limit)
{
	hash_table <int, int> t;
	for (int i = 0; i < limit; ++i)
		t.insert (t.search (i).where, i, i / 2);
	tprintf ("[~{~A~^, ~}]~%", to_vector (t));
	for (int i = 0; i < limit; ++i)
		assert (t.access (t.search (i).where) == i / 2);
}

int main ()
{
	test <ordered_bucket> ();
	test <unordered_bucket> ();
	test <hash_table> ();
	test2 (100);
}
