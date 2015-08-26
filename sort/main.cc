#include <vector>
#include <iostream>
#include "quicksort.hh"
#include "mergesort.hh"
#include "../cl-format/format.hh"
#include "lift.hh"

template <typename T>
void print (const std::vector <T>& v)
{
	tprintf ("[~{~A~^, ~}]~%", v);
}

template <typename T>
void print (const list <T>& l)
{
	std::vector <T> v;
	for (auto* n = l.get (); n != nullptr; n = n->next.get ())
		v.push_back (n->datum);
	print (v);
}

template <typename Sorter>
void test (Sorter sort)
{
	std::vector <int> v = {8, 6, 7, 5, 3, 0, 9, 1, 1};
	print (v);
	sort (v.begin (), v.end ());
	print (v);
	sort (v.begin (), v.end (), std::greater <> {});
	print (v);
}

int main ()
{
	tprintf ("Quicksort~%");
	test (LIFT (quicksort));
	auto l = new_list ({8, 6, 7, 5, 3, 0, 9, 1, 1});
	print (l);
	mergesort (l);
	print (l);
}
