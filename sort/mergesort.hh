#ifndef MERGESORT_HH
#define MERGESORT_HH

#include <memory>
#include <initializer_list>
#include <iterator>

template <typename T>
struct node;

template <typename T>
using list = std::unique_ptr <node <T>>;

template <typename T>
struct node
{
	T datum;
	list <T> next;

	node (T datum, list <T> next)
		: datum (std::move (datum)),
		  next (std::move (next))
	{
	}
	node (const node&) = delete;
	node (node&&) = default;
};

template <typename T>
list <T> new_list (std::initializer_list <T> il)
{
	list <T> l = nullptr;

	auto rbegin = std::reverse_iterator <typename decltype (il)::iterator> {il.end ()};
	auto rend   = std::reverse_iterator <typename decltype (il)::iterator> {il.begin ()};
	for (auto i = rbegin; i != rend; ++i)
		l = std::make_unique <node <T>> (*i, std::move (l));

	return l;
}



template <typename T>
std::tuple <list <T>, list <T>>
split (list <T>& l)
{
	list <T> l1 = nullptr;
	list <T> l2 = nullptr;
	list <T>* c1 = &l1;
	list <T>* c2 = &l2;

	bool which = false;
	for (auto* p = &l; *p != nullptr;) {
		list <T>*& c = (which ? c1 : c2);
		*c = std::move (*p);
		p = c = &(*c)->next;
		which = !which;
	}

	return std::make_tuple (std::move (l1), std::move (l2));
}

template <typename T>
list <T> merge (list <T>& l1, list <T>& l2)
{
	if (l1 == nullptr)
		return std::move (l2);
	if (l2 == nullptr)
		return std::move (l1);

	list <T> l = nullptr;
	list <T>* c = &l;

	while (true) {
		if (l1 == nullptr) {
			*c = std::move (l2);
			return l;
		}
		if (l2 == nullptr) {
			*c = std::move (l1);
			return l;
		}

		if (l2->datum < l1->datum) {
			*c = std::move (l2);
			l2 = std::move ((*c)->next);
		}
		else {
			*c = std::move (l1);
			l1 = std::move ((*c)->next);
		}

		c = &(*c)->next;
	}
}

template <typename T>
void mergesort (list <T>& l)
{
	if (l == nullptr || l->next == nullptr)
		return;

	list <T> l1, l2; std::tie (l1, l2) = split (l);
	mergesort (l1);
	mergesort (l2);
	l = merge (l1, l2);
}

#endif
