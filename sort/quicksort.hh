#ifndef QUICKSORT_HH
#define QUICKSORT_HH

#include <algorithm>

template <typename RIter, typename Compare>
const auto& select_pivot (RIter left, RIter right, Compare cmp)
/* Requires: left != right */
{
	const auto& a = left [0];
	const auto& b = left [std::distance (left, right) / 2];
	const auto& c = left [std::distance (left, right) - 1];

	if (cmp (a, c)) {
		if (cmp (b, a)) return a;
		if (cmp (c, b)) return c;
		return b;
	}
	else {
		if (cmp (b, c)) return c;
		if (cmp (a, b)) return a;
		return b;
	}
}

template <typename RIter, typename Compare = std::less <> >
void quicksort (RIter left, RIter right, Compare cmp = {})
{
	if (left == right)
		return;

	const auto pivot = select_pivot (left, right, cmp);
	auto midl = std::partition (left, right, [&] (const auto& elt) { return  cmp (elt, pivot); });
	auto midr = std::partition (midl, right, [&] (const auto& elt) { return !cmp (pivot, elt); });

	quicksort (left, midl, cmp);
	quicksort (midr, right, cmp);
}

#endif
