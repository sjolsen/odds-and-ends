#ifndef BINARY_SEARCH_HH
#define BINARY_SEARCH_HH

#include <functional>
#include <iterator>

template <typename RIter>
struct binary_search_result
{
	bool found;
	RIter where;
};

template <typename RIter, typename T, typename Cmp, typename By>
binary_search_result <RIter>
binary_search (RIter begin, RIter end, T&& value, Cmp cmp, By by)
{
	while (begin != end) {
		auto mid = begin + (std::distance (begin, end) / 2);
		if (cmp (value, by (*mid))) {
			end = mid;
			continue;
		}
		if (cmp (by (*mid), value)) {
			begin = std::next (mid);
			continue;
		}
		return {true, mid};
	}
	return {false, begin};
}

#endif
