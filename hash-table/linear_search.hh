#ifndef LINEAR_SEARCH_HH
#define LINEAR_SEARCH_HH

#include <functional>
#include <iterator>

template <typename RIter>
struct linear_search_result
{
	bool found;
	RIter where;
};

template <typename RIter, typename T, typename By>
linear_search_result <RIter>
linear_search (RIter begin, RIter end, T&& value, By by)
{
	while (begin != end) {
		if (by (*begin) == value)
			return {true, begin};
		++begin;
	}
	return {false, begin};
}

#endif
