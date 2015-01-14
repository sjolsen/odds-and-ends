#ifndef ANAGRAM_HH
#define ANAGRAM_HH

#include <algorithm>
#include <functional>

template <typename IIter, typename OIter, typename T, typename Comp = std::less <void>>
void anagrams (IIter first, IIter last,
               OIter output,
               T&& key,
               Comp cmp = Comp {})
{
	using std::begin;
	using std::end;

	const auto norm = [&] (auto&& key) {
		auto skey = key;
		std::sort (begin (skey), end (skey), cmp);
		return skey;
	};

	const auto skey = norm (key);
	for (auto iter = first; iter != last; ++iter) {
		auto selmt = norm (*iter);
		if (!cmp (skey, selmt) && !cmp (selmt, skey)) { // skey == selmt
			*output = *iter;
			++output;
		}
	}
}

#endif
