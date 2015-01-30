#include <utility>
#include <functional>

//// Recursive definition
// template <typename RIter, typename T, typename Comp = std::less <T> >
// std::pair <RIter, bool>
// binary_search (RIter begin, RIter end, const T& value, Comp&& comp = Comp {})
// {
// 	if (begin == end)
// 		return {end, false};
// 	auto mid = begin + (std::distance (begin, end) / 2);
// 	if (comp (value, *mid))
// 		return binary_search (begin, mid, value, comp);
// 	if (comp (*mid, value))
// 		return binary_search (mid + 1, end, value, comp);
// 	return {mid, true};
// }

template <typename RIter, typename T, typename Comp = std::less <T> >
std::pair <RIter, bool>
stackless_binary_search (RIter begin, RIter end, const T& value, Comp&& comp = Comp {})
{
	RIter mid;
	while (begin != end)
	{
		mid = begin + (std::distance (begin, end) / 2);
		if (comp (value, *mid)) {
			end = mid;
			continue;
		}
		if (comp (*mid, value)) {
			begin = mid + 1;
			continue;
		}
		return {mid, true};
	}
	return {end, false};
}


#include <cstdlib>
#include <type_traits>
#include "../dynamic-bind/dynamic_bind.hh"

template <typename Comp>
dynamic_variable <Comp*> comparator_object (nullptr);

template <typename Comp, typename T>
int comparator (const void* a, const void* b)
{
	const T& _a = *static_cast <const T*> (a);
	const T& _b = *static_cast <const T*> (b);
	auto&& comp = *comparator_object <Comp>.get ();

	if (comp (_a, _b))
		return -1;
	if (comp (_b, _a))
		return 1;
	return 0;
}

template <typename T, typename Comp = std::less <T> >
const T* reference_binary_search (const T* begin, const T* end, const T& value, Comp&& comp = Comp {})
{
	using _Comp = std::remove_cv_t <std::remove_reference_t <Comp> >;
	DYNAMIC_BIND (comparator_object <_Comp>, &comp);
	auto erased_comp = &comparator <_Comp, T>;
	auto result = std::bsearch (&value, begin, end - begin, sizeof (T), erased_comp);
	return static_cast <const T*> (result);
}

template <typename T, typename Comp1 = std::less <T>, typename Comp2 = std::less <T> >
bool pass_basic (const T* begin, const T* end, const T& value, Comp1&& pcomp = Comp1 {}, Comp2&& qcomp = Comp2 {})
{
	auto std_result = reference_binary_search (begin, end, value, qcomp);
	auto my_result  = stackless_binary_search (begin, end, value, pcomp);

	if (std_result == nullptr)
		return my_result.second == false;
	else
		return my_result.second == true && my_result.first == std_result;
}


#include <iostream>
#include <iomanip>
#include <algorithm>

template <typename IIter>
std::ostream& print_sequence (std::ostream& os, IIter begin, IIter end)
{
	os << "{";
	if (begin != end) {
		os << *begin;
		while (++begin != end)
			os << ", " << *begin;
	}
	return os << "}";
}

template <typename First, typename Second>
std::ostream& print_pair (std::ostream& os, const std::pair <First, Second>& p)
{
	return os << "(" << p.first << ", " << p.second << ")";
}

template <typename Comp>
struct counting_comparator
{
	Comp comp;
	int count = 0;

	template <typename... Args>
	decltype (auto) operator () (Args&&... args)
	{
		++count;
		return comp (std::forward <Args> (args)...);
	}
};

template <typename Comp>
auto make_counting_comparator (Comp comp)
{
	return counting_comparator <Comp> {std::move (comp)};
}

int main ()
{
	auto comp = std::less <> {};

	std::string data [] = {
		"The", "quick", "brown", "fox", "jumps",
		"over", "the", "lazy", "dog"
	};

	std::string tests [] = {
		"The", "fox", "is", "lazy", "and",
		"the", "dog", "is", "crazy"
	};

	auto pcomp = make_counting_comparator (comp);
	auto qcomp = make_counting_comparator (comp);

	std::sort (std::begin (data), std::end (data), comp);
	for (auto a = std::begin (data); a != std::end (data); ++a)
		for (auto b = a; b != std::end (data); ++b)
			for (auto&& s : tests)
				if (!pass_basic (&*a, &*b, s, pcomp, qcomp))
				{
					std::cerr << "Failed on seq = ";
					print_sequence (std::cerr, a, b);
					std::cerr << ", value = " << s;
					std::cerr << std::endl;

					auto p = stackless_binary_search (a, b, s, comp);
					auto q = reference_binary_search (&*a, &*b, s, comp);

					std::cerr << "  Got " << std::boolalpha;
					print_pair (std::cerr, p);
					std::cerr << ", " << q;
					std::cerr << std::endl;
				}

	std::cout << "stackless_binary_search: " << pcomp.count << " comparisons" << std::endl;
	std::cout << "reference_binary_search: " << qcomp.count << " comparisons" << std::endl;
}
