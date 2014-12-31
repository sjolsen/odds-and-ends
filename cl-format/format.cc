#include <iostream>
#include <type_traits>
#include <utility>
#include "../dynamic-bind/dynamic_bind.hh"

extern dynamic_variable <std::ostream&> _standard_output_;
dynamic_variable <std::ostream&> _standard_output_ (std::cout);


/// Parser state definitions

enum class arg_type
{
	t_error,
	t_auto,
	t_lit,
	t_loop_in,
	t_loop_out,
	t_escape_last,
	t_char,
	t_end
};

struct auto_spec_t {};

template <std::size_t begin, std::size_t end>
struct lit_spec_t {};

template <typename Str, std::size_t begin, std::size_t end, std::size_t level, bool last>
struct loop_spec_t {};

template <char c>
struct char_spec_t {};

template <std::size_t Next, arg_type Type, typename Spec>
struct partial_parse
{
	static constexpr const std::size_t next = Next;
	static constexpr const arg_type type = Type;
	using spec = Spec;
};

template <typename pp>
using ppnext = typename pp::next;

template <typename pp>
using ppspec = typename pp::spec;


/// Format string parsing

template <typename Str>
static inline constexpr
std::size_t litend (Str str, std::size_t begin, std::size_t end)
{
	return (begin == end) ? end : ((str [begin] == '~') ? begin : litend (str, begin + 1, end));
}

template <typename Str, std::size_t begin, std::size_t end>
struct parse_lit_impl;
template <typename Str, std::size_t begin, std::size_t end>
using  parse_lit = typename parse_lit_impl <Str, begin, end>::pparse;

template <typename Str, std::size_t begin, std::size_t end>
struct parse_lit_impl
{
	static constexpr const auto split = litend (Str {}, begin + 1, end);
	using pparse = partial_parse <split, arg_type::t_lit, lit_spec_t <begin, split>>;
};



template <typename Str, std::size_t begin, std::size_t end>
struct parse_flag_impl;
template <typename Str, std::size_t begin, std::size_t end>
using  parse_flag = typename parse_flag_impl <Str, begin, end>::pparse;

template <typename Str, std::size_t end>
struct parse_flag_impl <Str, end, end>
{
	using pparse = partial_parse <end, arg_type::t_error, void>;
};

template <typename Str, std::size_t begin, std::size_t end>
struct parse_flag_impl
{
	using pparse = typename std::conditional <Str {} [begin] == 'a',
	                                          partial_parse <begin + 1, arg_type::t_auto, auto_spec_t>,
	               typename std::conditional <Str {} [begin] == '{',
	                                          partial_parse <begin + 1, arg_type::t_loop_in, void>,
	               typename std::conditional <Str {} [begin] == '}',
	                                          partial_parse <begin + 1, arg_type::t_loop_out, void>,
	               typename std::conditional <Str {} [begin] == '^',
	                                          partial_parse <begin + 1, arg_type::t_escape_last, void>,
	               typename std::conditional <Str {} [begin] == '%',
	                                          partial_parse <begin + 1, arg_type::t_char, char_spec_t <'\n'>>,
	               typename std::conditional <Str {} [begin] == '~',
	                                          parse_lit <Str, begin, end>,
	                                          partial_parse <begin, arg_type::t_error, void>>::type>::type>::type>::type>::type>::type;
};



template <typename Str, std::size_t begin, std::size_t end>
struct parse_impl;
template <typename Str, std::size_t begin, std::size_t end>
using  parse = typename parse_impl <Str, begin, end>::pparse;

template <typename Str, std::size_t end>
struct parse_impl <Str, end, end>
{
	using pparse = partial_parse <end, arg_type::t_end, void>;
};

template <typename Str, std::size_t begin, std::size_t end>
struct parse_impl
{
	using pparse = typename std::conditional <Str {} [begin] == '~',
	                                          parse_flag <Str, begin + 1, end>,
	                                          parse_lit <Str, begin, end>>::type;
};


/// Format logic

template <typename Arg>
static inline
void format_impl (Arg&& arg, auto_spec_t)
{
	_standard_output_.get () << std::forward <Arg> (arg);
}

template <char c>
static inline
void format_impl (char_spec_t <c>)
{
	_standard_output_.get () << c;
}

template <typename Str, std::size_t begin, std::size_t end>
static inline
void format_impl (Str string, lit_spec_t <begin, end>)
{
	_standard_output_.get ().write (string.begin + begin, end - begin);
}

// Clang freaks out if we put Rest second
template <typename Arg, typename Str, std::size_t begin, std::size_t end, std::size_t level, bool last, typename... Rest>
void format_impl (Arg&& arg, Rest&&... rest, loop_spec_t <Str, begin, end, level, last>);

template <typename Str, std::size_t begin, std::size_t end, std::size_t level, bool last>
struct formatter
{
	using spec = parse <Str, begin, end>;
	static_assert (spec::type != arg_type::t_error, "Failed to parse format string");
	static_assert (!(spec::type == arg_type::t_loop_out && level == 0), "Tried to exit a loop where there is none");
	static_assert (!(spec::type == arg_type::t_end && level != 0), "Format string ended inside loop");


	template <typename X>
	static constexpr typename std::enable_if <(sizeof (X), spec::type == arg_type::t_loop_out), std::size_t>::type
	loop_end () { return spec::next; }

	template <typename X>
	static constexpr typename std::enable_if <(sizeof (X), spec::type == arg_type::t_end), std::size_t>::type
	loop_end () { return end; }

	template <typename X>
	static constexpr typename std::enable_if <(sizeof (X), spec::type == arg_type::t_loop_in), std::size_t>::type
	loop_end () { return formatter <Str, formatter <Str, spec::next, end, level + 1, false>::template loop_end <char> (), end, level, last>::template loop_end <char> (); }

	template <typename X>
	static constexpr typename std::enable_if <(sizeof (X), !(spec::type == arg_type::t_loop_out || spec::type == arg_type::t_end || spec::type == arg_type::t_loop_in)), std::size_t>::type
	loop_end () { return formatter <Str, spec::next, end, level, last>::template loop_end <char> (); }


	template <typename X, typename First, typename... Rest>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_auto)>::type
	format (First&& first, Rest&&... rest)
	{
		format_impl (std::forward <First> (first), ppspec <spec> {});
		formatter <Str, spec::next, end, level, last>::template format <char> (std::forward <Rest> (rest)...);
	}

	template <typename X, typename... Rest>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_lit)>::type
	format (Rest&&... rest)
	{
		format_impl (Str {}, ppspec <spec> {});
		formatter <Str, spec::next, end, level, last>::template format <char> (std::forward <Rest> (rest)...);
	}

	template <typename X, typename... Rest>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_char)>::type
	format (Rest&&... rest)
	{
		format_impl (ppspec <spec> {});
		formatter <Str, spec::next, end, level, last>::template format <char> (std::forward <Rest> (rest)...);
	}

	template <typename X, typename First, typename... Rest>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_loop_in)>::type
	format (First&& first, Rest&&... rest)
	{
		format_impl <First, Str, spec::next, end, level + 1, last, Rest...> (std::forward <First> (first), std::forward <Rest> (rest)..., {});
	}

	template <typename X, typename... Rest>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_loop_out)>::type
	format (Rest&&... rest)
	{
	}

	template <typename X, typename... Rest>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_escape_last)>::type
	format (Rest&&... rest)
	{
		if (!last)
			formatter <Str, spec::next, end, level, last>::template format <char> (std::forward <Rest> (rest)...);
	}

	template <typename X>
	static typename std::enable_if <(sizeof (X), spec::type == arg_type::t_end)>::type
	format ()
	{
	}
};

template <typename Arg, typename Str, std::size_t begin, std::size_t end, std::size_t level, bool last, typename... Rest>
void format_impl (Arg&& arg, Rest&&... rest, loop_spec_t <Str, begin, end, level, last>)
{
	using inner_fmt = formatter <Str, begin, end, level, false>;
	using inner_fmt_l = formatter <Str, begin, end, level, true>;
	using outer_fmt = formatter <Str, inner_fmt::template loop_end <char> (), end, level - 1, last>;

	using std::begin;
	using std::end;
	auto&& range = std::forward <Arg> (arg);
	auto b = begin (range);
	auto e = end (range);
	while (b != e && std::next (b) != e) {
		inner_fmt::template format <char> (*b);
		++b;
	}
	if (b != e)
		inner_fmt_l::template format <char> (*b);

	outer_fmt::template format <char> (std::forward <Rest> (rest)...);
}



template <std::size_t N>
static inline constexpr
std::size_t tstrlen (const char (&) [N])
{
	return N;
}

#define tprintf(fmt, ...) ([&] { \
	struct string_t { \
		const char* const begin = fmt; \
		const char* const end   = fmt + tstrlen (fmt) - 1; \
		constexpr \
		char operator [] (std::size_t i) const \
		{ return begin [i]; } \
	}; \
	formatter <string_t, 0, tstrlen (fmt) - 1, 0, false>::template format <char> (__VA_ARGS__); \
} ())



#include <vector>
#include <fstream>

void do_a_thing ()
{
	std::vector <std::vector <int>> v = {{1},
	                                     {4, 5},
	                                     {7, 8, 9}};
	tprintf ("Stuff: [~{[~{~a~^, ~}]~^,~%"
	         "        ~}]~%", v);
}

int main ()
{
	tprintf ("Hello, stdout!~%");
	do_a_thing ();
	{
		std::ofstream fout ("foo.txt");
		DYNAMIC_BIND (_standard_output_, fout);
		do_a_thing ();
	}
	tprintf ("Hello again.~%");
}
