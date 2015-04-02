#include "lex.hh"
#include <algorithm>
#include <tuple>
#include <cctype>
#include <cerrno>
#include <cstdlib>
#include <climits>

namespace
{
	template <typename FRList>
	FRList* fr_reverse (FRList* head)
	{
		FRList* cursor = head;
		FRList* prev = nullptr;
		while (cursor != nullptr) {
			auto next = cursor->rest;
			cursor->rest = prev;
			prev = cursor;
			cursor = next;
		}
		return prev;
	}

	bool valid_ascii_specifiers [128] = {
		/*            0    1    2    3    4    5    6    7       8    9    A    B    C    D    E    F
		   0x00       0,   0,   0,   0,   0,   0,   0,   0,      0,   0, '\n',  0,   0,   0,   0,   0,
		   0x10       0,   0,   0,   0,   0,   0,   0,   0,      0,   0,   0,   0,   0,   0,   0,   0,
		   0x20       0,   0,   0,   0, '$', '%', '&',   0,    '(', ')', '*',   0,   0,   0,   0, '/',
		   0x30       0,   0,   0,   0,   0,   0,   0,   0,      0,   0,   0, ';', '<',   0, '>', '?',
		   0x40       0, 'A', 'B', 'C', 'D', 'E', 'F', 'G',      0, 'I',   0,   0,   0,   0,   0, 'O',
		   0x50     'P',   0, 'R', 'S', 'T',   0,   0, 'W',    'X',   0,   0, '[',   0, ']', '^', '_',
		   0x60       0, 'a', 'b', 'c', 'd', 'e', 'f', 'g',      0, 'i',   0,   0,   0,   0,   0, 'o',
		   0x70     'p',   0, 'r', 's', 't',   0,   0, 'w',    'x',   0,   0, '{', '|', '}', '~',   0  */

		/*            0    1    2    3    4    5    6    7       8    9    A    B    C    D    E    F */
		/* 0x00 */    0,   0,   0,   0,   0,   0,   0,   0,      0,   0,   1,   0,   0,   0,   0,   0,
		/* 0x10 */    0,   0,   0,   0,   0,   0,   0,   0,      0,   0,   0,   0,   0,   0,   0,   0,
		/* 0x20 */    0,   0,   0,   0,   1,   1,   1,   0,      1,   1,   1,   0,   0,   0,   0,   1,
		/* 0x30 */    0,   0,   0,   0,   0,   0,   0,   0,      0,   0,   0,   1,   1,   0,   1,   1,
		/* 0x40 */    0,   1,   1,   1,   1,   1,   1,   1,      0,   1,   0,   0,   0,   0,   0,   1,
		/* 0x50 */    1,   0,   1,   1,   1,   0,   0,   1,      1,   0,   0,   1,   0,   1,   1,   1,
		/* 0x60 */    0,   1,   1,   1,   1,   1,   1,   1,      0,   1,   0,   0,   0,   0,   0,   1,
		/* 0x70 */    1,   0,   1,   1,   1,   0,   0,   1,      1,   0,   0,   1,   1,   1,   1,   0
	};

	bool valid_specifier (char c)
	{
		return valid_ascii_specifiers [static_cast <std::size_t> (c)];
	}
}

namespace cl_format {
	namespace parse {
		namespace lex {

			namespace
			{
				arg_t make_decimal_arg (int d)
				{
					arg_t result;
					result.type = arg_t::decimal_tag;
					result.decimal = d;
					return result;
				}

				arg_t make_char_arg (char c)
				{
					arg_t result;
					result.type = arg_t::character_tag;
					result.character = c;
					return result;
				}

				arg_t make_vee_arg () {
					return {arg_t::vee_tag, {}};
				}

				arg_t make_hash_arg () {
					return {arg_t::hash_tag, {}};
				}

				arg_t make_unspecified_arg () {
					return {arg_t::unspecified_tag, {}};
				}


				std::tuple <int, const char*>
				get_decimal (const char* begin, const char* end)
				{
					if (begin == end)
						throw uninformative_exception {};

					errno = 0;
					char* point = nullptr;
					long result = std::strtol (begin, &point, 10);
					if (errno != 0 || begin == point)
						throw uninformative_exception {};
					if (result < INT_MIN || INT_MAX < result)
						throw uninformative_exception {};

					return std::make_tuple (static_cast <int> (result), point);
				}

				std::tuple <arglist_t*, const char*>
				_get_args (const char* begin, const char* end, new_arglist_t new_arglist, arglist_t* acc)
				{
					if (begin == end)
						return std::make_tuple (acc, begin);

					switch (*begin) {
						case ',':
							return _get_args (begin + 1, end, new_arglist, new_arglist (make_unspecified_arg (), acc));
						case 'V':
						case 'v': {
							acc = new_arglist (make_vee_arg (), acc);
							if (begin + 1 == end || begin [1] != ',')
								return std::make_tuple (acc, begin + 1);
							else
								return _get_args (begin + 2, end, new_arglist, acc);
						}
						case '#': {
							acc = new_arglist (make_hash_arg (), acc);
							if (begin + 1 == end || begin [1] != ',')
								return std::make_tuple (acc, begin + 1);
							else
								return _get_args (begin + 2, end, new_arglist, acc);
						}
						case '\'': {
							if (begin + 1 == end)
								throw uninformative_exception {};
							acc = new_arglist (make_char_arg (begin [1]), acc);
							if (begin + 2 == end || begin [2] != ',')
								return std::make_tuple (acc, begin + 2);
							else
								return _get_args (begin + 3, end, new_arglist, acc);
						}
						case '-':
						case '+':
						default: {
							if (std::isdigit (*begin)) {
								int d;
								std::tie (d, begin) = get_decimal (begin, end);
								acc = new_arglist (make_decimal_arg (d), acc);
								if (begin == end || begin [0] != ',')
									return std::make_tuple (acc, begin);
								else
									return _get_args (begin + 1, end, new_arglist, acc);
							}
							else
								return std::make_tuple (acc, begin);
						}
					}
				}

				std::tuple <arglist_t*, const char*>
				get_args (const char* begin, const char* end, new_arglist_t new_arglist)
				{
					arglist_t* args = nullptr;
					std::tie (args, begin) = _get_args (begin, end, new_arglist, nullptr);
					return std::make_tuple (fr_reverse (args), begin);
				}

				std::tuple <bool, bool, const char*>
				get_colon_at (const char* begin, const char* end)
				{
					bool colon = false;
					bool at = false;

					while (begin != end && (*begin == ':' || *begin == '@')) {
						if (*begin == ':') {
							if (colon)
								throw uninformative_exception {};
							else
								colon = true;
						}
						if (*begin == '@') {
							if (at)
								throw uninformative_exception {};
							else
								at = true;
						}
						++begin;
					}

					return std::make_tuple (colon, at, begin);
				}

				std::tuple <control_component_t, const char*>
				get_directive (const char* begin, const char* end, new_arglist_t new_arglist)
				{
					arglist_t* args = nullptr;
					std::tie (args, begin) = get_args (begin, end, new_arglist);

					bool colon = false;
					bool at = false;
					std::tie (colon, at, begin) = get_colon_at (begin, end);

					if (begin == end)
						throw uninformative_exception {};
					if (*begin == '/') {
						auto point = std::find (begin + 1, end, '/');
						if (point == end)
							throw uninformative_exception {};
						auto specifier = string_t {begin + 1, point};
						auto directive = funcall_directive_t {args, colon, at, specifier};
						return std::make_tuple (control_component_t {directive}, point + 1);
					}
					else {
						if (begin == end)
							throw uninformative_exception {};
						auto specifier = *begin;
						if (!valid_specifier (specifier))
							throw uninformative_exception {};
						auto directive = directive_t {args, colon, at, specifier};
						return std::make_tuple (control_component_t {directive}, begin + 1);
					}
				}

				std::tuple <control_component_t, const char*>
				get_simple_text (const char* begin, const char* end)
				{
					auto point = std::find (begin + 1, end, '~');
					auto str = string_t {begin, point};
					return std::make_tuple (control_component_t {str}, point);
				}

				std::tuple <format_control_t*, const char*>
				_lexer (const char* begin,
				        const char* end,
				        new_arglist_t new_arglist,
				        new_control_t new_control,
				        format_control_t* acc)
				{
					if (begin == end)
						return std::make_tuple (acc, begin);
					if (*begin == '~') {
						control_component_t control;
						std::tie (control, begin) = get_directive (begin + 1, end, new_arglist);
						return _lexer (begin, end, new_arglist, new_control, new_control (control, acc));
					}
					else {
						control_component_t control;
						std::tie (control, begin) = get_simple_text (begin, end);
						return _lexer (begin, end, new_arglist, new_control, new_control (control, acc));
					}
				}

			}

			format_control_t*
			lexer (const char* begin,
			       const char* end,
			       new_arglist_t new_arglist,
			       new_control_t new_control)
			{
				format_control_t* result = nullptr;
				std::tie (result, begin) = _lexer (begin, end, new_arglist, new_control, nullptr);
				if (begin != end)
					throw uninformative_exception {};
				return fr_reverse (result);
			}

		}
	}
}
