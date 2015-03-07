#include "parse_format.hh"
#include <tuple>
#include <cctype>

namespace parse_format
{
	struct incomplete_directive {};
	struct illegal_directive {};


	control_component_t get_simple_text (const char* begin, const char* end)
	{
		return control_component_t {
			control_component_t::simple_text_t,
			string_t {begin, end}
		};
	}

	std::tuple <control_component_t, const char*>
	parse_directive (const char* begin, const char* end)
	{
		arglist_t args;
		std::tie (args, begin) = parse_args (begin, end);

		bool colon, at;
		std::tie (colon, at, begin) = parse_colon_at (begin, end);

		if (begin == end)
			throw incomplete_directive ();
		switch (std::toupper (*begin))
		{
			case 'C':
			case '%':
			case '&':
			case '|':
			case '~':

			case 'R':
			case 'D':
			case 'B':
			case 'O':
			case 'X':

			case 'F':
			case 'E':
			case 'G':
			case '$':

			case 'A':
			case 'S':
			case 'W':

			case '_':
			case '<':
			case 'I':
			case '/':

			case 'T':
			case '>':

			case '*':
			case '[':
			case ']':
			case '{':
			case '}':
			case '?':

			case '(':
			case ')':
			case 'P':
			case ';':
			case '^':
			case '\n':

			default: throw illegal_directive ();
		}
	}

	format_control_t parse (const char* begin, const char* end)
	{
		std::vector <control_component_t> components;
		while (begin != end)
		{
			auto next = std::find (begin, end, '~');
			if (next == begin) {
				components.emplace_back ();
				std::tie (components.back (), begin) = parse_directive (next + 1, end);
			}
			else {
				result.components.push_back (get_simple_text (begin, next));
				begin = next;
			}
		}
		return format_control_t {std::move (result)};
	}

}
