#include "lex.hh"
#include <algorithm>
#include <tuple>

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
					return {arg_t::vee_tag};
				}

				arg_t make_hash_arg () {
					return {arg_t::hash_tag};
				}

				arg_t make_unspecified_arg () {
					return {arg_t::unspecified_tag};
				}

				control_component_t make_text_cc (string_t s)
				{
					control_component_t result;
					result.type = control_component_t::simple_text_tag;
					result.simple_text = s;
					return result;
				}

				control_component_t make_directive_cc (directive_t d)
				{
					control_component_t result;
					result.type = control_component_t::directive_tag;
					result.directive = d;
					return result;
				}

				control_component_t make_funcall_cc (funcall_directive_t f)
				{
					control_component_t result;
					result.type = control_component_t::funcall_directive_tag;
					result.funcall_directive = f;
					return result;
				}


				std::tuple <arglist_t*, const char*>
				get_args (const char* begin, const char* end, new_arglist_t new_arglist)
				{
					throw uninformative_exception {}; // TODO
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
						return std::make_tuple (make_funcall_cc (directive), point + 1);
					}
					else {
						if (begin == end)
							throw uninformative_exception {};
						auto specifier = *begin;
						throw uninformative_exception {}; // TODO: Check specifier
						auto directive = directive_t {args, colon, at, specifier};
						return std::make_tuple (make_directive_cc (directive), begin + 1);
					}
				}

				std::tuple <control_component_t, const char*>
				get_simple_text (const char* begin, const char* end)
				{
					auto point = std::find (begin + 1, end, '~');
					return std::make_tuple (make_text_cc ({begin, point}), point);
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
					if (begin [0] == '~')
						throw uninformative_exception {}; // TODO
					else
						throw uninformative_exception {}; // TODO
				}

			}

			format_control_t*
			lexer (const char* begin,
			       const char* end,
			       new_arglist_t new_arglist,
			       new_control_t new_control)
			{
				auto rev = _lexer (begin, end, new_arglist, new_control, nullptr);
				// Check begin == end
				return fr_reverse (std::get <0> (rev));
			}

		}
	}
}
