#ifndef CL_FORMAT_PARSE_LEX_HH
#define CL_FORMAT_PARSE_LEX_HH

#include <functional>

namespace cl_format {
	namespace parse {
		namespace lex {

			struct string_t {
				const char* begin;
				const char* end;
			};

			struct arg_t {
				enum type_t {
					decimal_tag,
					character_tag,
					vee_tag,
					hash_tag,
					unspecified_tag
				} type;
				union {
					int  decimal;
					char character;
				};
			};

			struct arglist_t {
				arg_t      first;
				arglist_t* rest;

				arglist_t (arg_t first, arglist_t* rest)
					: first (first),
					  rest  (rest)
				{
				}
			};

			struct directive_t {
				arglist_t* args;
				bool colon;
				bool at;
				char specifier;
			};

			struct funcall_directive_t {
				arglist_t* args;
				bool colon;
				bool at;
				string_t specifier;
			};

			struct control_component_t {
				enum type_t {
					simple_text_tag,
					directive_tag,
					funcall_directive_tag
				} type;
				union {
					string_t            simple_text;
					directive_t         directive;
					funcall_directive_t funcall_directive;
				};

				control_component_t ()
				{
				}

				control_component_t (string_t s)
					: type (simple_text_tag),
					  simple_text (s)
				{
				}

				control_component_t (directive_t d)
					: type (directive_tag),
					  directive (d)
				{
				}

				control_component_t (funcall_directive_t f)
					: type (funcall_directive_tag),
					  funcall_directive (f)
				{
				}
			};

			struct format_control_t {
				control_component_t first;
				format_control_t*   rest;

				format_control_t (control_component_t first, format_control_t* rest)
					: first (first),
					  rest  (rest)
				{
				}
			};


			using new_arglist_t = std::function <arglist_t* (arg_t, arglist_t*)>;
			using new_control_t = std::function <format_control_t* (control_component_t, format_control_t*)>;

			format_control_t* lexer (const char* begin, const char* end, new_arglist_t, new_control_t);

			struct uninformative_exception {};

		}
	}
}

#endif
