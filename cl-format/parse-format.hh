#ifndef PARSE_FORMAT_HH
#define PARSE_FORMAT_HH

#include <vector>

namespace parse_format
{
	struct string_t {
		const char* begin;
		const char* end;
	};

	struct control_component_t;

	struct format_control_t {
		std::vector <control_component_t> components;
	};

	struct format_control_list_t {
		std::vector <format_control_t> controls;
	};

	struct numeric_arg_t {
		enum type_t {
			unspecified_t,
			decimal_t,
			vee_t,
			hash_t
		} type;
		int decimal;
	};

	struct character_arg_t {
		enum type_t {
			unspecified_t,
			character_t,
			vee_t,
			hash_t
		} type;
		char character;
	};

	struct generic_arg_t {
		enum type_t {
			unspecified_t,
			decimal_t,
			character_t,
			vee_t,
			hash_t
		} type;
		union {
			int  decimal;
			char character;
		};
	};

	struct arglist_t {
		std::vector <generic_arg_t> args;
	};

	struct character_directive_t {
		bool colon;
		bool at;
	};

	struct newline_directive_t {
		numeric_arg_t n;
	};

	struct fresh_line_directive_t {
		numeric_arg_t n;
	};

	struct page_directive_t {
		numeric_arg_t n;
	};

	struct tilde_directive_t {
		numeric_arg_t n;
	};

	struct radix_directive_t {
		numeric_arg_t   radix;
		numeric_arg_t   mincol;
		character_arg_t padchar;
		character_arg_t commachar;
		numeric_arg_t   comma_interval;
		bool            colon;
		bool            at;
	};

	struct decimal_directive_t {
		numeric_arg_t   mincol;
		character_arg_t padchar;
		character_arg_t commachar;
		numeric_arg_t   comma_interval;
		bool            colon;
		bool            at;
	};

	struct binary_directive_t {
		numeric_arg_t   mincol;
		character_arg_t padchar;
		character_arg_t commachar;
		numeric_arg_t   comma_interval;
		bool            colon;
		bool            at;
	};

	struct octal_directive_t {
		numeric_arg_t   mincol;
		character_arg_t padchar;
		character_arg_t commachar;
		numeric_arg_t   comma_interval;
		bool            colon;
		bool            at;
	};

	struct hexadecimal_directive_t {
		numeric_arg_t   mincol;
		character_arg_t padchar;
		character_arg_t commachar;
		numeric_arg_t   comma_interval;
		bool            colon;
		bool            at;
	};

	struct fixed_format_fp_directive_t {
		numeric_arg_t   w;
		numeric_arg_t   d;
		numeric_arg_t   k;
		character_arg_t overflowchar;
		character_arg_t padchar;
		bool            at;
	};

	struct exponential_fp_directive_t {
		numeric_arg_t   w;
		numeric_arg_t   d;
		numeric_arg_t   e;
		numeric_arg_t   k;
		character_arg_t overflowchar;
		character_arg_t padchar;
		character_arg_t exponentchar;
		bool            at;
	};

	struct general_fp_directive_t {
		numeric_arg_t   w;
		numeric_arg_t   d;
		numeric_arg_t   e;
		numeric_arg_t   k;
		character_arg_t overflowchar;
		character_arg_t padchar;
		character_arg_t exponentchar;
		bool            at;
	};

	struct monetary_fp_directive_t {
		numeric_arg_t   d;
		numeric_arg_t   n;
		numeric_arg_t   w;
		character_arg_t padchar;
		bool            colon;
		bool            at;
	};

	struct aesthetic_directive_t {
		numeric_arg_t   mincol;
		numeric_arg_t   colinc;
		numeric_arg_t   minpad;
		character_arg_t padchar;
		bool            colon;
		bool            at;
	};

	struct standard_directive_t {
		numeric_arg_t   mincol;
		numeric_arg_t   colinc;
		numeric_arg_t   minpad;
		character_arg_t padchar;
		bool            colon;
		bool            at;
	};

	struct write_directive_t {
		bool colon;
		bool at;
	};

	struct conditional_newline_directive_t {
		bool colon;
		bool at;
	};

	struct logical_block_directive_t {
		string_t         prefix;
		format_control_t body;
		string_t         suffix;
		bool             colon;
		bool             at;
		bool             at2;
	};

	struct indent_directive_t {
		numeric_arg_t n;
		bool          colon;
	};

	struct call_function_directive_t {
		arglist_t args;
		string_t  name;
		bool      colon;
		bool      at;
	};

	struct tabulate_directive_t {
		union {
			numeric_arg_t colnum;
			numeric_arg_t colrel;
		};
		numeric_arg_t colinc;
		bool          colon;
		bool          at;
	};

	struct justification_directive_t {
		numeric_arg_t   mincol;
		numeric_arg_t   colinc;
		numeric_arg_t   minpad;
		character_arg_t padchar;
		bool            colon;
		bool            at;

		bool                  special_first_p;
		format_control_t      special_first;
		numeric_arg_t         comma_width;
		numeric_arg_t         line_width;
		format_control_list_t clauses;
	};

	struct go_to_directive_t {
		numeric_arg_t n;
		bool          colon;
		bool          at;
	};

	struct conditional_directive_t {
		numeric_arg_t         n;
		bool                  colon;
		bool                  at;
		format_control_list_t clauses;
		format_control_t      default_clause;
	};

	struct iteration_directive_t {
		bool             colon;
		bool             at;
		bool             colon2;
		format_control_t subclause;
	};

	struct recursive_directive_t {
		bool at;
	};

	struct case_conversion_directive_t {
		bool colon;
		bool at;
		format_control_t subclause;
	};

	struct plural_directive_t {
		bool colon;
		bool at;
	};

	struct escape_upward_directive_t {
		numeric_arg_t n;
		bool          colon;
	};

	struct ignored_newline_directive_t {
		bool colon;
		bool at;
	};

	struct any_directive_t {
		enum type_t {
			character_t,     newline_t,             fresh_line_t,      page_t,
			tilde_t,         radix_t,               decimal_t,         binary_t,
			octal_t,         hexadecimal_t,         fixed_format_fp_t, exponential_fp_t,
			general_fp_t,    monetary_fp_t,         aesthetic_t,       standard_t,
			write_t,         conditional_newline_t, logical_block_t,   indent_t,
			call_function_t, tabulate_t,            justification_t,   go_to_t,
			conditional_t,   iteration_t,           recursive_t,       case_conversion_t,
			plural_t,        escape_upward_t,       ignored_newline_t
		} type;
		union {
			character_directive_t           character;
			newline_directive_t             newline;
			fresh_line_directive_t          fresh_line;
			page_directive_t                page;
			tilde_directive_t               tilde;
			radix_directive_t               radix;
			decimal_directive_t             decimal;
			binary_directive_t              binary;
			octal_directive_t               octal;
			hexadecimal_directive_t         hexadecimal;
			fixed_format_fp_directive_t     fixed_format_fp;
			exponential_fp_directive_t      exponential_fp;
			general_fp_directive_t          general_fp;
			monetary_fp_directive_t         monetary_fp;
			aesthetic_directive_t           aesthetic;
			standard_directive_t            standard;
			write_directive_t               write;
			conditional_newline_directive_t conditional_newline;
			logical_block_directive_t       logical_block;
			indent_directive_t              indent;
			call_function_directive_t       call_function;
			tabulate_directive_t            tabulate;
			justification_directive_t       justification;
			go_to_directive_t               go_to;
			conditional_directive_t         conditional;
			iteration_directive_t           iteration;
			recursive_directive_t           recursive;
			case_conversion_directive_t     case_conversion;
			plural_directive_t              plural;
			escape_upward_directive_t       escape_upward;
			ignored_newline_directive_t     ignored_newline;
		};
	};

	struct control_component_t {
		enum type_t {
			simple_text_t,
			directive_t
		} type;
		union {
			string_t        simple_text;
			any_directive_t directive;
		};
	};
}

#endif
