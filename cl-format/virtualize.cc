#include <iosfwd>
#include <experimental/string_view>

struct format_vtable
{
	std::ostream& (*princ) (std::ostream&, const void*);
};

template <typename T>
struct format_vtable_instantiate
{
	static format_vtable instance;
};

template <typename T>
format_vtable format_vtable_instantiate <T>::instance = {
	[] (std::ostream& os, const void* arg) -> auto& {
		return os << *static_cast <const T*> (arg);
	}
};



class format_arg
{
	const format_vtable* _vtable;
	const void* _arg;

public:
	template <typename Arg>
	format_arg (const Arg& arg)
		: _vtable (&format_vtable_instantiate <Arg>::instance),
		  _arg (&arg)
	{
	}

	friend
	std::ostream& princ (std::ostream& os, format_arg arg)
	{
		return arg._vtable->princ (os, arg._arg);
	}
};

template <typename... Args>
std::ostream& format (std::ostream& os, std::experimental::string_view fmt, Args&&... args)
{
	for (auto arg : {format_arg {args}...})
		princ (os, arg);
	return os;
}


#include <iostream>

int main ()
{
	format (std::cout, "", 1, 42.3, "foobar", '\n');
}
