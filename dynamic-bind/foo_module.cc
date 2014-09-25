#include "foo_module.hh"
#include <ostream>

namespace foo
{

namespace
{

dynamic_variable <int> log_level = 0;

inline
std::ostream& print (std::ostream& os)
{
	return os;
}

template <typename First, typename... Rest>
std::ostream& print (std::ostream& os, First&& first, Rest&&... rest)
{
	return print (os << std::forward <First> (first), std::forward <Rest> (rest)...);
}

template <typename... Args>
void log (Args&&... args)
{
	if (log_stream)
	{
		for (int i = 0; i < log_level; ++i)
			print (*log_stream, "  ");
		print (*log_stream, std::forward <Args> (args)...);
		*log_stream << std::endl;
	}
}

}

// Disable logging by default
dynamic_variable <std::ostream*> log_stream = nullptr;

void do_some_stuff ()
{
	log ("Doing some stuff!");
}

namespace detail
{

void call_a_callback_impl (void (*callback) (void*), void* data)
{
	log ("Calling a callback:");
	{
		DYNAMIC_BIND (log_level, log_level + 1);
		callback (data);
	}
	log ("Callback finished");
}

}

}
