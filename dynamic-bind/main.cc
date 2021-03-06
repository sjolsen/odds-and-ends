#include "foo_module.hh"
#include <iostream>
#include <fstream>

void make_noise ()
{
	foo::do_some_stuff ();
	foo::call_a_callback (foo::do_some_stuff);
}

void make_more_noise ()
{
	foo::do_some_stuff ();
	foo::call_a_callback (make_noise);
}

int main ()
{
	// Make noise with foo's default logger
	make_noise ();
	// Make noise with something a little louder
	DYNAMIC_BIND (foo::log_stream, &std::cout);
	make_noise ();
	{
		// We need to go deeper
		DYNAMIC_BIND (foo::log_stream, &std::cerr);
		make_more_noise ();
		// And now for something... a little different
		std::ofstream my_logfile ("output");
		DYNAMIC_BIND (foo::log_stream, &my_logfile);
		make_more_noise ();
	}
	// Just to prove we can
	make_more_noise ();
}
