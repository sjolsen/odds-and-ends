#include <vector>
#include <fstream>
#include "format.hh"

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
