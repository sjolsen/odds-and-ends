#include "derived.h"

int main ()
{
	derived_t d = derived (stdout, "hello");
	foo (&d.base3.base1);
	bar (&d.base2);
	quux (&d.base3);
}
