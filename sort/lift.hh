#ifndef LIFT_HH
#define LIFT_HH

#include <utility>

#define LIFT(fname) \
[] (auto&&... args) -> decltype (auto) \
{ \
	return fname (std::forward <decltype (args)> (args)...); \
}

#endif
