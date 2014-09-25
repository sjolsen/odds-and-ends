#ifndef FOO_MODULE_HH
#define FOO_MODULE_HH

#include "dynamic_bind.hh"
#include <iosfwd>

namespace foo
{

namespace detail
{
void call_a_callback_impl (void (*) (void*), void*);
}

extern
dynamic_variable <std::ostream*> log_stream;

void do_some_stuff ();

template <typename F>
inline
void call_a_callback (F f)
{
	detail::call_a_callback_impl ([] (void* f) { (*static_cast <F*> (f)) (); }, &f);
}

}

#endif
