#ifndef BASE3_H
#define BASE3_H

#include "base1.h"
#include "oop.h"

typedef struct base3 base3_t;
typedef struct base3_vtable base3_vtable_t;

struct base3
{
	base1_t base1;
	const base3_vtable_t* vtable;
};

struct base3_vtable
{
	base1_vtable_t base1_vtable;
	void (*quux) (base3_t* this);
};

#define DOWNCAST_BASE1_TO_BASE3(this) \
	DOWNCAST_FROM_MEMBER(base3_t, base1, this)

static inline
void quux (base3_t* this)
{ this->vtable->quux (this); }

#endif
