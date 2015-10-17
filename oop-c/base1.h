#ifndef BASE1_H
#define BASE1_H

typedef struct base1 base1_t;
typedef struct base1_vtable base1_vtable_t;

struct base1
{
	const base1_vtable_t* vtable;
};

struct base1_vtable
{
	void (*foo) (base1_t* this);
};

static inline
void foo (base1_t* this)
{ this->vtable->foo (this); }

#endif
