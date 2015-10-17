#ifndef BASE2_H
#define BASE2_H

typedef struct base2 base2_t;
typedef struct base2_vtable base2_vtable_t;

struct base2
{
	const base2_vtable_t* vtable;
};

struct base2_vtable
{
	void (*bar) (base2_t* this);
};

static inline
void bar (base2_t* this)
{ this->vtable->bar (this); }

#endif
