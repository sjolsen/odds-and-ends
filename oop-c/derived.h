#ifndef DERIVED_H
#define DERIVED_H

#include "base1.h"
#include "base2.h"
#include "base3.h"
#include "oop.h"

#include <stdio.h>

typedef struct derived
{
	base2_t base2;
	base3_t base3;
	FILE* file;
	const char* str;
} derived_t;

#define DOWNCAST_BASE1_TO_DERIVED(this) \
	DOWNCAST_BASE3_TO_DERIVED ( \
		DOWNCAST_BASE1_TO_BASE3(this) \
	)
#define DOWNCAST_BASE2_TO_DERIVED(this) \
	DOWNCAST_FROM_MEMBER(derived_t, base2, this)
#define DOWNCAST_BASE3_TO_DERIVED(this) \
	DOWNCAST_FROM_MEMBER(derived_t, base3, this)

derived_t derived (FILE* file, const char* str);

#endif
