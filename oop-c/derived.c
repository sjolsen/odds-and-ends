#include "derived.h"

#include <stdio.h>
#include <stddef.h>
#include <assert.h>

static void derived_foo (base1_t* this);
static void derived_bar (base2_t* this);
static void derived_quux (base3_t* this);

/* Public interface */

static const base2_vtable_t derived_base2_vtable = {
	.bar = &derived_bar,
};

static const base3_vtable_t derived_base3_vtable = {
	.base1_vtable = {
		.foo = &derived_foo,
	},
	.quux = &derived_quux,
};

derived_t derived (FILE* file, const char* str)
{
	assert (file != NULL);
	assert (str != NULL);

	return (derived_t) {
		.base2 = {
			.vtable = &derived_base2_vtable,
		},
		.base3 = {
			.base1 = {
				.vtable = &derived_base3_vtable.base1_vtable,
			},
			.vtable = &derived_base3_vtable,
		},
		.file = file,
		.str  = str,
	};
}

/* Implementation */

static void derived_foo (base1_t* this)
{
	derived_t* _this = DOWNCAST_BASE1_TO_DERIVED (this);
	fprintf (_this->file, "Derived foo: %s\n", _this->str);
}

static void derived_bar (base2_t* this)
{
	derived_t* _this = DOWNCAST_BASE2_TO_DERIVED (this);
	fprintf (_this->file, "Derived bar: %s\n", _this->str);
}

static void derived_quux (base3_t* this)
{
	derived_t* _this = DOWNCAST_BASE3_TO_DERIVED (this);
	fprintf (_this->file, "Derived quux: %s\n", _this->str);
}
