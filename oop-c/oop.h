#ifndef OOP_H
#define OOP_H

#include <stddef.h>
#include <stdint.h>

#define DOWNCAST_FROM_MEMBER(type,member,this) ( \
	(type*) ( \
		((uint8_t*)(this)) - offsetof (type, member) \
	) \
)

#endif
