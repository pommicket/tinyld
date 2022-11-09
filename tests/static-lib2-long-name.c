#include "static-lib.h"
#include <stdio.h>

int g() {
	++p;
	printf("call %d\n", p);
	return p;
}
