// temporary test file

#include <stdlib.h>

int f() { return 13; }

void entry(void) {
	exit(f());
}
