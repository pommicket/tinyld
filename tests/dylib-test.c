#include "dylib.h"
#include <stdlib.h>
#include <stdio.h>

void entry(void) {
	the_number = 7;
	printf("%d\n",the_number);
	bigger();
	printf("%d\n",the_number);
	
	exit(0);
}
