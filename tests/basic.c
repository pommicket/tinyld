#include <stdio.h>
#include <stdlib.h>

int my_number;
void entry() {
	volatile int *p = &my_number;
	*p = 137;
	printf("%d\n",*p);
	exit(0);
	    
}
