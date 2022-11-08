// temporary test file

#include<stdio.h>
#include <stdlib.h>
int f() {
	return 7;
}


void entry(void) {
	printf("%d\n", f());
	exit(0);
}
