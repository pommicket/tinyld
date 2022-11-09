#include "static-lib.h"

#include <stdlib.h>
#include <stdio.h>

int main(void) {
	printf("%d\n",f());
	printf("%d\n",f());
	return 0;
}

void entry(void) {
	exit(main());
}
