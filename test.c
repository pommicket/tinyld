#include <stdio.h>
#include <stdlib.h>

extern int errno;
int main() {
	errno = 0;
	fopen("zzz","r");
	printf("%d\n",errno);
	//printf("hello\n");
	exit(0);
	    
}
