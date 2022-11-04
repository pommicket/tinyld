#include <stdio.h>
int x;
void main() {
	x = 123;
	printf("hi");
	__asm__ ("movl $1, %%eax\n"
		"movl %0, %%ebx\n"
	    "int $0x80\n"
	    :
	    : "r" (x) : "ebx", "eax");
	    
}
