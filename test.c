#include<stdio.h>

void entry(void) {
	printf("hi\n");
	__asm__ (
		"mov $1, %eax\n"
		"mov $0, %ebx\n"
		"int $0x80\n"
	);
}
