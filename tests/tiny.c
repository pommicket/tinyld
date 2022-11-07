// no dependencies no bss

void entry(void) {
	__asm__ (
		"mov $1, %eax\n"
		"mov $0, %ebx\n"
		"int $0x80\n"
	);
}
