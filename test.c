int x;
void entry() {
	x += 1;
	__asm__("xor %ebx, %ebx\n"
                "int $0x80\n");
}
