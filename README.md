# tinyld

a linker for making tiny 32-bit linux executables.

*Just after* making this, I found out that something similar already existed here:
https://github.com/Shizmob/smol/ -- although smold's executables are giving me segfaults
for some reason.
This linker is worse in terms of output size, but the executables are more standard-compliant
and don't rely on undocumented ELF magic. The difference isn't even that big (in the 10s of bytes)
after compressing with `xz` -- so if you're using [this handy executable unpacker](https://gitlab.com/PoroCYon/vondehi),
you'll get about the same output size.

## Executable sizes

Exit using inline assembly (tests/tiny.c): **93 bytes**

Hello world: **369 bytes** (252 bytes `xz`-compressed)

Open a window, get a GL context, and call `glClearColor`, `glClear` each frame (tests/sdl.c): **881 bytes**
(532 bytes `xz`-compressed)

## Installation

You will need a [rust installation](https://www.rust-lang.org/tools/install).

```
cargo install --path .
```

##  Usage

`gcc-multilib`/`g++-multilib` are needed for 32-bit headers for C/C++.

Example: create a file called `hello.c` containing
```
#include <stdio.h>
#include <stdlib.h>

void entry(void) {
	printf("Hello, world!\n");
	exit(0);
}
```

then run `tinyld hello.c -o hello`. You now have an executable called `hello` which prints `Hello, world!`.

To add libaries, use e.g. `tinyld my_sdl_program.c libSDL2.so`.

You can use C++, but exceptions probably won't work, and `cout`/`cin` don't seem to work either
(you should be using `printf` anyways if you want a smaller executable).

Only 32-bit x86 ELF is supported. If you give tinyld a 64-bit executable it will die.
If you're compiling your own object files, you need to add `-fno-pic` otherwise tinyld will die.

For more information, see `tinyld --help`.
