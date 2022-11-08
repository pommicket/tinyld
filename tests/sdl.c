#define SDL_DISABLE_IMMINTRIN_H
#include <SDL2/SDL.h>
#include <GL/glcorearb.h>
#include <stdio.h>
#include <stdbool.h>

int main(void) {
	SDL_Init(SDL_INIT_EVERYTHING);
	SDL_Window *window = SDL_CreateWindow("hi", 0, 0, 1280, 720, SDL_WINDOW_SHOWN|SDL_WINDOW_OPENGL);
	SDL_GLContext ctx = SDL_GL_CreateContext(window);
	PFNGLCLEARPROC glClear = SDL_GL_GetProcAddress("glClear");
	PFNGLCLEARCOLORPROC glClearColor = SDL_GL_GetProcAddress("glClearColor");
	SDL_GL_SetSwapInterval(1);
	while (true) {
		SDL_Event event;
		while (SDL_PollEvent(&event)) {
			if (event.type == SDL_QUIT) {
				return 0;
			}
		}
		glClearColor(1, 1, 1, 1);
		glClear(GL_COLOR_BUFFER_BIT);
		SDL_GL_SwapWindow(window);
	}
	(void)ctx;
}

void entry(void) {
	exit(main());
}
