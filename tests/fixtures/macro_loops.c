#ifndef TESTING
#define TESTING
#define T1
#define T4
#include <stdio.h>
int main(void) {
#include "macro_loops.c"
#elif !defined T16
printf("Hello\n");
#ifndef T1
#define T1
#else
#undef T1
#ifndef T2
#define T2
#else
#undef T2
#ifndef T4
#define T4
#else
#undef T4
#ifndef T8
#define T8
#else
#undef T8
#ifndef T16
#define T16
#endif
#endif
#endif
#endif
#endif

#include "macro_loops.c"
#else
return 0;
}
#endif
