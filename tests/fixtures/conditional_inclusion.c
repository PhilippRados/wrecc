#include <stdio.h>

#ifdef foo
#define num 0
#elif 1 - (foo + !defined more)
#define num 1
#elif !okay_this_is_it
#define num 2
#elif unreachable
#define num other
#else
#define num unreachable
#endif

#if 1 << 2 > 8
int main() { printf("actual:%d\n", num); }
#else
int main() { printf("debug:%d\n", num); }
#endif
