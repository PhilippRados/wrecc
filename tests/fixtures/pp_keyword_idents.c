#include <../include/stdio.h>

#define if 2

#if if != 2
int main() { printf("actual:%d\n", if); }
#elif defined if
int main() { printf("elif actual:%d\n", if + 1); }
#elif include
int main() { printf("include actual:%d\n", if + 1); }
#else
int main() { printf("actual:%d\n", else); }
#endif
