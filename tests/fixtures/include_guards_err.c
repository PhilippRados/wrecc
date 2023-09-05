#include <stdio.h>

#ifndef _STDIO_H_
  int main() { printf("%d\n", 1); }
#endif

#endif

#ifndef sme

#define real_main
#ifdef real_main
  int main() { printf("%d\n", 2); }
#   endif

#ifdef uwe
  #ifdef some
#endif
