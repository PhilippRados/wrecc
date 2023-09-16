#include <stdio.h>

#if foo < 3
char* first = "true";
#endif

#define some 3
#if defined(  some ) && !none
char* sec = "true";
#endif

#if (!defined some & 3) + 2
char* third = "true";
#endif

// TODO: defines replacement:
// #define foo some name
// #if some || foo
// #define foo some
// #if foo - 3
// char* fourth = "true";
// #else
// char* fourth = "false";
// #endif

// TODO: < string replacement
// #if 2 < some
// ...
// #endif

#define foo bar
#if foo != 0
char* fourth = "true";
#endif
char* fourth = "false";


int main() {
  printf("%s\n",first);
  printf("%s\n",sec);
  printf("%s\n",third);
  printf("%s\n",fourth);
}
