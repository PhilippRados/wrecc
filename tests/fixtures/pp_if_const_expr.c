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

#define foo some
#if foo == 3
char* fourth = "true";
#endif

#define other bar
#if other != 0
char* fifth = "true";
#endif
char* fifth = "false";

#if 2 < some && !undefined
char* sixth = "true";
#endif

int main() {
  printf("%s\n",first);
  printf("%s\n",sec);
  printf("%s\n",third);
  printf("%s\n",fourth);
  printf("%s\n",fifth);
  printf("%s\n",sixth);
}
