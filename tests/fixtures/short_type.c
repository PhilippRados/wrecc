#include <stdio.h>

short int foo(int short s) { return 4 - s; }

int main() {
  char c = sizeof((short int)5);
  short int s = foo(9);
  int short o = foo(3);
  printf("%d", c);
  printf("%d", s);
  printf("%d", o);
  printf("%ld", sizeof(s));
}
