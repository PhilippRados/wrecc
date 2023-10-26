#include <stdio.h>

union More {
  int a;
  char *empty;
  char name[4];
  long d;
} e = {.name[2] = 'e', .d = 12};

int main() { printf("%d\n", e.d); }
