#include <stdio.h>

static int foo() {
  static int i = 0;
  return ++i;
}

extern int bar() {
  static int i = 0;
  return ++i;
}

extern int k;
int k;

int main() {
  foo();
  foo();
  foo();
  bar();
  register int i = foo();
  auto int j = bar();

  printf("%d,%d,%d", i, j, k);
}
