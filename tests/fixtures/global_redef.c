#include <stdio.h>

int a;
int a = 2;
int a;
int x, y, x = 3, x;

int a, z;

int foo();
int foo() { return 4; }
int foo();

typedef int some;
typedef int some;

int baz();

int bar() { return y; }

some main() {
  int foo();

  printf("%d\n", foo());
  printf("%d\n", baz());
  printf("%d\n", bar());
  printf("%d\n", x);
  printf("%d\n", a);
}

int y = 7, z = 1, e;

int baz() { return z; }
