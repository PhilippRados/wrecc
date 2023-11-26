#include <stdio.h>

int a;
int a = 2;
int a;
int x, x = 3, x;

int foo();
int foo() { return 4; }
int foo();

// int foo() { return 2; }

// int some;

typedef int some;
typedef int some;

// int some() { return 1; }

some main() {
  int foo();
  // int some() { return 1; }
  // int some();
  // return a;

  printf("%d\n", foo());
  printf("%d\n", x);
  printf("%d\n", a);
}
