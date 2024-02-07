#include <stdio.h>

void foo(int a) { printf("Hello from foo!\n"); }
void bar(int a) { printf("Hello from foo!\n"); }

int main() {
  int diff = foo - bar;
  void (*next)(int) = foo + 1;
  void (*next2)(int) = foo - 1;

  void (*next3)(int) = 1 + foo;

  return 0;
}
