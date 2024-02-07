#include <stdio.h>

void foo() { printf("Hello from foo!\n"); }
void bar() { printf("Hello from bar!\n"); }

int main() {
  void (*func_array[2])() = {foo, bar};
  // void (*func_array[2])();

  // func_array[0] = foo;
  // func_array[1] = bar;

  func_array[0](); // Calls foo
  func_array[1](); // Calls bar

  return 0;
}
