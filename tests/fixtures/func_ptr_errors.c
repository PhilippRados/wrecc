#include <stdio.h>

void foo(int a) { printf("Hello from foo!\n"); }

typedef void (*Callback)(int);

void callbackFunction(long *value) {
  printf("Callback with value: %p\n", value);
}

int main() {
  void (*func)(void) = foo;
  void (**func2)(void) = &func;

  func2();

  int(func_ptr)() = 42;

  Callback callback = callbackFunction; // Error: Incompatible argument type
  callback(42); // This would result in undefined behavior

  return 0;
}
