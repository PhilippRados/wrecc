#include <stdio.h>

typedef void(Callback)(int);

void callbackFunction(int value) { printf("Callback with value: %d\n", value); }
int otherCallbackFunction(int value) {
  printf("other with value: %d\n", value);
  return 0;
}

void doSomething(Callback callback) { callback(42); }
void alsoDoSomething(Callback *callback) { callback(12); }

Callback *getFunc() {
  Callback *test = callbackFunction;
  return test;
}
int (*alsoGetFunc(void))(int) {
  int (*test)(int) = otherCallbackFunction;
  return test;
}

int main() {
  doSomething(callbackFunction);
  doSomething(&callbackFunction);
  alsoDoSomething(callbackFunction);
  alsoDoSomething(&callbackFunction);

  getFunc()(2);
  alsoGetFunc()(3);

  return 0;
}
