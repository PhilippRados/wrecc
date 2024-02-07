#include <stdio.h>

typedef void(Callback)(int);

void callbackFunction(int value) { printf("Callback with value: %d\n", value); }

void doSomething(Callback callback) { callback(42); }
void alsoDoSomething(Callback *callback) { callback(12); }

int main() {
  doSomething(callbackFunction);
  doSomething(&callbackFunction);
  alsoDoSomething(callbackFunction);
  alsoDoSomething(&callbackFunction);
  return 0;
}
