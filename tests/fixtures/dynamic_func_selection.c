#include <stdio.h>

void add(int a, int b) { printf("Sum: %d\n", a + b); }

void subtract(int a, int b) { printf("Difference: %d\n", a - b); }

int main() {
  void (*operation)(int, int) = NULL;

  // Dynamically select function based on some condition
  int condition = 0;
  if (condition) {
    operation = add;
  } else {
    operation = subtract;
  }

  operation(5, 3);
  return 0;
}
