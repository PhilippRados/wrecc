#include <setjmp.h>
#include <stdio.h>

// Define a jump buffer
jmp_buf jump_buffer;

// Function that performs division and handles division by zero error
int divide(int a, int b) {
  // Save the current execution context in the jump buffer
  if (b == 0) {
    printf("Error: Division by zero\n");
    longjmp(jump_buffer, 1); // Jump back to the point where setjmp was called
  }
  return a / b;
}

int main() {
  int result;

  // Setjmp saves the current execution context in jump_buffer
  if (setjmp(jump_buffer) == 0) {
    // Call divide function
    result = divide(2, 0);
    printf("Result of division: %d\n", result);
  } else {
    // Error handling path
    printf("Error occurred during division\n");
  }

  return 0;
}
