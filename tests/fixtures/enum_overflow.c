#include <stdio.h>

enum Some { D = 9223372036854775807, E, F };
enum Other { A = 2147483646, B, C };
enum Foo { BAR = 2147483646, BAZ, BOO = 1 };
enum Else { EDGE = 2147483647 };

int main() {
  printf("%d\n", A);
  printf("%d\n", B);
  printf("%d\n", C);

  printf("%d\n", D);
}
