#include <stdio.h>

enum Some { D = 2147483648, E, F };  // no overflow since fold truncates
enum Other { A = 2147483647, B, C }; // overflow

int main() {
  printf("%d\n", A);
  printf("%d\n", B);
  printf("%d\n", C);

  printf("%d\n", D);
  printf("%d\n", E);
  printf("%d\n", F);
}
