#include <stdio.h>

int main() {
  unsigned char b = 200;
  char a = b;
  printf("%d\n", a);
  printf("%d\n", b);

  long d = (unsigned)-3;
  printf("%ld", d);
}
