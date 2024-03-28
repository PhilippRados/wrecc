#include <stdio.h>

char c = 3000;
char c2 = -3000;

char c3 = -3000 + 200;
int d = ((char)-3000) + 200;

int main() {
  int d2 = ((char)-3000) + 200;
  int d3 = 2147483649;

  printf("%d\n", c);
  printf("%d\n", c2);
  printf("%d\n", c3);
  printf("%d\n", d);
  printf("%d\n", d2);
  printf("%d\n", d3);
}
