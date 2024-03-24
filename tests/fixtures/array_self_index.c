#include <stdio.h>

int main() {
  int a[10] = {[2] = 3, [5] = 1};
  a[0] = 0;
  a[0][a] = 1;
  a[2][a] = 1;

  *(*(5 + a) + a) = 2;

  for (int i = 0; i < 10; i++) {
    printf("%d\n", a[i]);
  }
}
