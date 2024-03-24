#include <stdio.h>

#define LEN 10

long b[LEN] = {};

int main() {
  int a[LEN] = {};

  for (int i = 0; i < LEN; i++) {
    printf("%d,%ld\n", a[i], b[i]);
  }
}
