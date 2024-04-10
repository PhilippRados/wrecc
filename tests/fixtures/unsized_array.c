#include <stdio.h>

int a[];
int main() {
  int z[] = {1, 2, 3, [10] = 1, 11, [3] = 5};
  int e[][2] = {{1, 2}, 1, 2, 3, 5, 6, 6, 7};
  char s[] = "hello";

  printf("%ld\n", sizeof(z));
  printf("%ld\n", sizeof(s));
  printf("%ld\n", sizeof(e));
  printf("%s\n", s);

  for (int i = 0; i < sizeof(z) / sizeof(z[0]); i++) {
    printf("%d\n", z[i]);
  }
  for (int i = 0; i < 2; i++) {
    printf("%d\n", a[i]);
  }

  int(*k)[12] = &z;
  int(*k2)[] = &z;
  int(*k3)[] = k2;

  printf("%ld\n", sizeof(*k));
}

int a[] = {1, 23};
