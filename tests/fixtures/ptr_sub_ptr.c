#include <stdio.h>

int main() {
  long a = 0;
  long b = 3;
  int p = &b - &a;
  printf("%d\n", p);

  int c;
  long e;
  int t;
  int p2 = &c - &t;
  printf("%d\n", p2);

  char(*k)[9];
  char(*u)[9];
  long res = u - &u[2];
  long res2 = u - k;
  printf("%ld\n", res);
}
