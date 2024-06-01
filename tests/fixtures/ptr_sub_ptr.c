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
  // implementation defined: wrecc and clang emit 3, gcc 1
  printf("%d\n", p2);

  char(*k)[9];
  char(*j)[9];
  long res = j - &j[2];
  long res2 = j - k;
  printf("%ld\n", res);

  long s = (const short *)9223372036854775809 - (short *)1;
  long s2 = 9223372036854775808;
  long l = (long)(const short *)9223372036854775809 - (long)(short *)1;
  long l2 = -9223372036854775806;
  long u = (unsigned long)9223372036854775809 - (unsigned long)1;

  printf("%ld\n", s);
  printf("%ld\n", s2);
  printf("%ld\n", l);
  printf("%ld\n", l2);
  printf("%ld\n", u);

  unsigned long v = 9223372036854775809;
  long big_var = (const short *)v - (short *)1;
  printf("%ld\n", big_var);
}
