#include <stdio.h>

long foo(unsigned);
long foo(unsigned int a) { return a; }

int main() {
  printf("%ld\n", foo((unsigned short)-1));

  unsigned int c = 2147483649;
  int d = 2000;
  int s = d + c;
  printf("%d\n", c);
  printf("%d\n", s);

  unsigned long i = 999999u * 9999999 * 999999;
  unsigned long l = -9223372036854775808u + 1;
  printf("%lu\n", i);
  printf("%lu\n", l);

  int eq = 18446744073709551615u == 18446744073709551615ll;
  printf("%d\n", eq);

  unsigned char n = 372897938;
  printf("%ld\n", (long)n);
}
