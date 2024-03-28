#include <stdio.h>

enum some { first = 'e', sec };

enum { more = 3 } calc(enum {one, some} name) { return some + 3; }

int main() {
  enum some value = more;
  enum { one = 1, two = 2 } other = sec;

  printf("%d\n", other);
  printf("%d\n", value);
  printf("%d\n", calc(one));

  int a[(enum A{B})4 << 2];
  printf("%d", sizeof(a));
}
