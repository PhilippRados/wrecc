#include <stdio.h>

union More {
  int a;
  char *empty;
  char name[4];
  long d;
} e = {.name[2] = 'e', .d = 12};

int main() {
  printf("%ld\n", e.d);

  union Foo {
    char s[3];
    char a[2];
  } u = {.s = "uwe", .a[0] = 'b', .s = "aha"};

  printf("%s", u.a);
}
