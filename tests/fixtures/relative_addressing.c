#include <stdio.h>

int main() {
  int (*f)(char *, ...) = printf;

  f("hello");

  printf("uwe");
}
