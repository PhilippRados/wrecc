#include <stdio.h>

struct {
  int age;
} *p = 0;

void *some() { return 0; }

int main() {
  char *c = 0;
  int *b = (long)1 - 1;

  if (b == 1 - 1) {
    printf("%p", some());
  } else {
    printf("else");
  }
}
