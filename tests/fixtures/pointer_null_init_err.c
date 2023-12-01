#include <stdio.h>

struct {
  int age;
} *p = 1;

void *some() { return -1 + 1; }

int main() {
  char *c = 0;
  int *b = 1 - 2 + 0;

  if (b == 1 - 2) {
    printf("%p", some());
  } else {
    printf("else");
  }
}
