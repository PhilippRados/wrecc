#include <stdio.h>

int a[];
int a[];

int b[];
int b[20];
int b[] = {1, 2, sizeof(b)};

struct S bar;
struct S {
  int age;
};

int main() {
  bar.age = 12;
  a[0] = 3;
  printf("%d\n", a[0]);
  printf("%d\n", bar.age);
  printf("%ld\n", sizeof(b));
}

int a[] = {1, 23};
