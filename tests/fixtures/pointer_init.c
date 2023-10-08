#include <stdio.h>

struct Some {
  char c;
  int *a;
};

int a = 4;
struct Some arr[2] = {{'d'}, {'a', &a}};

int main() {
  printf("%c,%p\n", arr[0].c, arr[0].a);
  printf("%c,%d\n", arr[1].c, *arr[1].a);
}
