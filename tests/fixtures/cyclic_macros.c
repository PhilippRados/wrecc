#include <stdio.h>

#define ONE TWO
#define TWO THREE
#define THREE ONE

int main() {
  int ONE, TWO, THREE;
  ONE = 1;
  TWO = 2;
  THREE = 3;
  printf("ONE, TWO, THREE = %d, %d, %d \n", ONE, TWO, THREE);
}
