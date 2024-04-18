#include <stdio.h>

enum Tok { One, Two, Three };

void nest(enum Tok tok[]) {
  for (int i = 0; i < 3; i++) {
    printf("%d", tok[i]);
  }
  switch (tok[0]) {
  case One: {
    switch (tok[1]) {
    case One:
      printf("nest\n");
      break;
    default:
      return;
    }
  }
  case Three: {
    printf("second\n");
    break;
  }
  default: {
    switch (tok[2]) {
    case Three: {
      printf("sec nest\n");
      break;
    }
    default: {
      return;
    }
    }
    printf("none\n");
    break;
  }
  }
}

int main() {
  enum Tok arr1[] = {Two, Three, Three};
  nest(arr1);

  enum Tok arr2[] = {One, One, Two};
  nest(arr2);
}
