#include <stdio.h>

int y;

int main() {
  for (int x = 0; x < 5; x++) {
    switch (x) {
    case 1: {
      y = 5;
      break;
    }
    case 2: {
      y = 7;
      break;
    }
    default: {
      y = 100;
      break;
    }
    case 3: {
      y = 9;
    }
    }
    printf("%d\n", y);
  }

  for (int x = 0; x < 5; x++) {
    switch (x) {
    case 1: {
      y = 5;
      break;
    }
    case 2: {
      y = 7;
      break;
    }
    case 3: {
      y = 9;
    }
    default: {
      y = 100;
    }
    }
    printf("%d\n", y);
  }

  // if no default just skip switch
  int a = 0;
  switch (a) {
  case 4: {
    printf("first");
    break;
  }
  case 3: {
    printf("second");
    break;
  }
  }

  switch (a) {
  case 4: {
    printf("first");
    break;
  }
  case 3: {
    printf("second");
    break;
  }
  default: {
    printf("else");
    break;
  }
  }
}
