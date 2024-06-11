#include <stdio.h>

int main() {
  if (0xFFFFFFFF == 037777777777) {
    printf("equal");
  }
  if (0xFFFFFFFA == -6) {
    printf("equal");
  }
  if (-0xFFFFFFFF == 0xFFFFFFFF) {
    printf("equal");
  }
}
