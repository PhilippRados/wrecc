#include <limits.h>
#include <stdio.h>

int main() {
  {
    unsigned int a = UINT_MAX;
    unsigned int b = 2;
    printf("%u\n", a % b);
    printf("%u\n", a / b);
  }
  {
    unsigned long a = ULONG_MAX;
    unsigned long b = 2;
    printf("%lu\n", a / b);
  }
  {
    long a = LONG_MAX;
    long b = 2;
    printf("%ld\n", a / b);
  }
}
