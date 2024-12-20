#include <stdio.h>

int main() {
    int B = 42;
#define A B
#define B C
#define C B, B
    printf("%d %d\n", A);
}
