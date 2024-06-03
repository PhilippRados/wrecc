#include <stdio.h>

int main() {
  int a = 0;
  int b = 3;
  int c = 'a';

  int *p = &a - 1;
  int *p2 = &b + 1;
  int *p3 = &a - 2;
  int *p4 = 1 + &c;

  printf("%d\n", *p);
  printf("%d\n", *p2);
  printf("%d\n", *p3);
  printf("%d\n", *p4);

  // make sure scaling works same way as in fold
  {
    int offset = -1;
    void *p = (short *)5 + offset;
    printf("%p\n", p);
  }
  {
    long offset = -9223372036854775807;
    void *p = (int *)1 + offset;
    printf("%p\n", p);
  }
  {
    int offset = 2147483646;
    void *p = (int *)1 + offset;
    printf("%p\n", p);
  }
  {
    long offset = 9223372036854775806;
    void *p = (short *)1 + offset;
    printf("%p\n", p);
  }

  int arr[] = {1, 2, 3, 4, 5, 6};
  int *p_arr = &arr[2];
  printf("%d\n", p_arr[-1]);
  printf("%d\n", p_arr[-9223372036854775807]);
}
