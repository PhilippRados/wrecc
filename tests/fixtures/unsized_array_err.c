#include <stdio.h>

int global[];

struct {
  int age;
  int a[];
  long c;
} foo = {1, {}};

typedef int array[9];

int also_glob[][2] = {1, 2, {1, 2}, 4, 5};

int main() {
  array a[] = {1, 2, 3};
  int a[] = 34;
  int also[][2] = {1, 2, {1, 2}, 4, 5};

  // int arr[4] = {*arr + 3, [3] = 2, [0] = 3};
  int b[][] = {1, 2, {2, 4, 5}};
  (int *[])2;
  int c[] = {1, {23, 2}};

  int e[] = 1;
  int e1[2] = 1;

  long *f[] = {sizeof(f)};
  sizeof(array[]);
  sizeof(global);

  long(*p[])[];

  int some_arr[] = {1, 2, 3};
  int(*k2)[] = &some_arr;
  printf("%ld", sizeof(*k2));

  long *first[] = {(long *)1, (void *)2};
  long *sec[] = {(long *)2, (void *)3};
  long(*three[])[] = {first, sec};

  long(*also2)[][2] = &also;
}

int global[] = {1};

void bar() { sizeof(global); }
int func(int a[2][]) { return 0; }
