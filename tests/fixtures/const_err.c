#include <stdio.h>

// const int g;
// int g;

// int foo(int);
// int foo(const int);

struct Foo {
  int age;
  const enum { One, Two } dig;
} a, b;

int main() {
  a.age = 45;
  a.dig = Two;
  a = b;

  const int n;
  n++;

  typedef int A[2][3];
  const A nest = {{4, 5, 6}, {7, 8, 9}}; // array of array of const int
  int *pi = nest[0];                     // Error: a[0] has type const int*

  const char *str1 = "Hello"; // Pointer to constant data
  char *const str2 = "World"; // Constant pointer to mutable data
  str1[0] = 'h';
  str1 = "uwe";
  str2 = "Goodbye";
  str2[0] = 3;
  printf("str1: %s\n", str1);
  printf("str2: %s\n", str2);

  typedef const int num;
  volatile num a = 5;
  a = 5;

  int *p = 0;
  const int *cp = p; // OK: adds qualifiers (int to const int)
  p = cp;            // Error: discards qualifiers (const int to int)
  p = (int *)cp;     // OK: cast

  const char *jdk;
  volatile char *pk;
  jdk = pk;

  // int *dsj = (const int *)0;
  // const int *dsp = (int *)0;

  long *const *s0;
  long **s1 = s0;

  long *const *sj;
  long **sjj = sj;

  long **const s9;
  long **s8 = s9;

  long **s;
  const long **s2 = s;
  long *s3;
  const long *s4 = s3;
}
