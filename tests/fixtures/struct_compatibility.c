
struct Foo {
  int age;
} a, b;

union Bar {
  int a;
  char b;
} u, u2;
union Bar u3;

int main() {
  struct Foo c;
  a = c;

  struct Foo {
    int age;
  } d;
  a = d;

  u3 = u;
  union Bar {
    int a;
    char b;
  } u4, u5;

  u4 = u3;
  u4 = u5;

  struct Foo z;
  int diff1 = &a - &z;
  int diff2 = &u3 - &u2;

  union Bar u6;
  u6 = u4;
}
