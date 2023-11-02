long a[100000] = {1, [4000] = 3, 4, 5, 5};

struct Foo {
  int age;
  char *e;
} b = {a, "he", .age = 3};

int main() {
  int a[2][3] = {[0] = 1, 4, [1] = 6, 7, 9, [0] = 2};
  int b[3] = {[2] = 2, 3, 4};
  int c[2][2][2] = {[0][1][0] = 3, 4, 5, 6, 7, 8};
  int d[2][2][2] = {[1][0][0] = 3, 4, 6};

  struct Foo {
    int age;
    struct Other {
      char s[3];
      char c;
    } name[2];
  } e = {1, {2, 'h', '2'}, {1, 2}, 3};
  union Bar {
    long a;
    int more[3];
  } t = {2, .more = 3, .a = 6};

  union Else {
    int more[3];
    int a;
  } l = {1, 2, 3, 5};

  struct Foo2 {
    union Bar age;
    char name[2];
  } k = {.age.more = {1, 2}, "he", .age = 1, 2, 4};

  int p[2][2][1] = {[0][1] = {1, 2}};

  struct Mo {
    struct Foo2 e;
  } h = {.e.age.more = 4};

  int hall[2][2] = {1, [0] = {2, 3}};
}
