// this should be allowed but isn't:
// typedef int m(const int);
// typedef int m(int);

int foo(volatile int *);
int foo(const int *);

int boo(const int a);
int boo(int a);

const int goo(void *);
int goo(void *);

int main() {
  int (*bar)(int *const) = foo;
  int (*baz)(volatile int *) = foo;
  const int (*boi)(void *) = goo;
}
