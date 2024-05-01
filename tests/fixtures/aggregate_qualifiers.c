int main() {
  typedef int A[2][3];
  volatile A a = {{4, 5, 6}, {7, 8, 9}}; // array of array of volatile int
  int *pi = a[0];

  union Foo {
    int age;
    struct {
      int coo;
    } nest;
  };

  volatile union Foo foo;
  foo.age = pi;

  const union Foo bar;
  bar.age = *pi;
  bar.nest.coo = 2;
}
