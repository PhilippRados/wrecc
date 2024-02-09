void foo(int a) {}
int bar(int a) { return 0; }

int main() {
  int a = foo - bar;
  int b = foo + bar;
  int c = foo * bar;
  int d = foo * 1;
  int e = 1 - bar;
  long f = (int *())a;
  int g = ~foo;
  int h = !foo;

  *foo = 1;
  *bar = 1;

  // WARN: doesnt catch this because `foo[3]` is syntax sugar for `*(foo + 3)`
  // and the latter doesn't error
  void *i = foo[3];
}
