register int s;

static int bar(auto int);
int baz(register int[]);

int main() {
  static int foo();
  auto int foor();
  for (register int i = 0;;)
    ;
  for (typedef int i = 0;;)
    ;
  for (static int i = 0;;)
    ;

  static int array[2] = {baz((int *)1)};

  extern char *c;
  extern char *c;

  register int arr[3];
  int *b = arr + 3;
  int *d = arr;
}
