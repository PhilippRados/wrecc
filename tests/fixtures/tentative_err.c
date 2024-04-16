
int a[];

struct Uwe k;

struct Bar gh, gb;

struct Bar kso = gh;

int b[];
int b[] = {1, 2, 3};
int b[20];

typedef int ty[];
typedef int ty[2];
typedef int ty[];

void call(char *, ...);

int main() {
  gh.age = 12;
  a[0] = 3;
  extern void v;

  gh = gb;
  sizeof(a);

  call("print", a);
  call("print", v);
}

struct Bar {
  int age;
};
