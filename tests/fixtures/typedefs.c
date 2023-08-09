void printf(char* f, int d);

typedef int FOO;
FOO var1;

struct bar {
  int x;
  int y;
};

typedef struct bar BAR;

int main() {
  {
    struct something {int age;};

    typedef char something;

    something first = -3;
    printf("%d\n", first);
  }
  BAR var2;

  var1 = 5;
  printf("%d\n", var1);

  var2.x = 7;
  var2.y = 10;
  printf("%d\n", var2.x + var2.y);
}
