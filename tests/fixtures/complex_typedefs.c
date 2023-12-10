void printf(char *f, int d);

typedef struct {
  int x;
  int y;
} Point;

typedef struct {
  Point start;
  Point end;
} Line;

typedef struct {
  char name[20];
  int age;
  Line address;
} Person;

int main() {
  typedef int Number;
  Number a = 5;

  {
    typedef char Number;
    Number b = 'd';
    printf("b = %c\n", b);
  }

  printf("a = %d\n", a);

  Person john = {"John", 25, {{12, 3}, {-7, 1}}};
  printf("a = %c\n", john.name[0]);
  printf("a = %c\n", john.name[1]);
  printf("a = %c\n", john.name[2]);
  printf("a = %c\n", john.name[3]);

  printf("a = %d\n", john.age);
  printf("a = %d\n", john.address.start.x);
  printf("a = %d\n", john.address.start.y);
  printf("a = %d\n", john.address.end.x);
  printf("a = %d\n", john.address.end.y);
}
