struct Emp {
  long some;
  int id;
};

void printf(char* s,int d);
struct Emp* malloc(int d);

struct Emp other;

struct Emp* init() {
  struct Emp* e = malloc(12);
  e->id = 3;
  (*e).some = 1;
  return e;
}

int main() {
  struct Emp emp;

  int id = init()->id;
  struct Emp another = other = emp = *init();

  printf("%d\n",id);

  printf("%d\n",emp.id);
  printf("%d\n",emp.some);

  printf("%d\n",other.id);
  printf("%d\n",other.some);

  printf("%d\n",another.id);
  printf("%d\n",another.some);
}
