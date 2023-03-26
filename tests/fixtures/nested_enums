void printf(char* f, int d);

struct some {
  union {
      struct {
          struct some* a;
        } b;
      enum {one = 1, two} c;
    } z;
} value;

int main(){
  int a = value.z.c = one;

  printf("%d\n", a);
  printf("%d\n", two);
  printf("%d\n", value.z.c);
}
