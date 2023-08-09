int printf(char* s, int d);

typedef struct s *sp;

struct s my_struct;

struct s {
  int outer;
};

int main() {
  sp my_struct_pointer = &my_struct;
  int c = my_struct_pointer->outer = 4;

  printf("%d\n",c);
}
