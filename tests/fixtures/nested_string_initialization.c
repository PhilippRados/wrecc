void printf(char* f,int d, char* s);
void puts(char* s);

struct Some {
  char s[6];
  int age;
};

int main() {
  char s[2][3] = {"ha", "le"};
  (*s)[1] = 'x';
  puts(*s);

  //struct Some e[2] = {"ha", 2, {"looooo", 2}};
  struct Some e[2] = {{.s = "test"}, [0].age = 3, [1].s = "some", 1};

  for (int i = 0; i < 2; i++) {
    printf("%d\n%s\n", e[i].age, e[i].s);
  }
}
