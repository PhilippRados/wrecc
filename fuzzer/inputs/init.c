struct Some {
  int age;
  struct Some *self;
} e = {.age = 12, (void *)0};

int main() {
  typedef struct Some other_un;

  other_un container = {.age = e.age};
}
