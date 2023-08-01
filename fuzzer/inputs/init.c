struct Some {
  int age;
  struct Some *self;
} e = {.age = 12, (void *)0};

union Other {
  struct More {
    int arr[3];
  } a;
  long b;
};

int main() {
  typedef union Other other_un;

  other_un container = {.b = e.age};
}
