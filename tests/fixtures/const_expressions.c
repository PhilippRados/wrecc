int printf(char *s, int d);

enum Some { A = -1, B = -4 * 2, C };

int main() {
  int a['=' + 2] = {1, 2, 3, 4, [5 * 2] = 10};
  a[3] = 378912;
  int size = sizeof(a) / sizeof(a[0]);
  printf("%d\n", size);

  for (int i = 0; i < size; i++) {
    printf("%d\n", a[i]);
  }

  enum Some state = B;
  switch (state) {
  case -4 * 2: {
    printf("in case B = %d\n", B);
    break;
  }
  default: {
    printf("Nothing", 0);
  }
  }
}
