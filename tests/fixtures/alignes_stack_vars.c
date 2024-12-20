int **malloc(int size);
void printf(char *s, int digit);

int main() {
  int c;
  int **a = malloc(8);
  int b = 3;
  *a = &c;

  *(*a) = b;

  printf("%d\n", *(*a));
  printf("%d\n", c);
}
