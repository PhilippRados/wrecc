void printf(char *s, int digit);

int main() {
  char b = 10;
  char *a = &(b);
  printf("%s\n", *a);

  a = &(b + 3);

  int *c = &(int)b;
}
