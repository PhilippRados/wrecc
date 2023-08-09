void printf(char* s,int d);

int main() {
  int a = 5;
  int i = a > 2 ? 3 : 0;
  int y = 2;
  int z = -2;
  int x = (y > 4) ? 2 * y - 18 : y * z - 3 * a;

  printf("%d\n", i);
  printf("%d\n", x);

  y = 3;

  for (y = 0; y < 10; y++) {
    x = (y < 4) ? y + 2 : (y > 7) ? 1000 : y + 9;
    printf("%d\n", x);
  }
}
