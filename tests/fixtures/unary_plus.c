void printf(char *s, ...);
int main() {
  char c = 'c';

  printf("%c,%d\n", c, sizeof(c));
  printf("%c,%d\n", +c, sizeof(+c));

  printf("%d,%d\n", +'e', sizeof(+'e'));
  printf("%d,%d\n", +-+12322, sizeof(+-+12322));
}
