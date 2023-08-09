int printf(char* s, int d);

int main() {
  struct d *a[4];
  int e = 2;

  printf("%d\n",*(&*a)[!-e]->outer);
}
