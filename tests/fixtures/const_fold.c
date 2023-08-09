int printf(char* s, int d);

int call();

enum Some { first = 10};
int a[first - 8] = {1 * first, 3 - 2};
int b[1 || call()];

int main() {
  printf("%d\n",sizeof(b));
  for (int i = 0; i < (first - 8); i++){
    printf("%d\n", a[i]);
  }
}
