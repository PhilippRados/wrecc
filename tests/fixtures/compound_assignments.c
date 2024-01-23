int printf(char* s, int d);

int *foo(int *a) {
  printf("here\n",0);
  return a;
}

int main(){ 
  for (int i = 2; i < 20; i *= 2) {
      printf("%d\n",i);
  }

  int a = -2;
  a += 3 - 2;
  printf("%d\n",a);

  *foo(&a) += 2;
  printf("%d\n",a);

  long b = -2;
  b = -2 / -2;
  printf("%d\n",b);

  int c = 10;
  c -= 3 * 2;
  printf("%d\n",c);
}
