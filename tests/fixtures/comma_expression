int printf(char* s, int d);

int f(int a, int b, int c) {
  return b;
}

int main(){
  int a = 6;
  int x = 1, y = 2, z = f(x,(a=2, a=3), 9);
  int result = (x++, y++, z++, ++x + y + z + 1);


  printf("x:%d\n", x);
  printf("y:%d\n", y);
  printf("z:%d\n", z);
  printf("result:%d\n", result);
}
