void printf(char* s, int d);

int main(){
  int a = 3;
  long b = 4;
  char c = 2;

  printf("%d\n", a % b);
  printf("%d\n", b % a);
  printf("%d\n", b % c);

  b %= 5;
  printf("%d\n",b);

  // (a/b) * b + a%b => a
  printf("%d\n",-5 % -3);
}
