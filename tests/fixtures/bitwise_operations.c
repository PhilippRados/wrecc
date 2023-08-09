void printf(char* s, int d);

int main(){
  long a = 24;
  int b = 3;

  printf("%d\n", a & b);
  printf("%d\n", a | b);
  printf("%d\n", a ^ b);

  b |= 4;
  printf("%d\n",b);

  a ^= -4;
  printf("%d\n",a);

  a &= a - b;
  printf("%d\n",a);
}
