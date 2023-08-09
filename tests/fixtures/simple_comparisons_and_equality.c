void printf(char* format, int digit);

int main(){
  printf("%d\n",3 != 2);
  printf("%d\n",2 == 2);
  printf("%d\n",3 != 3);

  int a = 10;
  int b = 0;

  printf("%d\n",a < b);
  printf("%d\n",b <= a);

  a = 0;
  b = 2;
  printf("%d\n",a > b);

  a = 2;
  printf("%d\n",a >= b);
}
