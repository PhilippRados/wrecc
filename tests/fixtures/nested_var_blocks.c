void printf(char* format, int input);

int main(){
  int a = 1;
  int b = 2;
  int c = 3;
  {
    int a = 4;
    int b = 5;
    {
      int a = 6;
      printf("%d\n",a);
      printf("%d\n",b);
      printf("%d\n",c);
    }
    printf("%d\n",a);
    printf("%d\n",b);
    printf("%d\n",c);
  }
  printf("%d\n",a);
  printf("%d\n",b);
  printf("%d\n",c);
}
