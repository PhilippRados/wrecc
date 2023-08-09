void printf(char* format, int digit);

int main(){
  int a = 0;
  int b = 3;
  int c = 'a';

  int* p = &a - 1;
  int* p2 = &b + 1;
  int* p3 = &a - 2;
  int* p4 = 1 + &c;

  printf("%d\n",*p);
  printf("%d\n",*p2);
  printf("%d\n",*p3);
  printf("%d\n",*p4);
}
