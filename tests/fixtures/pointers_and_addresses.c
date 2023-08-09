void printf(char* format, int input);

int main() {
  char **b;
  char a;
  int d;
  int *e;
  int f;

  a = 18; 
  char* ptr_a = &a;
  b = &ptr_a; 
  char c = **b; 

  printf("%d\n",c);

  d= 12; printf("%d\n",d);
  e= &d; f= *e; printf("%d\n",f);
  return(0);
}
