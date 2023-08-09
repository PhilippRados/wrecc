void printf(char *fmt,int d);

union fred {
  char w;
  int  x;
  int  y;
  long z;
};

union fred var1;
union fred *varptr;

int main() {
  var1.x= 65; printf("%d\n", var1.x);
  var1.x= 66; printf("%d\n", var1.x);

  printf("%d\n", var1.y);
  printf("%d\n", var1.w);
  printf("%d\n", var1.z);

  varptr= &var1;
  varptr->x= 67;
  printf("%d\n", varptr->x);
  printf("%d\n", varptr->y);

  return(0);
}
