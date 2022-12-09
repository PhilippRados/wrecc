void printf(char* s, int d);
int* malloc(int d);

int f(int x, int *py, int **ppz){
  int y;
  int z;

  **ppz += 1; 
   z  = **ppz;
  *py += 2;
   y = *py;
   x += 3;

   return x + y + z;
}

int main(){ 
  // array increments
  int b[2];
  b[0] = 2;
  b[1] = 5;

  printf("%d\n", ++b[0]);
  printf("%d\n", --b[0]);

  printf("%d\n", b[1]++);
  printf("%d\n", b[1]);

  printf("%d\n", b[1]--);
  printf("%d\n", b[1]);


  // pointer increments
  int i;
  int *ptr = malloc(5 * 4);

  for (i=0; i<5; i++){
      *(ptr + i) = i;
      printf("i:%d\n",i);
  }

  for (i -= 1; i>0; i--){
      printf("p:%d\n",ptr[i]);
  }

  printf("%d\n", *ptr++);
  printf("%d\n", (*ptr)++);
  printf("%d\n", *ptr);
  printf("%d\n", *++ptr);
  printf("%d\n", ++*ptr);
  printf("%d\n", --*ptr);

  // complex function call
  int c = 4;
  int *z;
  int **a;

  z = &c;
  a = &z; 
  printf("%d\n", f(c,z,a)); // 19

  // iterating over pointer with increments
  char* s = "some text";
  for (char* p = s; *p != 0; p++){
    printf("%d ", *p);
  }
}
