void printf(char* s,int d);

int main() {
  struct test {
    long some;
    int age;
  } e;
  struct test name;

  name.age = 12;

  e = name;
  
  e.some = 2;

  name.some = e.some;

  printf("%d\n",e.age);
  printf("%d\n",e.some);
  printf("%d\n",name.age);
  printf("%d\n",name.some);
}
