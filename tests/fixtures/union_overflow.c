void printf(char* f, char* d);

int main(){
  // doesn't overflow when using designators
  union {int age; char* s;} a = {2, .s= "uwe"};

  union {
    char s[3];
    int age;
  } b = {'u', 'w', 'e', 2};

  printf("%s\n",a.s);
}
