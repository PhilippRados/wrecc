void printf(char* s,char* o,char* o2);

char* other(char*s ){return s;}
char* other2(char*s ){return s;}

int main(){
  printf("some: %s, %s\n",other("uwe1"),other2("uwe2"));
}
