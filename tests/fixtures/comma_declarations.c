int *q, p, printf(char* s, int d), s = 4;
int strlen(char* s);

int main(){
  p = 2;
  q = &p;

  printf("%d\n",p);
  printf("%d\n",*q);
  printf("%d\n",s);

  struct some {
    struct some* self;
    char* name;
  } s = {.self = ((void *)0),.name = "foo"},*sp;

  for (int i = 0; i < strlen(s.name); i++) {
    printf("%d\n",s.name[i]);
  }

  sp = &s;
  sp->name = "barz";
          
  for (int i = 0; i < strlen(s.name); i++) {
    printf("%d\n",s.name[i]);
  }
}
