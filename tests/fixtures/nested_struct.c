void printf(char* s,int d);
void strcpy(char* s1,char* s2);

struct Emp {
    int id;
    char name[6];
    struct Date {
      long dd;
      char mm;
      int yyyy;
    } date;
    struct Emp* self;
};

struct Emp* malloc(int d);

int main(){
  struct Emp emp;
  struct Date d;

  emp.id = 101;
  strcpy(emp.name,"hello");

  emp.date.dd = 10;
  emp.date.mm = 5;
  emp.date.yyyy = 2001;
  emp.self = malloc(32);
  emp.self->id = 34;

  d = emp.date;

  printf("%d\n",emp.date.dd);
  printf("%d\n",emp.date.mm);
  printf("%d\n",emp.date.yyyy);
  printf("%d\n",emp.self->id);

  printf("%d\n",d.dd);
  printf("%d\n",d.mm);
  printf("%d\n",d.yyyy);
}
