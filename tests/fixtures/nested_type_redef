int main(){
  typedef union Some u_some;

  union Some {
    int age;
  };

  u_some foo = {.age = 378};

  union Other {
    union Other {
      int a2,rr[3];
    } a;
    long b;
  };
}
