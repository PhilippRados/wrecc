#define uwe test
#define simon uwe
#define siggi simon; uwe

#define foo1 bar
#define bar foo2

int main() {
  foo1;
  siggi;
}
// preprocessor generates:
// int main(){
//   foo2;
//   test; test;
// }
