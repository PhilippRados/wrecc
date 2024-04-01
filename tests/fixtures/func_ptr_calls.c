#include <stdio.h>
void fun(int a) { printf("Value of a is %d\n", a); }

int main() {
  void (*fun_ptr1)(int) = &fun;
  void (**fun_ptr2)(int) = &fun_ptr1;
  void (***fun_ptr)(int) = &fun_ptr2;

  (******fun_ptr)(5);
  (*fun_ptr1)(10);
  fun_ptr1(15);

  return 0;
}
