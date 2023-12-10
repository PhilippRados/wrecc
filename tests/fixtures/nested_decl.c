#include <stdio.h>

;
;

int main() {
  char arr[4][2] = {{1, 2}, {2, 2}, 3}, (*p)[4], *q;

  char *arr_of4_ptrs[4] = {"hello", "there"}; // fine
  ;

  int typedef Number;
  int long typedef BigNumber;

  char a[4] = "hei";
  char(*ptr_to_arr_of4_also)[4] = &a;

  int(((z))) = 4;

  long int long hallo;

  long typedef *some, foo, bar;

  char *(arr_of2_arr4_ptr[2])[4] = {{"one", "two", "thre"}, {[3] = "last"}};

  some ptr = (void *)1;
  foo other = 1;

  printf("%s\n", arr_of4_ptrs[1]);
  printf("%s\n", *ptr_to_arr_of4_also);
  printf("%d\n", z);
  printf("%s,%s\n", arr_of2_arr4_ptr[0][1], arr_of2_arr4_ptr[1][3]);
  printf("%p\n", ptr);
  printf("%lu\n", other);
}
