int printf(char *s, int d);

char **string_offset = (char **)&"hello" + (int)(3 * 1);

int *int_literal_pointer_offset1 = (int *)3 + 2;
long *int_literal_pointer_offset2 = (long *)1 + 3;

int arr[4] = {1, 2, 3, 4};
int *array_element_addr = &arr[3];
int *arr_offset_neg = arr - 1;
int *arr_offset_neg_nested = &((arr + 2)[-1]);

int **array_ref_grouping = (int **)&(arr);

long *double_ptr_scale = 2 + (void *)1 + 3;

int *array_element_indirection = &*&arr[2];

struct Some {
  char id;
  int age;
} single_struct = {.id = 34, .age = 100};

void *member_addr = &single_struct.age;

int multi_arr[2][2];
int *multi_arr_first = *multi_arr;

struct Some struct_arr[3] = {1, 2, 3, 4, 5, 6};

void *struct_arr_arrow = &struct_arr->age;
void *struct_arr_index = &struct_arr[2].age;

union Other {
  long *first;
  struct Some sec;
} single_union = {.sec = {1, 2}};

struct Some *s_ptr = &single_union.sec;

char **string_offset_glob = (char **)&"hello" + (9223372036854775805 * 1);

int main() {
  printf("%d\n", (int)int_literal_pointer_offset1);
  printf("%d\n", (int)int_literal_pointer_offset2);
  printf("%d\n", *array_element_addr);
  printf("%d\n", *arr_offset_neg);
  printf("%d\n", *arr_offset_neg_nested);
  printf("%d\n", (int)*array_ref_grouping);
  printf("%d\n", (int)double_ptr_scale);
  printf("%d\n", *array_element_indirection);
  printf("%d\n", *(int *)member_addr);
  printf("%d\n", *multi_arr_first);
  printf("%d\n", *(int *)struct_arr_arrow);
  printf("%d\n", *(int *)struct_arr_index);
  printf("%d\n", s_ptr->id);
  printf("%d\n", s_ptr->age);

  char **string_offset_loc = (char **)&"hello" + (9223372036854775805 * 1);
  printf("%ld\n", (char **)&"hello" - string_offset_loc);
  printf("%ld\n", (char **)&"hello" - string_offset_glob);
}
