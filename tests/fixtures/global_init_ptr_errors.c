int printf(char* s, int d);

int *arr;
int *array_element_addr = &*(arr + 3);
int *arr_offset_neg = arr - 1;
int *arr_offset_neg_nested = &((arr + 2)[-1]);

int **array_ref_grouping = (int**)&(arr);

int *array_element_indirection = &*&arr[2];

int *multi_arr[2];
int *multi_arr_first = *multi_arr;

int main() {
}
