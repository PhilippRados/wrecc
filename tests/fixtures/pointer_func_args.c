void printf(char* format, int input);
void some(int* a) { *a = 3; }

int main() {
  int a = 2;
  some(&a);

  printf("%d\n",a);
}
