void printf(char *format, int input);

int main() {
  {
    int some() {
      printf("%d\n",1);
    }
    // WARN: this should be displayed as undeclared error
    some();
  }
}
