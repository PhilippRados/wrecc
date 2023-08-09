int printf(char* s, long d);

int long_function(int a, long b, char c) {
  printf("%ld\n", a);
  printf("%ld\n", b);
  printf("%ld\n", c);

  return a + b + c;
}

int main() {
  long z = 1;
  int r = 1;
  int a = long_function(r << 31, z << 63, 128);
  int b = long_function(z << 31, r << 63, 128);

  printf("%ld\n", a);
  printf("%ld\n", b);
}
