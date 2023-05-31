void printf(char* s, long d);

int longest_call(int a, long b, char c,int d, int e, int f, int g, char u, int z) {
  return a + b + c + d + e + f + g - u * z;
}

int long_call(int a, long b, char c,int d, int e, int f, int g, char u) {
  printf("%ld\n", a);
  printf("%lu\n", b);
  printf("%ld\n", c);

  return a + b + c + d + e + f + g + u;
}

int long_call_short(int a, long b, char c,int d, int e, int f, int g) {
  return a + b + c + d + e + f + g;
}

int main() {
  long z = 8;
  long result = longest_call(1,2,3,4,5,6,7,z - 3, z * 2);
  long result2 = long_call_short(1,2,3,4,5,6,7);
  long result3 = long_call(1,2,3,4,5,6,7,z + 2);

  printf("%ld\n", result);
  printf("%ld\n", result2);
  printf("%ld\n", result3);
}
