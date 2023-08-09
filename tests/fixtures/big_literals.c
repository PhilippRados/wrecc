int printf(char* s, long d);

int main(){
  long d = -2147483690;
  printf("%ld\n", d);

  long lo = 2147483648;
  printf("%ld", lo);
}
