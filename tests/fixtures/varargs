int printf(char* s, ...);
int sprintf(char* s1, char* s2,...);

int main() {
  char a = 'd';
  long z = (long)1 << 36;

  printf("some\n");
  printf("%c,%d,%ld,%s\n",a,a,z,"string");

  char buffer[64];
  sprintf(buffer,"Some complex operations: %d - %ld", 100, z + 100000);

  printf("%s\n",buffer);
}
