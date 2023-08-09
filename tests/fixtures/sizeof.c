int printf(char* s, int d);

int main() {
  int a = 2;
  long x = 3;

  printf("%d\n",sizeof('d' + 'a'));
  printf("%d\n",sizeof(a + x));
  printf("%d\n",sizeof a + x);
  printf("%d\n",sizeof ++a + x);
  printf("%d\n",sizeof(char*[3]));
}
