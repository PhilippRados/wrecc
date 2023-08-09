void printf(char* s,int d);

int main() {
  int d = 0;
  do {
      printf("%d\n",d);
  } while (d != 0);

   while (d != 0) {
      printf("%d\n",d);
  }
  for (int d = 0;;){
    do {
      d++;
      if (d % 2) {
        continue;
      } else {
          d *= 3;
      }

      while (d < 10){
          printf("%d\n",d);
          d += 1;
      }
      printf("%d\n",d);
    } while (d < 3);
    break;
  }
}
