int printf(char* s, int d);

void printNumbers();

int main() {
  int a = 2;

  if (1) {
    for (int i = 0;; i++) {
        printf("%d\n",i);
        if (i == a) {
            goto found;
        }
    }
  } else {
      found: printf("Found it\n",1);
  }

  printNumbers();

  int i = 0;

start:
  if (i > 5) {
    goto end;
  }
  printf("i = %d\n", i);
  i++;

  if (i == 3) {
    goto skip;
  }
  printf("This message will be printed for i = %d\n", i);

skip:
  i++;
  if (i == 5) {
    goto end;
  }
  printf("This message will be skipped for i = %d\n", i);
  goto start;

end:
  printf("Loop ended at i = %d\n", i);
  return 0;
}

void printNumbers(){
    int n = 1;
label:
    printf("%d ", n);
    n++;
    if (n <= 10)
        goto label;
}
