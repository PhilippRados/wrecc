void printf(char* s, int d,int d2);

void send(char* to, char* from, int count) {
  int n = (count + 7) / 8;
  switch (count % 8) {
  case 0:
    do {
      *to++ = *from++;
    case 7:
      *to++ = *from++;
    case 6:
      *to++ = *from++;
    case 5:
      *to++ = *from++;
    case 4:
      *to++ = *from++;
    case 3:
      *to++ = *from++;
    case 2:
      *to++ = *from++;
    case 1:
      *to++ = *from++;
    } while (--n > 0);
  }
}

int main() {
  char input[10] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j'};
  char output[10];
  send(output, input, 10);

  for (int i = 0; i < 10; i++) {
    printf("%d, %d\n", input[i], output[i]);
  }
}
