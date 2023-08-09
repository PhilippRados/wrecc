//void printf(char* s, int d);

//int main(){
//    int x = 3;
//    int y = 1;
//    int sum;
//    int carry;
//
//    sum = x ^ y; // x XOR y
//    carry = x & y; // x AND y
//
//    while (carry != 0) {
//        carry = carry << 1; // left shift the carry
//        x = sum; // initialize x as sum
//        y = carry; // initialize y as carry
//        sum = x ^ y; // sum is calculated
//        carry = x & y;
//    }
//
//    printf("%d","%u\n", sum); // the program will print 4
//}

void printf(char* s, int d);
int putchar(int c);

char* str;
int   x;

int main() {
  x= -23;
  printf("%d\n",x);
  printf("%d\n",-10 * -10);

  x= 1; x= ~x; printf("%d\n",x);

  x= 2 > 5; printf("%d\n",x);
  x= !x; printf("%d\n",x);
  x= !x; printf("%d\n",x);

  x= 13; if (x) { printf("%d\n",13); }
  x= 0; if (!x) { printf("%d\n",14); }

  for (str= "Hello world\n"; *str; str++) {
    putchar(*str);
  }
}
