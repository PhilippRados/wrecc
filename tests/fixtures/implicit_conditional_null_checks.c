void printf(char* s,int c);

void copy_string(long* destination, long* source) {
    while(*source) {
        *destination++ = *source++;
    }
    *destination = 0;  // add null terminator to destination string
}

int main() {
  long d[4] = {1,2,3,0};
  long e[4];
  copy_string(e,d);

  for(long* p = e; *p++;){
    printf("%d\n",*p);
  }

  for(long* p = d; *p++;){
    printf("%d\n",*p);
  }
}
