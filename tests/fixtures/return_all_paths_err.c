void printf(char* format, int digit);

int some(char a){
  if (2 > 1) {
    if (2){
      if (1){
        return 1;
      } else {
        1 + 1; // doesnt return;
      }
    } else {
      return 0;
    }
  } else {
    return 1;
  }
}
int main(){
  printf("%d\n",some(1));
}
