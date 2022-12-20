void printf(char* s, int d);

int rotateLeft(int num, int rotation){
    int INT_BITS = 4 * 8 - 1;
    rotation %= INT_BITS;

    while(rotation--)
        num = (num << 1) | (1 & (num >> INT_BITS));

    return num;
}

int rotateRight(int num, int rotation){
    int INT_BITS = 4 * 8 - 1;
    rotation %= INT_BITS;

    while(rotation--)
        num = ((num >> 1) & (~(1 << INT_BITS)) | ((num & 1) << INT_BITS));

    return num;
}

int main(){
  int num = -15;
  int rotation = 2;

  printf("left: %d\n", rotateLeft(num,rotation));
  printf("right: %d\n", rotateRight(num,rotation));
}
