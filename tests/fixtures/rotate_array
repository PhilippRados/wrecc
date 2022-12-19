void printf(char* s, int d);

void invertArray(int *array, int start, int end){
    while(start < end){
        int tmp = array[start];
        array[start++] = array[end];
        array[end--] = tmp;
    }
}

void rotate(int* nums, int numsSize, int k){
    if(numsSize < 2){
        return;
    }
    k = k % numsSize;
    
    invertArray(nums,0,numsSize-1);
    invertArray(nums,0,k-1);
    invertArray(nums,k,numsSize-1);       
}

int main(){
  int nums[7] = {1,2,3,4,5,6,7};
  int k = 3;

  rotate(nums,7,k);
  for(int i = 0; i < 7; i++){
    printf("%d\n", nums[i]);
  }

  int nums2[4] = {-1,-100,3,99};
  int k2 = 2;

  rotate(nums2,4,k2);
  for(int i = 0; i < 4; i++){
    printf("%d\n", nums2[i]);
  }
}
