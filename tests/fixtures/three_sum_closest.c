void printf(char* s, char d);
int abs(int x);

int threeSumClosest(int* nums,int size, int target) {
    int close=1000000000;

    for(int i=0;i<size-2;i++) {
        int p1=i+1;
        int p2=size-1;
        while(p1<p2) {
            int sum = nums[i] + nums[p1] + nums[p2];
            if (abs(target - sum) < abs(target - close)) {
              close = sum;
            }
            if(sum>target) {
                p2--;
            } else {
                p1++;
            }
         }
    }
    return close;
}

int main() {
  int nums[4];
  nums[0] = -4;
  nums[1] = -1;
  nums[2] = 1;
  nums[3] = 2;

  int target = 1;

  printf("output: %d\n",threeSumClosest(nums,4,target));
}
