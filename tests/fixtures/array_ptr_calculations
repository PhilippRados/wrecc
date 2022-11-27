void printf(char* s, int digit);

int calc_sum(int arr[10],int n){
  int result = 0;
  for(int i=0; i < n; i = i + 1) {
    result = result + *(arr + i);
  }
  return result;
}
int main() {
  int marks[10];
  int i = 0;
  int n = 10;
  int sum = 0;
  int average;

  for(i=0; i < n; i = i + 1) {
    *(marks + i) = i + 1;
  }
  sum = calc_sum(marks,n);

  average = sum / n;
  printf("%d\n",sum);
  printf("%d\n",n);

  printf("%d\n",average);
}
