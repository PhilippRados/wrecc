void printf(char* s,int d);

int main() {
  int i = 1;
  int j = 1;

  // Simple for loop
  for (int i = 1; i <= 10; i++) {
    if (i == 5) {
      break; // Exit the loop when i is equal to 5
    }
    printf("%d ", i);
  }
  printf("\n%d\n", i);

  // Nested for loop
  for (i = 1; i <= 3; i++) {
    for (j = 1; j <= 3; j++) {
      if (i == 2 && j == 2) {
        continue; // Skip printing "2 2"
      }
      printf("%d ", i);
      printf("%d ", j);
    }
    if (i == 3) {
      break;
    }
  }
  printf("\n%d\n", i);
  printf("\n%d\n", j);

  // While loop
  i = 1;
  while (i <= 10) {
    if (i == 5) {
      break; // Exit the loop when i is equal to 5
    }
    printf("%d ", i);
    i++;
  }
  printf("\n%d\n", i);
  printf("\n%d\n", j);

  // Nested while loop
  i = 1;
  j = 1;
  while (i <= 3) {
    break;
    while (j <= 3) {
      if (i == 2 && j == 2) {
        j++;
        continue; // Skip printing "2 2"
      }
      printf("%d", i);
      printf("%d", j);
      j++;
    }
    i++;
    j = 1; // Reset j for the next iteration of the outer loop
  }

  printf("\n%d\n", i);
  printf("\n%d\n", j);
}
