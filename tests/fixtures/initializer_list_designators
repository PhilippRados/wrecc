void printf(char* f,int d, int d2);

struct Emp {
  int age;
  struct {
    long other;
  } some[2];
};

int main() {
  struct Emp arr[3] = {[1].age = 1, [2] = {.age = 1, .some[1].other = 3}, [0] = 2, 3};

  for (int i = 0; i < 3; i++) {
    printf("%d: %d\n", i, arr[i].age);
    printf("%d: %d\n", i, arr[i].some[0].other);
    printf("%d: %d\n\n", i, arr[i].some[1].other);
  }

  int w[4][3][2] = {[3][2][1] = 6, [2][1][1] = 4, 3, 5, 12};
  int x = 0;
  for (int i = 0; i < 4; i++) {
    for (int j = 0; j < 3; j++) {
      for (int k = 0; k < 2; k++) {
        printf("%d: %d\n", x, w[i][j][k]);
        x++;
      }
    }
  }
}
