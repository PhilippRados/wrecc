void* printf(char* f, long d);
int strlen(char* s);
void* malloc(int d);


// Define a new enum
enum Color {
    RED,
    GREEN,
    BLUE
};

// Define a new struct
struct Point {
    int x;
    int y;
};

// Define a new union
union Number {
    int i;
    char f;
};

int main() {
    // Declare variables of different types
    int x = 10;
    enum Color color = GREEN;
    struct Point point = {3, 4};
    union Number num = {.f = 'd'};

    // Cast uint to int
    int y = (int)x;

    // Cast enum to int
    int color_int = (int)color;

    // Cast struct to void pointer
    void *ptr = (void *)&point;

    // Cast union to int
    int num_int = (int)num.i;

    // Print the values of the casted variables
    printf("Value of x: %d\n", y);
    printf("Value of color: %d\n", color_int);
    printf("Value of point: %d\n", ((struct Point *)ptr)->x);
    printf("Value of point: %d\n", ((struct Point *)ptr)->y);
    printf("Value of num: %d\n", num_int);

    int a = 3;

    struct other {
      int age;
    } b2 = *(struct other*)&a;

    printf("%ld\n", b2.age);

    int c[2] = {2,1};
    int d = *(int*)(void*)c;

    printf("%ld\n", d);

    {
      int a = 128;
      int b = (char)(int)a;

      printf("%d\n", b);

      int c = (1 + 4);
      void* d = &c;

      printf("%ld\n", *(int*)d);

      char p = 'A';
      int i = p;
      long l = 1234567890;
      void* ptr;

      ptr = (void*)&p;
      printf("Value of c: %ld\n", *((char*)ptr)); // cast void pointer back to char pointer

      ptr = (void*)&i;
      printf("Value of i: %ld\n", *((int*)ptr)); // cast void pointer back to int pointer

      ptr = (void*)&l;
      printf("Value of l: %ld\n", *((long*)ptr)); // cast void pointer back to long pointer
    }
}
