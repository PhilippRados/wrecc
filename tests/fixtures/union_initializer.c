void printf(char* f,int d,int e);

struct point_t{
    char x;
    long y;
} ;

union some {
    int s;
    long d;
  };

 struct circle_t{
    struct point_t center;
    union some radius;
} ;

 struct triangle_t{
    struct point_t vertices[3];
} ;

 struct rectangle_t{
    struct point_t vertices[4];
} ;

union shape_t{
    struct circle_t circle;
    struct triangle_t triangle;
    struct rectangle_t rectangle;
};

int main() {
    //union shape_t shape = { .circle = { .center = { .x = 1, .y = 2 }, .radius = 3 } };

  union shape_t shape = {.circle = {.center = {.x = 1, .y = 2}, .radius.s = 3}, .circle.radius.d = 5};

    printf("Center: (%d, %d)\n", shape.circle.center.x, shape.circle.center.y);
    printf("Radius: %d, %d\n", shape.circle.radius.s,shape.circle.radius.d);

    return 0;
}
