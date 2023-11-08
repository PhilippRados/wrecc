void printf(char* f,int d);

struct Point {
    int x;
    int y;
};

struct Line {
    struct Point start;
    struct Point end;
};

int main() {
    struct Line lines[2] = {{
        .start =
            {
                .x = -1,
                .y = -1,
            },
        .end =
            {
                .x = 1,
                .y = 1,
            },
    },
    {2, 2, 3, 3},
    [0] = {.end.y = -2}
  };
  for (int i = 0; i < 2; i++) {
    printf("%d\n", lines[i].start.x);
    printf("%d\n", lines[i].start.y);
    printf("%d\n", lines[i].end.x);
    printf("%d\n", lines[i].end.y);
  }
}
