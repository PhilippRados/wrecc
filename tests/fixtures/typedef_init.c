#include <stdio.h>

typedef struct {
  int k;
  int l;
  int a[2];
} T;

typedef struct {
  int i;
  T t;
} S;
T x = {.l = 43, .k = 42, .a[1] = 19, .a[0] = 18};
// x initialized to {42, 43, {18, 19} }

int main(void) {
  printf("%d\n", x.k);
  printf("%d\n", x.l);
  printf("%d\n", x.a[0]);
  printf("%d\n", x.a[1]);

  S l = {
      .i = 1,      // initializes l.i to 1
      .t = x,      // initializes l.t to {42, 43, {18, 19} }
      .t.l = 41,   // changes l.t to {42, 41, {18, 19} }
      .t.a[1] = 17 // changes l.t to {42, 41, {18, 17} }
  };
  printf("%d\n", l.i);
  printf("%d\n", l.t.k);
  printf("%d\n", l.t.l);
  printf("%d\n", l.t.a[0]);
  printf("%d", l.t.a[1]);
}
