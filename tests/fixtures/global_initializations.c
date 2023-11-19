#include <stdio.h>

char *str[2] = {"te", "uwe"};
char **e[1] = {str};

char d[3] = "se";
char *t = d;

int c = 100;
int *k = &c;

int main() {
  putchar(c);
  putchar(*k);

  printf("%s\n", str[1]);
  printf("%s\n", **e);
  printf("%s\n", t);

  struct fred {
    char s[4];
    int n;
  };
  struct fred x[1] = {
      {{"abc"}, 1},  // inits x[0] to { {'a','b','c','\0'}, 1 }
      [0].s[0] = 'q' // changes x[0] to { {'q','b','c','\0'}, 1 }
  };
  struct fred y[1] = {
      {{"abc"}, 1}, // inits y[0] to { {'a','b','c','\0'}, 1 }
      [0] =
          {             // current object is now the entire y[0] object
           .s[0] = 'q'} // replaces y[0] with { {'q','\0','\0','\0'}, 0 }
  };

  for (int i = 0; i < 1; i++) {
    printf("%s, %d\n", x[i].s, x[i].n);
    printf("%s, %d\n", y[i].s, y[i].n);
  }
}
