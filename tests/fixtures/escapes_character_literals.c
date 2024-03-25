#include <stdio.h>

int main() {

  char c0 = '\0';
  char d = '\\';

  printf("%d\n", c0);
  printf("%c\n", d);

  char s0[12] = "some\nthing";
  char s1[14] = "some\\nthing";
  printf("%d\n", s0[4]);
  printf("%s\n", s0);
  printf("%s\n", s1);
  printf("%d\n", s1[4]);
  printf("%d\n", s1[5]);

  char c = '\'';
  char c2 = '\"';
  char c3 = '"';
  char *s = "s   \"   more";
  char *s2 = "hello\0ignore";

  printf("%c\n", c);
  printf("%c\n", c2);
  printf("%c\n", c3);
  printf("%s\n", s);
  printf("%s", s2);
}
