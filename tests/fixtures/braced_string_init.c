
int main(void) {
  // both are the same
  char s[7] = "hello";
  char e[7] = {"hello"};

  char g[7] = {{"hello"}};
  char j[7] = {{{"hello"}}};

  // should be char-array overflow
  char p[7] = {"zwe", "test"};
  char m[7] = {"zwe", [0] = 1};

  struct Foo {
    char c;
    char s[4];
  } l = {{1}, {[2] = "foo"}};

  struct Foo d = {.s[0] = "foo"};

  struct Foo o = {.s = {"foo"}};
}
