void printf(char* s, char* c);

int main() {
  char* c[4];
  c[0] = "GeksQuiz";
  c[1] = "MCQ";
  c[2] = "TEST";
  c[3] = "QUIZ";

  char** cp[4];
  cp[0] = c + 3;
  cp[1] = c + 2;
  cp[2] = c + 1;
  cp[3] = c;

  char*** cpp = cp;

  printf("%s ", **++cpp);
  printf("%s ", *--*++cpp + 3);
  printf("%s ", *cpp[-2] + 3);
  printf("%s\n", cpp[-1][-1] + 1);
}
