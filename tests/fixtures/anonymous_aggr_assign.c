int main(void) {
  typedef struct {
    int age;
  } A;

  A a;
  A b = a;

  typedef struct {
    int age;
  } B;

  B c;
  A d = c;

  union {
    int age;
  } e;
  struct {
    int age;
  } f = e;
}
