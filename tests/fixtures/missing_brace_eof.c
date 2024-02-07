// QUESTION: should error twice saying missing closing brace
// but only does once... why?
int main() {
  {
    { int age = 12; }
