int a = 's' + (long)1;

int foo(int *ptr) { return *ptr - 3; }

int main() { foo(&a); }
