#define BAR <stdio.h>

#define FOO BAR
#include FOO

#define BAZ "../mock_headers/foo"
#include BAZ

int main() { printf("%d", random_num); }
