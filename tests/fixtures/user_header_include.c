#include "../mock_headers/foo"
// TODO: change this absolute path test bc its not portable to other machines
#include "/Users/philipprados/Documents/coding/Rust/rucc/tests/mock_headers/foo"
#include <stdio.h>

int main() { printf("%d is defined in %s", num, header_name); }
