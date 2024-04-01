<div>
  <p align="left">
    <img src="https://i.ibb.co/1bfxpbb/wreckage-mj.jpg" width="800">
  </p>
</div>

[![Test](https://github.com/PhilippRados/wrecc/actions/workflows/test.yml/badge.svg)](https://github.com/PhilippRados/wrecc/actions/workflows/test.yml)
![](https://img.shields.io/github/license/PhilippRados/wrecc)
![](https://img.shields.io/badge/made_for-UNIX-lightgrey)
![](https://img.shields.io/badge/Architecture-x86--64-blue)

Wrecc is a x86-64 C99 compiler written from scratch. The name is a play on the word `wreck` which describes a rusting ship on the sea floor. 

### Table of contents
* [Installation](#installation)
  + [Pre-built binaries](#binaries)
  + [Cargo](#cargo)
* [Features](#features)
  + [Preprocessor](#preprocessor)
  + [Compiler](#compiler)
    + [Supported keywords](#keywords)
    + [Ast pretty-printer](#ast)
    + [Error messages](#errors)
* [Testing](#testing)
  + [Unit-tests](#unit)
  + [Snapshot-tests](#snap)
  + [Fuzzer](#fuzzer)
* [Contribution](#contribution)
* [Agenda](#agenda)
* [Ressources](#ressources)


## Installation
The compiler emits [x86-64](https://en.wikipedia.org/wiki/X86-64) assembly in [AT&T syntax](https://staffwww.fullcoll.edu/aclifton/courses/cs241/syntax.html), it adheres to the [System V ABI](https://wiki.osdev.org/System_V_ABI) which I could only test for Ubuntu and Macos.
### Pre-built binaries <a name="binaries"></a>
If you don't have the rust toolchain installed on your system you can install the latest binary from the releases directly:
```
curl ...
```
### Cargo
Otherwise you can just use:
```
cargo install wrecc
```

## Features
Since not all keywords are currently implemented wrecc uses [custom headers](https://github.com/PhilippRados/wrecc/tree/master/include) which are built directly into the binary
### Preprocessor
The preprocessor implements all [C99 preprocessor directives](https://en.cppreference.com/w/c/keyword), except `#line`, `#error` and `#pragma`. Most prominently it currently also misses function-like macros which are on the agenda though.

#### Compiler
#### Supported Keywords <a name="keywords"></a>
<img width="487" alt="keywords" src="https://github.com/PhilippRados/wrecc/assets/60818062/b738b6e0-9ca3-4a8d-9a5a-e1a6da0c31ed">

Weird but working C code
```C
#include <stdio.h>

typedef struct {
  int (*print_func)(char*,...);
  char str[2 * 3];  
} PrintableString;

PrintableString s = {.print_func = printf, .str[3] = 's'};

int main() {

}
```

#### Unimplemented Features <a name="unimplemented"></a>
Aside from the missing keywords these are the main missing features:
- Arrays with unspecified size
- Raw structs/unions as function argument-/return-types
- Floating point types
Here is a list of all the stuff still missing: [todo](https://placid-eris-c19.notion.site/check-all-errors-from-c-testsuite-6f3fa2a3c24a4711b5e89f45354db540)

#### Error messages <a name="errors"></a>
Wrecc also has nice looking messages. Error reporting also doesn't stop after the first error. Using the `--no-color` option you can switch off color-highlighting in errors.


#### Ast pretty-printer <a name="ast"></a>

##### Inspect all options by running `wrecc --help`

## Testing
### Unit tests <a name="unit"></a>
```
cargo t --all
```
### Snapshot testing <a name="snap"></a>
This runs all [fixtures]() and compares them to the expected [snapshot]()
```
bash tests/snapshot_tests.sh
```
### Fuzzer
Runs the fuzzer using [afl.rs](https://github.com/rust-fuzz/afl.rs)
```
// in fuzzer directory
cargo afl build
cargo afl fuzz -i inputs -o outputs target/debug/fuzz_target
```

### Contribution
If you want to help me with this compiler I would really welcome it. The easiest place to start is probably by implementing one of the missing keywords/types mentioned in the [unimplemented features](#unimplemented) section. Make sure all tests still pass and implement your own if it's something new that is not already being tested.

### Agenda
Overall goals include:
- Not relying on custom headers
- Passing all C99 tests in [c-testsuite](https://github.com/c-testsuite/c-testsuite)
- Compiling multiple files at once

### Ressources
The following ressources helped me in building this compiler:
- [Crafting Interpreters](https://craftinginterpreters.com/)
- Engineering a Compiler (Book)
- [acwj](https://github.com/DoctorWkt/acwj)
- [saltwater](https://github.com/jyn514/saltwater)
- [chibicc](https://github.com/rui314/chibicc)

