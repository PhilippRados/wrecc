<div>
  <p align="left">
    <img src="https://i.ibb.co/1bfxpbb/wreckage-mj.jpg" width="800">
  </p>
</div>

[![Test](https://github.com/PhilippRados/wrecc/actions/workflows/test.yml/badge.svg)](https://github.com/PhilippRados/wrecc/actions/workflows/test.yml)
![](https://img.shields.io/github/license/PhilippRados/wrecc)
![](https://img.shields.io/badge/made_for-UNIX-lightgrey)
![](https://img.shields.io/badge/Architecture-x86--64-blue)

`wrecc` is a small,lean x86-64 C99 compiler written from scratch. The name is a play on the word _wreck_ which describes a rusting ship on the sea floor. 
The compiler emits [x86-64](https://en.wikipedia.org/wiki/X86-64) assembly in [AT&T syntax](https://staffwww.fullcoll.edu/aclifton/courses/cs241/syntax.html), it adheres to the [System V ABI](https://wiki.osdev.org/System_V_ABI) which I could only test for Ubuntu and Macos. There are no dependencies you only need your assembler and linker which the compiler then invokes to create the final binary.

### Table of contents
* [Installation](#installation)
  + [Pre-built binaries](#binaries)
  + [Cargo](#cargo)
* [Features](#features)
  + [Preprocessor](#preprocessor)
  + [Compiler](#compiler)
    + [Supported keywords](#keywords)
    + [Unimplemented features](#unimplemented)
  + [Error messages](#errors)
  + [Ast pretty-printer](#ast)
* [Testing](#testing)
* [Troubleshooting](#troubleshooting) 
* [Contribution](#contribution)
* [Project goals](#goals)
* [Resources](#resources)


## Installation
### Pre-built binaries <a name="binaries"></a>
If you don't have the rust toolchain installed on your system you can install the latest binary (MacOs, Linux) from the releases directly:
```
curl --proto '=https' --tlsv1.2 -LsSf https://github.com/PhilippRados/wrecc/releases/download/v0.2.0/wrecc-installer.sh | sh
```
### Cargo
Using `cargo binstall`
```
cargo binstall wrecc
```
or building from source
```
cargo install wrecc
```

## Features
Since not all keywords are currently implemented wrecc uses [custom standard-headers](https://github.com/PhilippRados/wrecc/tree/master/include) which are built directly into the binary
### Preprocessor
The preprocessor implements all [C99 preprocessor directives](https://en.cppreference.com/w/c/keyword), except `#line` and `#pragma`. Most prominently it currently also misses function-like macros which are on the agenda though.

### Compiler
#### Supported Keywords <a name="keywords"></a>
<img width="481" alt="keywords" src="https://github.com/PhilippRados/wrecc/assets/60818062/492cdf56-ee83-4333-9084-02fcd8a08356">

#### Other than that it even supports:
<details>
  <summary>Aggregate initialization with designated initializers</summary>
  
  ```C
  struct {
    union {
      int foo;
      long baz;
    } nested;
    int array[16];
  } bar = { .nested.foo = 3, .array[6] = 1};
  ```

</details>
<details>
  <summary>Function pointers</summary>

  ```C
  #include <stdio.h>
  
  typedef int (*BinaryOperation)(int, int);
  typedef struct {
    BinaryOperation add;
    BinaryOperation subtract;
  } Calculator;
  
  int add(int a, int b) { return a + b; }
  int subtract(int a, int b) { return a - b; }
  
  int main() {
    Calculator calc = {add, subtract};
  
    printf("Result of addition: %d\n", calc.add(10, 5));
    printf("Result of subtraction: %d\n", calc.subtract(10, 5));
  }

  ```

</details>
<details>
  <summary>Constant folding</summary>
  
  ```C
  char **string_offset = (char **)&"hello" + (int)(3 * 1);
  int array[(long)3 * 2 - 1];
  ```

</details>

#### Unimplemented Features <a name="unimplemented"></a>
Aside from the missing keywords these are the main missing features:
- [x] Arrays with unspecified size
- [x] Compiling multiple files at once
- [ ] Raw structs/unions as function argument-/return-types
- [ ] Floating point types<br>

Here is a list of all the stuff still missing: [todo](https://placid-eris-c19.notion.site/check-all-errors-from-c-testsuite-6f3fa2a3c24a4711b5e89f45354db540?pvs=4)

### Error messages <a name="errors"></a>
Wrecc also has nice looking messages. Error reporting doesn't stop after the first error. Using the `--no-color` option you can switch off color-highlighting in errors. Currently there are only errors and no warnings.
<table>
  <tr>
    <th>C code</th>
    <th>Errors</th>
  </tr>
  <tr>
  <td>
    
  ```C
  int foo(void);
  int main() {
    int a = foo(1);
    long *p = a;
  
    return p * 2;
  }
  ```
  </td>
  <td>
    <img width="535" alt="error" src="https://github.com/PhilippRados/wrecc/assets/60818062/0b0e0c9f-3600-460c-9da5-1705ef0f83d9">
  </td>
</tr>
</table>

### Ast pretty-printer <a name="ast"></a>
When compiling using the `--dump-ast` option it prints the parse-tree
<table>
  <tr>
    <th>C code</th>
    <th>AST</th>
  </tr>
  <tr>
  <td>
    
  ```C
  #define SIZE 16
  void foo(char);
  int main() {
    int arr[SIZE] = {1, 2};
    char p = (char)(*arr + 3);
  
    switch (p) {
    case 'c':
      foo(p);
    }
  }
  ```
  </td>
  <td>
  
  ```
  Declaration:
  -Decl: 'foo'
  FuncDef: 'main'
  -Declaration:
  --Init: 'arr'
  ---Aggregate:
  ----Scalar:
  -----Literal: 1
  ----Scalar:
  -----Literal: 2
  -Declaration:
  --Init: 'p'
  ---Scalar:
  ----Cast: 'char'
  -----Grouping:
  ------Binary: '+'
  -------Unary: '*'
  --------Ident: 'arr'
  -------Literal: 3
  -Switch:
  --Ident: 'p'
  --Block:
  ---Case:
  ----Literal: 99
  ----Expr:
  -----FuncCall:
  ------Ident: 'foo'
  ------Ident: 'p'
```
</td>
</tr>
</table>

#### Inspect all options by running `wrecc --help`

## Testing
Run different types of tests with `make <target>`. Available targets can be inspected using `make help` as shown below.
```console
$ make help
Usage:
  make <target>
  help             Display this help
  unit-tests       Run rust unit-tests
  snapshot-tests   Run snapshot-tests located in tests/
  c-testsuite      Requires c-testsuite (https://github.com/c-testsuite/c-testsuite) and env-var C_TESTSUITE set to its path
  fuzzer           Launch afl.rs fuzzer
```

## Troubleshooting
Reasons for `wrecc` not working properly on your machine:
- Unsupported architecture/OS
- Cannot find libc in standard library search paths (can be fixed by passing custom search path using `-L <path>` option)
- If it's not mentioned in the [unimplemented features](#unimplemented) section then please raise an issue

## Contribution
If you want to help me with this compiler I would really welcome it. The easiest place to start is probably by implementing one of the missing keywords/types mentioned in the [unimplemented features](#unimplemented) section. Make sure all tests still pass and implement your own if it's something new that is not already being tested.<br>
Have a look at the [documentation](https://docs.rs/wrecc_compiler/latest/wrecc_compiler/) to get a high level overview of the compiler pipeline.

## Project goals <a name="goals"></a>
- Not relying on custom headers
- Passing all C99 tests in [c-testsuite](https://github.com/c-testsuite/c-testsuite)
- Compiling real-world C projects like [Git](https://github.com/git/git/tree/master)

## Resources
The following resources helped me in building this compiler:
- [Crafting Interpreters](https://craftinginterpreters.com/)
- Engineering a Compiler (Book)
- [acwj](https://github.com/DoctorWkt/acwj)
- [saltwater](https://github.com/jyn514/saltwater)
- [chibicc](https://github.com/rui314/chibicc)

