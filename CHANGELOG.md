# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.2.0 - (2024-04-19)

### Added

- Support for arrays with unspecified size (`int array[] = {1,2,3}`)
- Capability to compile multiple files at once (`wrecc foo.c bar.c -o cool_file`)
- Implemented all storage-class-specifiers (`extern`, `static` etc.)
- Changelog (inception)

### Fixed

- Nested switch-statements caused panic
- Can handle dos-style carriage return (`'\r\n'`)
- Cast-expression rvalue bug

## 0.1.0 - (2024-04-03)

- Initial release
