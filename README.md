# RoccaC

A weird programming language, because why not

## Description
Rocca is one of my small personal projects, it is a compiled, statically typed programming language which compiles to it's own custom bytecode and is executed in it's own VM.

Rocca's syntax is heavily inspired :tm: by Rust.

## Project status
### Implemented
- [x] If/ElseIf/Else statements and While loops
- [x] Int, Bool, Unit and String data types
- [x] Local variables with mutability specifiers
- [x] Function definitions with optional return types
- [x] Immutable and mutable references and passing by reference
- [x] Native function interface (currently only `print()` is available)
- [x] Chained comparison (`0 < a < 10`)
- [x] Disassembler for bytecode
- [x] Proper scoped variable tracking
- [x] Basic borrow checker
- [x] Heap allocations

### Being worked on
- [ ] Custom data types (structs and enums)
- [ ] Extended native function interface

### Planned
- [ ] Support for C types and FFI
- [ ] Standard library

## Example
```rs
fn main() {
  print("Hello, World!\n");

  print("1 + 2 is:", add(1,2), "\n");

  let mut a = 5;
  modify(&mut a);

  print("a is now:", a, "\n");
}

fn add(a: Int, b: Int) -> Int {
  return a + b;
}

fn modify(a: &mut Int) {
  *a = 10;
}
```
