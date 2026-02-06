Garter Example Programs
=======================

This directory contains example programs demonstrating Garter's features.

Getting Started:
  simple.garter          - Basic syntax: arithmetic, variables, functions, tuples
  strings.garter         - String literals and operations
  pattern_matching.garter - Pattern matching showcase

Data Structures:
  lists.garter           - Linked list operations with pattern matching
  bintree.garter         - Binary tree operations
  mapreduce.garter       - Map, filter, fold operations

Advanced:
  closures.garter        - Closures and higher-order functions
  church.garter          - Church numerals (numbers as functions)
  ycombinator.garter     - Y combinator for anonymous recursion
  recursion_schemes.garter - Advanced recursion patterns
  mutual_recursion.garter - Mutually recursive functions
  match_examples.garter  - Advanced pattern matching examples

Performance Tests:
  tco_test.garter        - Tail call optimization test
  tco_million.garter     - TCO with large iteration count
  gc_test.garter         - Garbage collection test
  simple_gc_test.garter  - Simple GC test

To run an example:
  ./main input/simple.garter | nasm -f macho64 -o out.o /dev/stdin
  clang -arch x86_64 out.o main.c gc.c -o out.run
  ./out.run

Or use make:
  make output/simple.run && ./output/simple.run
