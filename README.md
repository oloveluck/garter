# Garter

Compiler for the Garter language, targeting x86-64.
Written for the Compilers CS Capstone @ Northeastern University w/ Ben Lerner.

## Building

```bash
make main      # Build compiler
make test      # Build test suite
./test         # Run tests
make lsp       # Build LSP server
make clean     # Clean build artifacts
```

## Usage

```bash
# Compile subcommands
./main program.garter                # Output assembly to stdout
./main compile program.garter        # Same as above
./main build program.garter          # Compile to native executable
./main build -o out program.garter   # Compile with custom output path
./main run program.garter            # Compile and run
./main run program.garter -- arg1    # Compile and run with arguments
```

## Testing

```bash
make test && ./test           # Build and run all tests
make test-verbose             # Run tests with verbose output
make test-one TEST=print3     # Run a single test by name
```

## Language Features

### Values

- **Integers**: 63-bit signed integers with overflow checking
- **Booleans**: `true`, `false`
- **Strings**: `"hello world"`
- **Tuples**: `(1, 2, 3)`
- **Nil**: `nil`

### Arithmetic

- `+`, `-`, `*`, `/`, `%`
- `add1`, `sub1`

### Comparisons

- `<`, `>`, `<=`, `>=`, `==`

### Boolean Operations

- `&&`, `||`, `!`

### Strings

```
let s = "hello" in
print(s)
```

### Tuples

- Creation: `(1, 2, 3)`
- Indexing: `t[0]`
- Mutation: `t[0] := 5`
- Destructuring: `let (a, b) = (1, 2) in a`

### Functions

- Lambda: `lambda(x, y): x + y`
- Definition: `def f(x): x + 1`
- First-class: functions are values, closures capture their environment
- Recursion and mutual recursion supported

### Control Flow

- Let bindings: `let x = 1 in x + 1`
- Recursive let: `let rec f = lambda(n): ... in f(10)`
- Conditionals: `if cond: then_expr else: else_expr`
- Sequences: `expr1; expr2; expr3`

### Pattern Matching

```
def sum(xs):
  match xs:
    | nil => 0
    | (h, t) => h + sum(t)

sum((1, (2, (3, nil))))
```

Patterns support literals, variables, tuples, nil, and wildcards (`_`).

### Mutual Recursion

Functions defined together with `and` can call each other:

```
def even(n):
  if n == 0: true
  else: odd(n - 1)
and def odd(n):
  if n == 0: false
  else: even(n - 1)

even(100)
```

### Runtime Type Checks

- `isnum(x)`, `isbool(x)`, `istuple(x)`

### I/O

- `print(x)` -- prints value and returns it
- `input()` -- reads a number from stdin

### Tail Call Optimization

Functions in tail position reuse the current stack frame:

```
def countdown(n):
  if n == 0: 0
  else: countdown(n - 1)

countdown(1000000)
```

### Garbage Collection

Cheney copying collector implemented in Rust. Triggered automatically when heap space runs low during tuple, closure, or string allocation. Tuples, closures, and strings are all traced and compacted.

### Type Inference

Hindley-Milner type inference runs as an advisory pass. Type errors are reported as warnings but never block compilation, so programs always compile and run.

The type system supports integers, booleans, strings, nil, tuples, lists, arrow types, and parametric polymorphism. It detects:

- Type mismatches in operators, conditionals, and function calls
- Infinite types (occurs check)
- Non-exhaustive pattern matches
- List pattern inference (nil + cons patterns infer a list type)

Warnings appear in both the CLI (colored stderr output) and the LSP server (yellow squiggles).

### LSP Server

A native LSP server provides IDE support:

- Hover for type information
- Go-to-definition
- Diagnostics (errors and type warnings)

Build with `make lsp`, then point your editor at the `garter-lsp` binary.

## Project Structure

| File | Purpose |
|------|---------|
| `compile.ml` | Code generation and compilation pipeline |
| `exprs.ml` | AST type definitions |
| `lexer.mll` | Lexer |
| `parser.mly` | Parser |
| `assembly.ml` | x86-64 instruction types |
| `infer.ml` | Hindley-Milner type inference |
| `types.ml` | Type representations |
| `unify.ml` | Unification algorithm |
| `registerallocation.ml` | Graph-coloring register allocator |
| `naivestack.ml` | Stack-based variable assignment (fallback) |
| `diagnostics.ml` | Error and warning formatting |
| `errors.ml` | Compiler error/warning types |
| `cli.ml` | Build orchestration (assemble, link) |
| `main.ml` | CLI entry point |
| `runner.ml` | Test runner utilities |
| `test.ml` | Test suite |
| `runtime/src/gc.rs` | Rust runtime with Cheney GC |
| `lsp/` | LSP server (analysis, hover, navigation) |

## Compilation Pipeline

```
Source -> Parse -> Well-formedness -> Type Check -> Desugar -> Tag -> Rename -> ANF -> Register Allocate -> Assembly
```

1. **Parsing**: Source text to AST
2. **Well-formedness**: Unbound variables, duplicate bindings, scope errors
3. **Type checking**: HM inference, warnings collected (never fatal)
4. **Desugaring**: `def` to `letrec`, destructuring to indexing
5. **Tagging**: Unique IDs on each AST node
6. **Renaming**: Alpha-conversion for unique variable names
7. **ANF**: A-Normal Form -- all intermediate values named
8. **Register allocation**: Graph-coloring assignment of variables to registers/stack slots
9. **Code generation**: x86-64 NASM assembly

### Debugging

```bash
./main --dump-parsed file.garter   # Show parsed AST
./main --dump-anf file.garter      # Show ANF representation
./main --dump-located file.garter  # Show ANF with variable locations
./main -t file.garter              # Show all compilation phases
./main --no-typecheck file.garter  # Skip type inference
```

## Runtime Errors

The compiler generates runtime checks for:

- Arithmetic overflow
- Type mismatches (arithmetic on non-numbers, etc.)
- Division by zero
- Index out of bounds on tuple access
- Nil dereference
- Calling non-functions
- Arity mismatches
