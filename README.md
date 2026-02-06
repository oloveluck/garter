# Garter Compiler

Compiler for the Garter language, targeting x86-64.
Written for the Compilers CS Capstone @ Northeastern University w/ Ben Lerner

## Building

```bash
make main      # Build compiler
make test      # Build test suite
./test         # Run tests
make clean     # Clean build artifacts
```

## Usage

```bash
./main program.garter    # Outputs assembly to stdout
```

## Testing

```bash
make test && ./test           # Build and run all tests
make test-verbose             # Run tests with verbose output
make test-one TEST=print3     # Run a single test by name
```

## Language Features

### Values
- Numbers: integers with overflow checking
- Booleans: `true`, `false`
- Tuples: `(1, 2, 3)`
- Nil: `nil`

### Arithmetic
- `+`, `-`, `*`
- `add1`, `sub1`

### Comparisons
- `<`, `>`, `<=`, `>=`, `==`

### Boolean Operations
- `&&`, `||`, `!`

### Tuples
- Creation: `(1, 2, 3)`
- Access: `t[0]`
- Mutation: `t[0] := 5`
- Destructuring: `let (a, b) = (1, 2) in a`

### Functions
- Lambda: `lambda(x, y): x + y`
- Definition: `def f(x): x + 1`
- Recursion supported

### Control Flow
- Let bindings: `let x = 1 in x + 1`
- Conditionals: `if cond: then_expr else: else_expr`
- Sequences: `begin expr1; expr2; expr3 end`

### Type Checking
- `isnum(x)`, `isbool(x)`, `istuple(x)`

### I/O
- `print(x)` - prints value and returns it
- `input()` - reads a number from stdin

## Project Structure

- `compile.ml` - Main compiler implementation
- `exprs.ml` - AST type definitions
- `lexer.mll` - Lexer specification
- `parser.mly` - Parser specification
- `assembly.ml` - Assembly instruction types
- `runner.ml` - Test runner utilities
- `test.ml` - Test suite
- `gc.c` - Garbage collector (runtime)
- `main.c` - Runtime entry point

## Compilation Pipeline

The compiler transforms source code through several phases:

```
Source → Parsed → WellFormed → Desugared → Tagged → Renamed → ANFed → Located → Assembly
```

### Pipeline Phases

1. **Source**: Raw text input from `.garter` file
2. **Parsing** (`lexer.mll`, `parser.mly`): Text to AST - converts source code to abstract syntax tree
3. **Well-formedness** (`compile.ml:is_well_formed`): Checks for unbound variables, duplicate bindings, and other static errors
4. **Desugaring** (`compile.ml:desugar`): Expands syntactic sugar:
   - `def f(x): body` → `letrec f = lambda(x): body`
   - Sequences → nested lets
   - Tuple destructuring → explicit indexing
5. **Tagging** (`exprs.ml:tag`): Adds unique IDs to each AST node for code generation labels
6. **Renaming** (`compile.ml:rename_and_tag`): Makes all variable names unique (alpha-conversion)
7. **ANF Conversion** (`compile.ml:anf`): Converts to A-Normal Form where all intermediate values are named
8. **Location Assignment** (`naivestack.ml`): Assigns stack slots or registers to each variable
9. **Code Generation** (`compile.ml:compile_prog`): Generates x86-64 assembly

### Debugging Compilation

Use these flags to inspect intermediate representations:

```bash
./main --dump-parsed file.garter   # Show parsed AST
./main --dump-anf file.garter      # Show ANF representation
./main --dump-located file.garter  # Show ANF with variable locations
./main -t file.garter              # Show all compilation phases
```

## Runtime Errors

The compiler generates runtime checks for:
- Arithmetic overflow
- Type mismatches (arithmetic on non-numbers, etc.)
- Index out of bounds on tuple access
- Nil dereference
- Calling non-functions
- Arity mismatches
