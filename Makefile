SNAKE_EXT= garter
UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  NASM_FORMAT=elf64
  CLANG_FLAGS=-mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer
  RUST_TARGET=x86_64-unknown-linux-gnu
else
ifeq ($(UNAME), Darwin)
  NASM_FORMAT=macho64
  CLANG_FLAGS=-arch x86_64 -mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer
  RUST_TARGET=x86_64-apple-darwin
endif
endif

RUNTIME_LIB=runtime/target/$(RUST_TARGET)/release/libgarter_runtime.a

PKGS=ounit2,extlib,unix

.PHONY: main test clean runtime runtime-debug all lsp

# Build everything
all: main runtime

main: *.ml parser.mly lexer.mll
	opam exec -- dune build main.exe
	rm -f main
	cp _build/default/main.exe main

lsp:
	opam exec -- dune build lsp/garter_lsp.exe
	rm -f garter-lsp
	cp _build/default/lsp/garter_lsp.exe garter-lsp

test: *.ml parser.mly lexer.mll runtime
	opam exec -- dune build test.exe
	rm -f test
	cp _build/default/test.exe test

test-verbose: test
	./test -display true -runner sequential

# Usage: make test-one NAME=print3
# Finds and runs a test by name (searches all_tests:0:unit_tests:*:NAME)
test-one: test
	@TEST_PATH=$$(./test -list-test 2>&1 | grep ":$(NAME)$$" | head -1) && \
	if [ -z "$$TEST_PATH" ]; then \
		echo "Test '$(NAME)' not found"; \
		exit 1; \
	fi && \
	./test -only-test "$$TEST_PATH"

# Build Rust runtime (cross-compile for x86-64 on ARM64 Mac)
runtime:
	cd runtime && cargo build --release --target $(RUST_TARGET)

runtime-debug:
	cd runtime && cargo build --target $(RUST_TARGET)

# Build the garter CLI tool
garter-cli: runtime
	cd runtime && cargo build --release --bin garter

# Link with Rust runtime (new rules)
output/%.run: output/%.o $(RUNTIME_LIB)
	clang $(CLANG_FLAGS) -o $@ $< $(RUNTIME_LIB) -lpthread -ldl

output/%.o: output/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/%.s
output/%.s: input/%.$(SNAKE_EXT) main
	./main $< > $@

output/do_pass/%.run: output/do_pass/%.o $(RUNTIME_LIB)
	clang $(CLANG_FLAGS) -o $@ $< $(RUNTIME_LIB) -lpthread -ldl

output/do_pass/%.o: output/do_pass/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/do_pass/%.s
output/do_pass/%.s: input/do_pass/%.$(SNAKE_EXT) main
	./main $< > $@


output/dont_pass/%.run: output/dont_pass/%.o $(RUNTIME_LIB)
	clang -g $(CLANG_FLAGS) -o $@ $< $(RUNTIME_LIB) -lpthread -ldl

output/dont_pass/%.o: output/dont_pass/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/dont_pass/%.s
output/dont_pass/%.s: input/dont_pass/%.$(SNAKE_EXT) main
	./main $< > $@


output/do_err/%.run: output/do_err/%.o $(RUNTIME_LIB)
	clang $(CLANG_FLAGS) -o $@ $< $(RUNTIME_LIB) -lpthread -ldl

output/do_err/%.o: output/do_err/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/do_err/%.s
output/do_err/%.s: input/do_err/%.$(SNAKE_EXT) main
	./main $< > $@


output/dont_err/%.run: output/dont_err/%.o $(RUNTIME_LIB)
	clang -g $(CLANG_FLAGS) -o $@ $< $(RUNTIME_LIB) -lpthread -ldl

output/dont_err/%.o: output/dont_err/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: output/dont_err/%.s
output/dont_err/%.s: input/dont_err/%.$(SNAKE_EXT) main
	./main $< > $@


format:
	opam exec -- dune fmt

format-check:
	opam exec -- dune fmt --check

clean:
	rm -rf output/*.o output/*.s output/*.dSYM output/*.run *.log *.o
	rm -rf output/*/*.o output/*/*.s output/*/*.dSYM output/*/*.run
	rm -rf _build/
	rm -rf runtime/target/
	rm -f main test
