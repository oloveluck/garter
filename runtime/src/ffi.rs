//! FFI exports for assembly code
//!
//! These functions are called from the generated assembly code.
//! The assembly uses `?` prefixed names (e.g., `?print`).
//!
//! On macOS, Rust's `#[export_name]` still applies the underscore prefix,
//! so we use `global_asm!` to create symbol aliases without the underscore.

use crate::builtins;
use crate::errors;
use crate::gc;
use crate::heap;
use crate::values::SnakeVal;
use std::arch::global_asm;

// Create symbol aliases without the underscore prefix for macOS
// The assembly code expects symbols like `?error`, not `_?error`
// For HEAP and HEAP_END, we need to alias the symbol directly (same address)
#[cfg(target_os = "macos")]
global_asm!(
    ".globl \"?error\"",
    ".globl \"?print\"",
    ".globl \"?input\"",
    ".globl \"?equal\"",
    ".globl \"?set_stack_bottom\"",
    ".globl \"?try_gc\"",
    ".globl \"?print_stack\"",
    ".globl \"?naive_print_heap\"",
    ".globl \"?HEAP\"",
    ".globl \"?HEAP_END\"",
    "\"?error\": jmp _ffi_error",
    "\"?print\": jmp _ffi_print",
    "\"?input\": jmp _ffi_input",
    "\"?equal\": jmp _ffi_equal",
    "\"?set_stack_bottom\": jmp _ffi_set_stack_bottom",
    "\"?try_gc\": jmp _ffi_try_gc",
    "\"?print_stack\": jmp _ffi_print_stack",
    "\"?naive_print_heap\": jmp _ffi_naive_print_heap",
    // HEAP and HEAP_END: use .set to create a symbol alias (same address)
    // .globl must come before .set for the symbol to be exported
    ".set \"?HEAP\", _HEAP",
    ".set \"?HEAP_END\", _HEAP_END",
);

// Linux doesn't need the alias workaround
#[cfg(target_os = "linux")]
global_asm!(
    ".globl \"?error\"",
    ".globl \"?print\"",
    ".globl \"?input\"",
    ".globl \"?equal\"",
    ".globl \"?set_stack_bottom\"",
    ".globl \"?try_gc\"",
    ".globl \"?print_stack\"",
    ".globl \"?naive_print_heap\"",
    ".globl \"?HEAP\"",
    ".globl \"?HEAP_END\"",
    "\"?error\": jmp ffi_error",
    "\"?print\": jmp ffi_print",
    "\"?input\": jmp ffi_input",
    "\"?equal\": jmp ffi_equal",
    "\"?set_stack_bottom\": jmp ffi_set_stack_bottom",
    "\"?try_gc\": jmp ffi_try_gc",
    "\"?print_stack\": jmp ffi_print_stack",
    "\"?naive_print_heap\": jmp ffi_naive_print_heap",
    ".set \"?HEAP\", HEAP",
    ".set \"?HEAP_END\", HEAP_END",
);

/// Error handler called from assembly
#[no_mangle]
pub extern "C" fn ffi_error(code: u64, val: SnakeVal) -> ! {
    errors::error(code, val)
}

/// Print a value and return it
#[no_mangle]
pub extern "C" fn ffi_print(val: SnakeVal) -> SnakeVal {
    builtins::print(val)
}

/// Read a number from stdin
#[no_mangle]
pub extern "C" fn ffi_input() -> SnakeVal {
    builtins::input()
}

/// Deep equality comparison
#[no_mangle]
pub extern "C" fn ffi_equal(val1: SnakeVal, val2: SnakeVal) -> SnakeVal {
    builtins::equal(val1, val2)
}

/// Set the stack bottom for GC
#[no_mangle]
pub extern "C" fn ffi_set_stack_bottom(rbp: *mut u64) -> SnakeVal {
    heap::set_stack_bottom(rbp);
    0
}

/// Try to allocate, running GC if needed
#[no_mangle]
pub extern "C" fn ffi_try_gc(
    alloc_ptr: *mut u64,
    amount_needed: u64,
    first_frame: *mut u64,
    stack_top: *mut u64,
) -> *mut u64 {
    unsafe { gc::try_gc(alloc_ptr, amount_needed, first_frame, stack_top) }
}

/// Print a register value with optional snake value interpretation
unsafe fn print_register<W: std::io::Write>(
    out: &mut W,
    name: &str,
    addr: *mut u64,
    show_value: bool,
) {
    use crate::builtins::print_val_to;

    let _ = write!(out, "{}: {:#018x}\t==>  ", name, addr as u64);
    if show_value {
        print_val_to(out, *addr);
    }
    let _ = writeln!(out);
}

/// Debug: print stack contents
#[no_mangle]
pub extern "C" fn ffi_print_stack(
    val: SnakeVal,
    rsp: *mut u64,
    rbp: *mut u64,
    args: u64,
) -> SnakeVal {
    use crate::builtins::print_val_to;
    use std::io::Write;

    let stdout = std::io::stdout();
    let mut handle = stdout.lock();

    unsafe {
        print_register(&mut handle, "RSP", rsp, true);
        print_register(&mut handle, "RBP", rbp, true);

        let _ = writeln!(
            handle,
            "(difference: {})",
            (rsp as isize - rbp as isize) / 8
        );

        let _ = write!(handle, "Requested return val: {:#018x}\t==> ", val);
        print_val_to(&mut handle, val);
        let _ = writeln!(handle);

        let _ = writeln!(handle, "Num args: {}", args);

        let stack_bottom = heap::get_stack_bottom();

        if rsp > rbp {
            let _ = writeln!(handle, "Error: RSP and RBP are not properly oriented");
        } else {
            let mut cur = rsp;
            let mut current_rbp = rbp;

            while cur < stack_bottom.add(3) {
                if cur == stack_bottom {
                    let _ = writeln!(
                        handle,
                        "BOT {:#018x}: {:#018x}\t==>  old rbp",
                        cur as u64, *cur
                    );
                } else if cur == current_rbp {
                    let _ = writeln!(
                        handle,
                        "RBP {:#018x}: {:#018x}\t==>  old rbp",
                        cur as u64, *cur
                    );
                } else if cur == current_rbp.add(1) {
                    let _ = writeln!(
                        handle,
                        "    {:#018x}: {:#018x}\t==>  saved ret",
                        cur as u64, *cur
                    );
                    current_rbp = (*current_rbp) as *mut u64;
                } else if cur == stack_bottom.add(2) {
                    let _ =
                        writeln!(handle, "    {:#018x}: {:#018x}\t==>  heap", cur as u64, *cur);
                } else {
                    let _ = write!(handle, "    {:#018x}: {:#018x}\t==>  ", cur as u64, *cur);
                    print_val_to(&mut handle, *cur);
                    let _ = writeln!(handle);
                }
                cur = cur.add(1);
            }
        }

        let _ = handle.flush();
    }

    val
}

/// Debug: print heap contents
#[no_mangle]
pub extern "C" fn ffi_naive_print_heap(heap: *mut u64, heap_end: *mut u64) -> *mut u64 {
    unsafe { gc::naive_print_heap(heap, heap_end) }
}
