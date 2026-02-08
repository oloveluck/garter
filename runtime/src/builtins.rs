//! Built-in functions: print, input, equal

use crate::values::*;
use std::io::{self, Read, Write};

const VISITED_MARKER: u64 = 0x8000_0000_0000_0000;
const VISITED_ID_MASK: u64 = 0x7FFF_FFFF_FFFF_FFFF;

unsafe fn write_string_chars<W: Write>(out: &mut W, addr: *const u64) {
    let len = *addr as usize;
    let chars = addr.add(1) as *const u8;
    let bytes = std::slice::from_raw_parts(chars, len);
    for &c in bytes {
        let _ = write!(out, "{}", c as char);
    }
}

pub fn print_val_to<W: Write>(out: &mut W, val: SnakeVal) {
    let mut counter = 0u64;
    print_help(out, val, &mut counter);
}

fn print_help<W: Write>(out: &mut W, val: SnakeVal, visited: &mut u64) {
    match classify(val) {
        Value::Nil => {
            let _ = write!(out, "nil");
        }
        Value::Num(n) => {
            let _ = write!(out, "{}", n);
        }
        Value::Bool(true) => {
            let _ = write!(out, "true");
        }
        Value::Bool(false) => {
            let _ = write!(out, "false");
        }
        Value::String(addr) => {
            unsafe { write_string_chars(out, addr); }
        }
        Value::Closure(addr) => {
            unsafe {
                let arity = (*addr) / 2;
                let num_frees = (*addr.add(1)) / 2;
                let fn_ptr = *addr.add(2);
                let _ = write!(
                    out,
                    "[{:p} - 5] ==> <function arity {}, closed {}, fn-ptr {:p}>",
                    val as *const u64,
                    arity,
                    num_frees,
                    fn_ptr as *const u64
                );
            }
        }
        Value::Tuple(addr) => {
            unsafe {
                let first_word = *addr;
                if (first_word & VISITED_MARKER) != 0 {
                    let _ = write!(
                        out,
                        "<cyclic tuple {}>",
                        (first_word & VISITED_ID_MASK) as u32
                    );
                    return;
                }

                if (first_word & 0x1) != 0 {
                    let _ = write!(out, "forwarding to {:p}", (first_word - 1) as *const u64);
                    return;
                }

                let len = first_word / 2;

                *visited += 1;
                *addr = VISITED_MARKER | *visited;

                let _ = write!(out, "(");
                for i in 1..=len {
                    if i > 1 {
                        let _ = write!(out, ", ");
                    }
                    print_help(out, *addr.add(i as usize), visited);
                }
                if len == 1 {
                    let _ = write!(out, ", ");
                }
                let _ = write!(out, ")");

                // Restore the length
                *addr = len * 2;
            }
        }
    }
}

pub fn print(val: SnakeVal) -> SnakeVal {
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    print_val_to(&mut handle, val);
    let _ = writeln!(handle);
    let _ = handle.flush();
    val
}

pub fn input() -> SnakeVal {
    let mut buffer = String::new();
    let stdin = io::stdin();
    let mut handle = stdin.lock();

    handle.read_to_string(&mut buffer)
        .ok()
        .and_then(|_| buffer.trim().parse::<i64>().ok())
        .map_or_else(|| tag_num(0), tag_num)
}

pub fn equal(val1: SnakeVal, val2: SnakeVal) -> SnakeVal {
    if val1 == val2 {
        return BOOL_TRUE;
    }

    if val1 == NIL || val2 == NIL {
        return BOOL_FALSE;
    }

    match (classify(val1), classify(val2)) {
        (Value::String(str1), Value::String(str2)) => {
            unsafe {
                let len1 = *str1 as usize;
                let len2 = *str2 as usize;
                if len1 != len2 {
                    return BOOL_FALSE;
                }
                let chars1 = str1.add(1) as *const u8;
                let chars2 = str2.add(1) as *const u8;
                let s1 = std::slice::from_raw_parts(chars1, len1);
                let s2 = std::slice::from_raw_parts(chars2, len2);
                bool_to_snake(s1 == s2)
            }
        }

        (Value::Tuple(tup1), Value::Tuple(tup2)) => {
            unsafe {
                if *tup1 != *tup2 {
                    return BOOL_FALSE;
                }
                let len = (*tup1) / 2;
                for i in 1..=len as usize {
                    if equal(*tup1.add(i), *tup2.add(i)) == BOOL_FALSE {
                        return BOOL_FALSE;
                    }
                }
                BOOL_TRUE
            }
        }

        _ => BOOL_FALSE,
    }
}
