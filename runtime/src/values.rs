//! Value tagging for Garter runtime
//!
//! Garter uses tagged pointers to represent values:
//! - Numbers: tag 0x0, value shifted left by 1
//! - Booleans: tag 0x7, true=0xFFFF..., false=0x7FFF...
//! - Tuples: tag 0x1, pointer to heap
//! - Closures: tag 0x5, pointer to heap
//! - Strings: tag 0x3, pointer to heap
//! - Nil: exactly 0x1

use std::fmt;

pub type SnakeVal = u64;

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Num(i64),
    Bool(bool),
    Nil,
    Tuple(*mut u64),
    Closure(*mut u64),
    String(*mut u64),
}

pub fn classify(val: SnakeVal) -> Value {
    if val == NIL { return Value::Nil; }
    if val == BOOL_TRUE { return Value::Bool(true); }
    if val == BOOL_FALSE { return Value::Bool(false); }
    if is_num(val) { return Value::Num(untag_num(val)); }
    if is_tuple(val) { return Value::Tuple(untag_tuple(val)); }
    if is_closure(val) { return Value::Closure(untag_closure(val)); }
    if is_string(val) { return Value::String(untag_string(val)); }
    panic!("Unknown value type: {:#018x}", val)
}

pub const HEAP_TAG_MASK: u64 = 0x7;
pub const NUM_TAG_MASK: u64 = 0x1;
pub const BOOL_TAG_MASK: u64 = HEAP_TAG_MASK;
pub const TUPLE_TAG_MASK: u64 = HEAP_TAG_MASK;
pub const CLOSURE_TAG_MASK: u64 = HEAP_TAG_MASK;
pub const STRING_TAG_MASK: u64 = HEAP_TAG_MASK;

pub const NUM_TAG: u64 = 0x0000000000000000;
pub const BOOL_TAG: u64 = 0x0000000000000007;
pub const TUPLE_TAG: u64 = 0x0000000000000001;
pub const CLOSURE_TAG: u64 = 0x0000000000000005;
pub const STRING_TAG: u64 = 0x0000000000000003;

pub const BOOL_TRUE: u64 = 0xFFFFFFFFFFFFFFFF;
pub const BOOL_FALSE: u64 = 0x7FFFFFFFFFFFFFFF;
pub const NIL: u64 = TUPLE_TAG; // 0x1

#[inline]
pub fn is_num(val: SnakeVal) -> bool {
    (val & NUM_TAG_MASK) == NUM_TAG
}

#[inline]
pub fn is_bool(val: SnakeVal) -> bool {
    (val & BOOL_TAG_MASK) == BOOL_TAG
}

#[inline]
pub fn is_tuple(val: SnakeVal) -> bool {
    (val & TUPLE_TAG_MASK) == TUPLE_TAG && val != NIL
}

#[inline]
pub fn is_closure(val: SnakeVal) -> bool {
    (val & CLOSURE_TAG_MASK) == CLOSURE_TAG
}

#[inline]
pub fn is_string(val: SnakeVal) -> bool {
    (val & STRING_TAG_MASK) == STRING_TAG
}

#[inline]
pub fn is_nil(val: SnakeVal) -> bool {
    val == NIL
}

#[inline]
pub fn untag_num(val: SnakeVal) -> i64 {
    (val as i64) >> 1
}

#[inline]
pub fn tag_num(n: i64) -> SnakeVal {
    (n << 1) as u64
}

#[inline]
pub fn untag_tuple(val: SnakeVal) -> *mut u64 {
    (val - TUPLE_TAG) as *mut u64
}

#[inline]
pub fn untag_closure(val: SnakeVal) -> *mut u64 {
    (val - CLOSURE_TAG) as *mut u64
}

#[inline]
pub fn untag_string(val: SnakeVal) -> *mut u64 {
    (val - STRING_TAG) as *mut u64
}

#[inline]
pub fn tag_tuple(ptr: *mut u64) -> SnakeVal {
    (ptr as u64) | TUPLE_TAG
}

#[inline]
pub fn tag_closure(ptr: *mut u64) -> SnakeVal {
    (ptr as u64) | CLOSURE_TAG
}

#[inline]
pub fn tag_string(ptr: *mut u64) -> SnakeVal {
    (ptr as u64) | STRING_TAG
}

#[inline]
pub fn bool_to_snake(b: bool) -> SnakeVal {
    if b {
        BOOL_TRUE
    } else {
        BOOL_FALSE
    }
}

#[inline]
pub fn snake_to_bool(val: SnakeVal) -> bool {
    val == BOOL_TRUE
}

pub struct DisplaySnakeVal(pub SnakeVal);

impl fmt::Display for DisplaySnakeVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match classify(self.0) {
            Value::Nil => write!(f, "nil"),
            Value::Bool(true) => write!(f, "true"),
            Value::Bool(false) => write!(f, "false"),
            Value::Num(n) => write!(f, "{}", n),
            Value::Tuple(_) => write!(f, "<tuple>"),
            Value::Closure(_) => write!(f, "<closure>"),
            Value::String(addr) => {
                unsafe {
                    let len = *addr as usize;
                    let chars = addr.add(1) as *const u8;
                    let bytes = std::slice::from_raw_parts(chars, len);
                    for &c in bytes {
                        write!(f, "{}", c as char)?;
                    }
                }
                Ok(())
            }
        }
    }
}
