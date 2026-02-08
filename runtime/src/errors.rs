//! Error codes and messages for Garter runtime

use crate::builtins::print_val_to;
use crate::values::SnakeVal;
use std::convert::TryFrom;
use std::io::Write;

/// Error codes matching compile.ml
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u64)]
pub enum ErrorCode {
    CompNotNum = 1,
    ArithNotNum = 2,
    LogicNotBool = 3,
    IfNotBool = 4,
    Overflow = 5,
    GetNotTuple = 6,
    GetLowIndex = 7,
    GetHighIndex = 8,
    NilDeref = 9,
    OutOfMemory = 10,
    SetNotTuple = 11,
    SetLowIndex = 12,
    SetHighIndex = 13,
    CallNotClosure = 14,
    CallArityErr = 15,
    DivByZero = 16,
}

impl TryFrom<u64> for ErrorCode {
    type Error = ();

    fn try_from(code: u64) -> Result<Self, Self::Error> {
        match code {
            1 => Ok(Self::CompNotNum),
            2 => Ok(Self::ArithNotNum),
            3 => Ok(Self::LogicNotBool),
            4 => Ok(Self::IfNotBool),
            5 => Ok(Self::Overflow),
            6 => Ok(Self::GetNotTuple),
            7 => Ok(Self::GetLowIndex),
            8 => Ok(Self::GetHighIndex),
            9 => Ok(Self::NilDeref),
            10 => Ok(Self::OutOfMemory),
            11 => Ok(Self::SetNotTuple),
            12 => Ok(Self::SetLowIndex),
            13 => Ok(Self::SetHighIndex),
            14 => Ok(Self::CallNotClosure),
            15 => Ok(Self::CallArityErr),
            16 => Ok(Self::DivByZero),
            _ => Err(()),
        }
    }
}

impl ErrorCode {
    /// Whether this error includes the snake value in its message
    fn shows_snake_value(&self) -> bool {
        matches!(
            self,
            ErrorCode::CompNotNum
                | ErrorCode::ArithNotNum
                | ErrorCode::LogicNotBool
                | ErrorCode::IfNotBool
                | ErrorCode::Overflow
                | ErrorCode::GetNotTuple
                | ErrorCode::CallNotClosure
        )
    }

    /// Get the error message for this error code
    fn message(&self) -> &'static str {
        match self {
            ErrorCode::CompNotNum => "Error: comparison expected a number, got ",
            ErrorCode::ArithNotNum => "Error: arithmetic expected a number, got ",
            ErrorCode::LogicNotBool => "Error: logic expected a boolean, got ",
            ErrorCode::IfNotBool => "Error: if expected a boolean, got ",
            ErrorCode::Overflow => "Error: Integer overflow, got ",
            ErrorCode::GetNotTuple => "Error: get expected tuple, got ",
            ErrorCode::GetLowIndex => "Error: index too small to get, got ",
            ErrorCode::GetHighIndex => "Error: index too large to get, got ",
            ErrorCode::NilDeref => "Error: tried to access component of nil",
            ErrorCode::OutOfMemory => "Error: out of memory",
            ErrorCode::SetNotTuple => "Error: set expected tuple",
            ErrorCode::SetLowIndex => "Error: index too small to set",
            ErrorCode::SetHighIndex => "Error: index too large to set",
            ErrorCode::CallNotClosure => "Error: tried to call a non-closure value: ",
            ErrorCode::CallArityErr => "Error: arity mismatch in call",
            ErrorCode::DivByZero => "Error: division by zero",
        }
    }

    /// Whether this error uses the val as a raw integer (not a snake value)
    fn uses_raw_int(&self) -> bool {
        matches!(
            self,
            ErrorCode::GetLowIndex | ErrorCode::GetHighIndex
        )
    }
}

// Keep the old constants for backwards compatibility with compile.ml
pub const ERR_COMP_NOT_NUM: u64 = ErrorCode::CompNotNum as u64;
pub const ERR_ARITH_NOT_NUM: u64 = ErrorCode::ArithNotNum as u64;
pub const ERR_LOGIC_NOT_BOOL: u64 = ErrorCode::LogicNotBool as u64;
pub const ERR_IF_NOT_BOOL: u64 = ErrorCode::IfNotBool as u64;
pub const ERR_OVERFLOW: u64 = ErrorCode::Overflow as u64;
pub const ERR_GET_NOT_TUPLE: u64 = ErrorCode::GetNotTuple as u64;
pub const ERR_GET_LOW_INDEX: u64 = ErrorCode::GetLowIndex as u64;
pub const ERR_GET_HIGH_INDEX: u64 = ErrorCode::GetHighIndex as u64;
pub const ERR_NIL_DEREF: u64 = ErrorCode::NilDeref as u64;
pub const ERR_OUT_OF_MEMORY: u64 = ErrorCode::OutOfMemory as u64;
pub const ERR_SET_NOT_TUPLE: u64 = ErrorCode::SetNotTuple as u64;
pub const ERR_SET_LOW_INDEX: u64 = ErrorCode::SetLowIndex as u64;
pub const ERR_SET_HIGH_INDEX: u64 = ErrorCode::SetHighIndex as u64;
pub const ERR_CALL_NOT_CLOSURE: u64 = ErrorCode::CallNotClosure as u64;
pub const ERR_CALL_ARITY_ERR: u64 = ErrorCode::CallArityErr as u64;
pub const ERR_DIV_BY_ZERO: u64 = ErrorCode::DivByZero as u64;

/// Print an error message and exit
pub fn error(code: u64, val: SnakeVal) -> ! {
    let stderr = std::io::stderr();
    let mut handle = stderr.lock();

    match ErrorCode::try_from(code) {
        Ok(err_code) => {
            let msg = err_code.message();

            if err_code.shows_snake_value() {
                let _ = write!(handle, "{}", msg);
                print_val_to(&mut handle, val);
            } else if err_code.uses_raw_int() {
                let _ = writeln!(handle, "{}{}", msg, val);
            } else {
                let _ = writeln!(handle, "{}", msg);
            }

            // Print extra debug info for snake value errors
            if err_code.shows_snake_value() {
                let _ = write!(handle, "\n{:p} ==> ", val as *const u64);
                print_val_to(&mut handle, val);
            }
        }
        Err(()) => {
            let _ = write!(handle, "Error: Unknown error code: {}, val: ", code);
            print_val_to(&mut handle, val);
        }
    }

    let _ = writeln!(handle);
    let _ = handle.flush();

    std::process::exit(code as i32);
}
