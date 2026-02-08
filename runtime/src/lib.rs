//! Garter Runtime Library

pub mod builtins;
pub mod errors;
pub mod ffi;
pub mod gc;
pub mod heap;
pub mod values;

use values::SnakeVal;

const DEFAULT_HEAP_SIZE: usize = 100_000;
const MAX_HEAP_SIZE: usize = 1_000_000;

// External function defined in the generated assembly
// On macOS, the assembly uses `?our_code_starts_here` (no underscore)
#[cfg(target_os = "macos")]
extern "C" {
    #[link_name = "\x01?our_code_starts_here"]
    fn our_code_starts_here(heap: *mut u64, size: u64) -> SnakeVal;
}

#[cfg(target_os = "linux")]
extern "C" {
    #[link_name = "?our_code_starts_here"]
    fn our_code_starts_here(heap: *mut u64, size: u64) -> SnakeVal;
}

/// C main function that the linker expects
#[no_mangle]
pub extern "C" fn main(argc: i32, argv: *const *const i8) -> i32 {
    // Parse command line argument for heap size
    let heap_size = if argc > 1 {
        unsafe {
            let arg = *argv.add(1);
            (!arg.is_null())
                .then(|| std::ffi::CStr::from_ptr(arg))
                .and_then(|c_str| c_str.to_str().ok())
                .and_then(|s| s.parse::<usize>().ok())
                .filter(|&n| n > 0 && n <= MAX_HEAP_SIZE)
                .unwrap_or(DEFAULT_HEAP_SIZE)
        }
    } else {
        DEFAULT_HEAP_SIZE
    };

    unsafe {
        let aligned = heap::init_heap(heap_size);

        let result = our_code_starts_here(aligned, heap_size as u64);

        builtins::print(result);

        heap::free_heap();
    }

    0
}
