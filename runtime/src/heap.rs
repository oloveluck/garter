//! Global heap state for Garter runtime

use std::ptr;

const ALIGNMENT_PADDING: usize = 15;

fn heap_layout(size: usize) -> std::alloc::Layout {
    std::alloc::Layout::from_size_align((size + ALIGNMENT_PADDING) * 8, 8)
        .expect("Invalid layout")
}

#[inline]
fn align_to_16(addr: u64) -> *mut u64 {
    ((addr + 15) & !0xF) as *mut u64
}

pub static mut HEAP_SIZE: usize = 0;

#[no_mangle]
pub static mut HEAP: *mut u64 = ptr::null_mut();

#[no_mangle]
pub static mut HEAP_END: *mut u64 = ptr::null_mut();

pub static mut STACK_BOTTOM: *mut u64 = ptr::null_mut();

pub static mut FROM_S: *mut u64 = ptr::null_mut();
pub static mut FROM_E: *mut u64 = ptr::null_mut();
pub static mut TO_S: *mut u64 = ptr::null_mut();
pub static mut TO_E: *mut u64 = ptr::null_mut();

static mut HEAP_ALLOC: *mut u64 = ptr::null_mut();

#[inline]
pub fn heap_start() -> *mut u64 {
    unsafe { HEAP }
}

#[inline]
pub fn heap_end() -> *mut u64 {
    unsafe { HEAP_END }
}

#[inline]
pub fn heap_size() -> usize {
    unsafe { HEAP_SIZE }
}

pub unsafe fn init_heap(size: usize) -> *mut u64 {
    HEAP_SIZE = size;

    let layout = heap_layout(size);
    HEAP_ALLOC = std::alloc::alloc_zeroed(layout) as *mut u64;

    if HEAP_ALLOC.is_null() {
        eprintln!("Error: could not allocate heap");
        std::process::exit(1);
    }

    let aligned = align_to_16(HEAP_ALLOC as u64);
    HEAP = HEAP_ALLOC;
    HEAP_END = aligned.add(size);

    aligned
}

pub unsafe fn free_heap() {
    if !HEAP_ALLOC.is_null() {
        let layout = heap_layout(HEAP_SIZE);
        std::alloc::dealloc(HEAP_ALLOC as *mut u8, layout);
        HEAP_ALLOC = ptr::null_mut();
        HEAP = ptr::null_mut();
        HEAP_END = ptr::null_mut();
    }
}

pub fn set_stack_bottom(stack_bottom: *mut u64) {
    unsafe {
        STACK_BOTTOM = stack_bottom;
    }
}

pub fn get_stack_bottom() -> *mut u64 {
    unsafe { STACK_BOTTOM }
}
