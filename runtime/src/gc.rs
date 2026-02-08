//! Cheney's copying garbage collector

use crate::heap::*;
use crate::values::*;
use std::ptr;

const FORWARDING_MARKER: u64 = 0x1;
const STRING_LENGTH_THRESHOLD: u64 = 1_000_000;
const MIN_CODE_POINTER: u64 = 0x1_0000_0000;

#[inline]
fn is_forwarded(first_word: u64) -> bool {
    (first_word & FORWARDING_MARKER) != 0
}

#[inline]
fn forwarded_address(first_word: u64) -> u64 {
    first_word - FORWARDING_MARKER
}

#[inline]
fn is_in_space(addr: u64, start: *mut u64, end: *mut u64) -> bool {
    addr >= start as u64 && addr < end as u64
}

#[inline]
fn looks_like_heap_value(word: u64) -> bool {
    matches!(word & 0x7, 1 | 3 | 5)
}

#[inline]
fn align_words(words: u64) -> u64 {
    words + (words & 1)
}

enum HeapObjectKind {
    Tuple { len: u64 },
    String { char_words: u64 },
    Closure { num_frees: u64 },
}

/// Detect the kind of heap object at the given pointer
///
/// # Safety
/// scan_ptr must point to a valid heap object header
unsafe fn detect_object_kind(scan_ptr: *mut u64, from_start: *mut u64, from_end: *mut u64, to_start: *mut u64, to_end: *mut u64) -> HeapObjectKind {
    let first_word = *scan_ptr;

    // Check if first_word is odd and small (likely a string length)
    if is_forwarded(first_word) && first_word <= STRING_LENGTH_THRESHOLD {
        let char_words = (first_word + 7) / 8;
        return HeapObjectKind::String { char_words };
    }

    // Check if this could be a closure
    if (first_word & 0x3) == 0 {
        let second_word = *scan_ptr.add(1);

        // Code pointers are not in heap memory
        let in_from_space = is_in_space(second_word, from_start, from_end);
        let in_to_space = is_in_space(second_word, to_start, to_end);

        // If second_word looks like a code pointer (not in heap, high address, aligned)
        if !in_from_space
            && !in_to_space
            && !looks_like_heap_value(second_word)
            && second_word > MIN_CODE_POINTER
            && (second_word & 0x7) == 0
        {
            let num_frees = (*scan_ptr.add(1)) / 2;
            return HeapObjectKind::Closure { num_frees };
        }
    }

    HeapObjectKind::Tuple { len: first_word / 2 }
}

unsafe fn copy_object(old_addr: *mut u64, heap_top: *mut u64, words: u64, tag: u64, garter_val_addr: *mut u64) -> *mut u64 {
    ptr::copy_nonoverlapping(old_addr, heap_top, words as usize);

    *old_addr = (heap_top as u64) | FORWARDING_MARKER;

    *garter_val_addr = (heap_top as u64) | tag;

    heap_top.add(align_words(words) as usize)
}

pub unsafe fn copy_if_needed(garter_val_addr: *mut u64, heap_top: *mut u64) -> *mut u64 {
    let val = *garter_val_addr;

    if (val & 0x7) == TUPLE_TAG && val != NIL {
        let old_addr = (val - TUPLE_TAG) as *mut u64;
        let first_word = *old_addr;

        if is_forwarded(first_word) {
            *garter_val_addr = forwarded_address(first_word) | TUPLE_TAG;
            return heap_top;
        }

        let len = first_word / 2;
        let words = 1 + len; // header + elements
        return copy_object(old_addr, heap_top, words, TUPLE_TAG, garter_val_addr);
    }

    if (val & 0x7) == STRING_TAG {
        let old_addr = (val - STRING_TAG) as *mut u64;
        let first_word = *old_addr;

        if is_forwarded(first_word) {
            *garter_val_addr = forwarded_address(first_word) | STRING_TAG;
            return heap_top;
        }

        let len = first_word;
        let char_words = (len + 7) / 8;
        let words = 1 + char_words;
        return copy_object(old_addr, heap_top, words, STRING_TAG, garter_val_addr);
    }

    if (val & 0x7) == CLOSURE_TAG {
        let old_addr = (val - CLOSURE_TAG) as *mut u64;
        let first_word = *old_addr;

        if is_forwarded(first_word) {
            *garter_val_addr = forwarded_address(first_word) | CLOSURE_TAG;
            return heap_top;
        }

        let num_frees = (*old_addr.add(1)) / 2;
        let words = 3 + num_frees;
        return copy_object(old_addr, heap_top, words, CLOSURE_TAG, garter_val_addr);
    }

    // Not a heap pointer (number, boolean, nil), return unchanged
    heap_top
}

pub unsafe fn gc(
    bottom_frame: *mut u64,
    top_frame: *mut u64,
    top_stack: *mut u64,
    _from_start: *mut u64,
    _from_end: *mut u64,
    to_start: *mut u64,
) -> *mut u64 {
    let mut alloc_ptr = to_start;
    let mut scan_ptr = to_start;

    let mut current_top_frame = top_frame;
    let mut current_top_stack = top_stack;
    let mut old_top_frame;

    loop {
        let mut cur_word = current_top_stack;
        while cur_word < current_top_frame {
            alloc_ptr = copy_if_needed(cur_word, alloc_ptr);
            cur_word = cur_word.add(1);
        }

        old_top_frame = current_top_frame;
        current_top_stack = current_top_frame.add(2);
        current_top_frame = *current_top_frame as *mut u64;

        if old_top_frame >= bottom_frame {
            break;
        }
    }

    while scan_ptr < alloc_ptr {
        let kind = detect_object_kind(scan_ptr, FROM_S, FROM_E, TO_S, TO_E);

        match kind {
            HeapObjectKind::String { char_words } => {
                let words = 1 + char_words;
                scan_ptr = scan_ptr.add(align_words(words) as usize);
            }
            HeapObjectKind::Closure { num_frees } => {
                for i in 0..num_frees {
                    alloc_ptr = copy_if_needed(scan_ptr.add(3 + i as usize), alloc_ptr);
                }
                let words = 3 + num_frees;
                scan_ptr = scan_ptr.add(align_words(words) as usize);
            }
            HeapObjectKind::Tuple { len } => {
                for i in 0..len {
                    alloc_ptr = copy_if_needed(scan_ptr.add(1 + i as usize), alloc_ptr);
                }
                let words = 1 + len;
                scan_ptr = scan_ptr.add(align_words(words) as usize);
            }
        }
    }

    alloc_ptr
}

/// Try to reserve memory, running GC if needed.
///
/// # Arguments
/// * `alloc_ptr` - Current heap allocation pointer (R15)
/// * `bytes_needed` - Number of bytes needed
/// * `cur_frame` - Current RBP
/// * `cur_stack_top` - Current RSP
///
/// # Returns
/// New allocation pointer after GC
///
/// # Safety
/// This function performs garbage collection.
pub unsafe fn try_gc(
    _alloc_ptr: *mut u64,
    bytes_needed: u64,
    cur_frame: *mut u64,
    cur_stack_top: *mut u64,
) -> *mut u64 {
    let layout = std::alloc::Layout::from_size_align((HEAP_SIZE + 15) * 8, 8).unwrap();
    let new_heap = std::alloc::alloc_zeroed(layout) as *mut u64;
    let old_heap = HEAP;

    if new_heap.is_null() {
        eprintln!("Out of memory: could not allocate a new semispace for garbage collection");
        if !old_heap.is_null() {
            std::alloc::dealloc(old_heap as *mut u8, layout);
        }
        std::process::exit(crate::errors::ERR_OUT_OF_MEMORY as i32);
    }

    let new_r15 = ((new_heap as u64 + 15) & !0xF) as *mut u64;
    let new_heap_end = new_r15.add(HEAP_SIZE);

    FROM_S = ((HEAP as u64 + 15) & !0xF) as *mut u64;
    FROM_E = HEAP_END;
    TO_S = new_r15;
    TO_E = new_heap_end;

    let new_r15 = gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, HEAP_END, new_r15);

    HEAP = new_heap;
    HEAP_END = new_heap_end;

    std::alloc::dealloc(old_heap as *mut u8, layout);

    let words_needed = bytes_needed / 8;
    let heap_size = HEAP_SIZE;
    if words_needed > heap_size as u64 {
        eprintln!(
            "Allocation error: needed {} words, but the heap is only {} words",
            words_needed, heap_size
        );
        std::alloc::dealloc(new_heap as *mut u8, layout);
        std::process::exit(crate::errors::ERR_OUT_OF_MEMORY as i32);
    }

    let remaining = (HEAP_END as usize - new_r15 as usize) / 8;
    if words_needed > remaining as u64 {
        eprintln!(
            "Out of memory: needed {} words, but only {} remain after collection",
            words_needed, remaining
        );
        std::alloc::dealloc(new_heap as *mut u8, layout);
        std::process::exit(crate::errors::ERR_OUT_OF_MEMORY as i32);
    }

    new_r15
}

pub unsafe fn naive_print_heap(heap: *mut u64, heap_end: *mut u64) -> *mut u64 {
    println!(
        "In naive_print_heap from {:p} to {:p}",
        heap as *const u64, heap_end as *const u64
    );
    let count = (heap_end as usize - heap as usize) / 8;
    for i in 0..count {
        let addr = heap.add(i);
        let val = *addr;
        println!("  {}/{:p}: {:p} ({})", i, addr, val as *const u64, val);
    }
    heap
}
