#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t SNAKEVAL;

void printHelp(FILE* out, SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t NIL;
extern uint64_t tupleCounter;
extern uint64_t* STACK_BOTTOM;
extern uint64_t* FROM_S;
extern uint64_t* FROM_E;
extern uint64_t* TO_S;
extern uint64_t* TO_E;

void naive_print_heap(uint64_t* heap, uint64_t* heap_end) {
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for(uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1) {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t*)(*(heap + i)), *(heap + i));
  }
}

// Implement the functions below

void smarter_print_heap(uint64_t* from_start, uint64_t* from_end, uint64_t* to_start, uint64_t* to_end) {
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
}

/*
  Copies a Garter value from the given address to the new heap, 
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.  
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location 
    with a forwarding pointer to its new location
 */
uint64_t* copy_if_needed(uint64_t* garter_val_addr, uint64_t* heap_top) {
  uint64_t val = *garter_val_addr;

  // fprintf(stderr, "  copy_if_needed: addr=%p val=0x%lx tag=%ld\n",
  //         garter_val_addr, val, val & 0x7);

  // Check if tuple (tag 0x1, but not NIL which is exactly 0x1)
  if ((val & 0x7) == TUPLE_TAG && val != NIL) {
    uint64_t* old_addr = (uint64_t*)(val - TUPLE_TAG);
    uint64_t first_word = old_addr[0];

    // Check if already forwarded (odd first word = forwarding pointer)
    if (first_word & 0x1) {
      // Already forwarded: update the reference to point to new location
      *garter_val_addr = (first_word - 1) | TUPLE_TAG;
      return heap_top;
    }

    // Copy tuple: first_word is length*2, so actual length is first_word/2
    uint64_t len = first_word / 2;
    uint64_t words = 1 + len;  // header + elements
    for (uint64_t i = 0; i < words; i++) {
      heap_top[i] = old_addr[i];
    }

    // Install forwarding pointer (new address + 1 to mark as forwarded)
    old_addr[0] = ((uint64_t)heap_top) | 0x1;

    // Update the reference to point to new location with tuple tag
    *garter_val_addr = ((uint64_t)heap_top) | TUPLE_TAG;

    // Advance heap_top (16-byte aligned)
    return heap_top + words + (words % 2);
  }

  // Check if closure (tag 0x5)
  if ((val & 0x7) == CLOSURE_TAG) {
    uint64_t* old_addr = (uint64_t*)(val - CLOSURE_TAG);
    uint64_t first_word = old_addr[0];

    // Check if already forwarded
    if (first_word & 0x1) {
      *garter_val_addr = (first_word - 1) | CLOSURE_TAG;
      return heap_top;
    }

    // Closure layout: [arity<<2, code_ptr, num_frees, free0, free1, ...]
    uint64_t num_frees = old_addr[2];
    uint64_t words = 3 + num_frees;  // arity, code_ptr, num_frees, + free vars
    for (uint64_t i = 0; i < words; i++) {
      heap_top[i] = old_addr[i];
    }

    // Install forwarding pointer
    old_addr[0] = ((uint64_t)heap_top) | 0x1;

    // Update the reference
    *garter_val_addr = ((uint64_t)heap_top) | CLOSURE_TAG;

    // Advance (16-byte aligned)
    return heap_top + words + (words % 2);
  }

  // Not a heap pointer (number, boolean, nil), return unchanged
  return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t* gc(uint64_t* bottom_frame, uint64_t* top_frame, uint64_t* top_stack, uint64_t* from_start, uint64_t* from_end, uint64_t* to_start) {

  uint64_t* alloc_ptr = to_start;  // Where to allocate next
  uint64_t* scan_ptr = to_start;   // Where to scan next (Cheney's algorithm)

  // fprintf(stderr, "GC: bottom=%p top_frame=%p top_stack=%p from_start=%p to_start=%p\n",
  //         bottom_frame, top_frame, top_stack, from_start, to_start);

  // Phase 1: Copy all roots from the stack
  uint64_t* old_top_frame = top_frame;
  do {
    for (uint64_t* cur_word = top_stack /* maybe need a +1 here? */; cur_word < top_frame; cur_word++) {
      alloc_ptr = copy_if_needed(cur_word, alloc_ptr);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * [top_frame + 8] is the return address, and
     * [top_frame + 16] is therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t*)(*top_frame);
  } while (old_top_frame < bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do

  // Phase 2: Cheney scan - scan copied objects and copy their children
  while (scan_ptr < alloc_ptr) {
    uint64_t first_word = scan_ptr[0];

    // Determine object type from header
    // Tuple: first_word = length*2 (even, could be 2, 4, 6, 8, ...)
    // Closure: first_word = arity<<2 (multiple of 4: 0, 4, 8, 12, ...)
    //
    // Distinguishing criterion:
    // - If first_word % 4 == 2, it's definitely a tuple (odd-length tuple)
    // - If first_word % 4 == 0, check second word:
    //   - Closure: second word is a code pointer (8-byte aligned, high address > heap)
    //   - Tuple: second word is a Garter value (will have tag bits or be in heap range)
    //
    // Better heuristic: check if second word is in the from-space or to-space range
    // If not, it's likely a code pointer (closure).

    int is_closure = 0;
    if ((first_word & 0x3) == 0) {
      // Could be closure (arity*4) or even-length tuple (len*2 where len is even)
      uint64_t second_word = scan_ptr[1];

      // Code pointers are not in heap memory
      // If second_word is outside both from-space and to-space, it's a code pointer
      int in_from_space = (second_word >= (uint64_t)FROM_S && second_word < (uint64_t)FROM_E);
      int in_to_space = (second_word >= (uint64_t)TO_S && second_word < (uint64_t)TO_E);

      // Also check: Garter values have tags in low bits, code pointers are 8-byte aligned
      // Code pointers won't have tag patterns (1 for tuple, 5 for closure)
      int looks_like_garter_heap_val = ((second_word & 0x7) == 1 || (second_word & 0x7) == 5);

      // If second_word looks like a code pointer (not in heap, high address)
      if (!in_from_space && !in_to_space && !looks_like_garter_heap_val &&
          second_word > 0x100000000UL) {
        is_closure = 1;
      }
    }

    if (is_closure) {
      // Closure: [arity<<2, code_ptr, num_frees, free0, ...]
      uint64_t num_frees = scan_ptr[2];
      // Copy each free variable (they start at offset 3)
      for (uint64_t i = 0; i < num_frees; i++) {
        alloc_ptr = copy_if_needed(&scan_ptr[3 + i], alloc_ptr);
      }
      uint64_t words = 3 + num_frees;
      scan_ptr += words + (words % 2);  // 16-byte aligned
    } else {
      // Tuple: [length*2, elem0, elem1, ...]
      uint64_t len = first_word / 2;
      // Copy each element
      for (uint64_t i = 0; i < len; i++) {
        alloc_ptr = copy_if_needed(&scan_ptr[1 + i], alloc_ptr);
      }
      uint64_t words = 1 + len;
      scan_ptr += words + (words % 2);  // 16-byte aligned
    }
  }

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return alloc_ptr;
}

