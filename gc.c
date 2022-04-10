#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t SNAKEVAL;

void printHelp(FILE *out, SNAKEVAL val);
extern void naive_print_heap(uint64_t *heap, uint64_t *heap_end) asm("?naive_print_heap");
SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp, uint64_t args) asm("?print_stack");

// void print(SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t NIL;
extern uint64_t tupleCounter;
extern uint64_t *STACK_BOTTOM;
extern uint64_t *FROM_S;
extern uint64_t *FROM_E;
extern uint64_t *TO_S;
extern uint64_t *TO_E;

char *fancy_pointer = "%#018lx";

void naive_print_heap(uint64_t *heap, uint64_t *heap_end)
{
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for (uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1)
  {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t *)(*(heap + i)), *(heap + i));
  }
}

// Implement the functions below

void smarter_print_heap(uint64_t *from_start, uint64_t *from_end, uint64_t *to_start, uint64_t *to_end)
{
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
}

/**
 * TODO:
 * Fix forwarding pointers
 * Recursive call
 * Implement lambdas
 */

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
uint64_t *copy_if_needed(uint64_t *garter_val_addr, uint64_t *heap_top, int just_log)
{
  printf("garter_val_addr: %#018lx\n", garter_val_addr);

  uint64_t val = *garter_val_addr;

  if ((val == 0x1))
  {
    return heap_top;
  }

  if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG || (val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    naive_print_heap(FROM_S, FROM_E);
    naive_print_heap(TO_S, TO_E);
    printf("\n val: %#018lx \n", val);
    int is_tuple = ((val & TUPLE_TAG_MASK) == TUPLE_TAG);
    // naive_print_heap(FROM_S, FROM_E);
    uint64_t *heap_thing_addr = (uint64_t *)(val & ~0x7);
    printf("\nheapthing addr: %#018lx\n", heap_thing_addr);
    if ((*heap_thing_addr & TUPLE_TAG_MASK) == 0x3)
    {
      *garter_val_addr = (*heap_thing_addr & TUPLE_TAG_MASK) | is_tuple ? TUPLE_TAG : CLOSURE_TAG;
      return heap_top;
    }
    // printf("\n heap_thing_addr: %ld \n", heap_thing_addr[0]);
    uint64_t length = is_tuple ? (uint64_t)(heap_thing_addr[0]) + 2 : (uint64_t)(heap_thing_addr[2]) + 6;
    printf(is_tuple ? "length: %#018lx \n" : "closure size %#018lx \n", length);
    uint64_t old_length = length / 2;
    length = length / 2;
    if (length % 2 != 0)
    {
      length += 1;
    }
    // printf("\n length: %ld, is_tuple: %d \n", length, is_tuple);
    // we have ourselves a heap_thing
    // printf("\n found heapthing, heaptop is: %ld\n", (uint64_t)heap_top);

    // copying over our heap_thing
    // smarter_print_heap(FROM_S, FROM_E, TO_S, TO_E);
    for (int i = 0; i < length; i++)
    {
      heap_top[i] = heap_thing_addr[i];
    }

    // *garter_val_addr = *garter_val_addr + 1
    // printf("garter val addr: %#018lx", garter_val_addr);

    // uint64_t *new_heap_top = (uint64_t *)((uint64_t)heap_top + (uint64_t)length);
    uint64_t *new_heap_top = heap_top + length;
    *garter_val_addr = ((uint64_t)(heap_top)) | (is_tuple ? TUPLE_TAG : CLOSURE_TAG);
    *heap_thing_addr = ((uint64_t)(heap_top) | 0x3);
    printf("\nold heap top addr: %#018lx\nnew heap top addr: %#018lx\n", heap_top, new_heap_top);
    printf("setting fowarding pointer to %#018lx at memory: %#018lx\n", *heap_thing_addr, heap_thing_addr);
    for (uint64_t i = 0; i < length; i++)
    {
      // printf("\n");
      // if (!((val & CLOSURE_TAG_MASK) == CLOSURE_TAG || (val & TUPLE_TAG_MASK) == TUPLE_TAG))
      // {
      new_heap_top = copy_if_needed((heap_top + i), new_heap_top, 0);
      // }
    }
    return new_heap_top;
  }
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
int gc_count = 0;
uint64_t *gc(uint64_t *bottom_frame, uint64_t *top_frame, uint64_t *top_stack, uint64_t *from_start, uint64_t *from_end, uint64_t *to_start)
{
  naive_print_heap(FROM_S, FROM_E);
  naive_print_heap(TO_S, TO_E);
  gc_count++;
  printf("gcing");
  uint64_t *old_top_frame = top_frame;
  do
  {
    for (uint64_t *cur_word = top_stack /* maybe need a +1 here? */; cur_word < top_frame; cur_word++)
    {
      if ((*cur_word & CLOSURE_TAG_MASK) == CLOSURE_TAG || (*cur_word & TUPLE_TAG_MASK) == TUPLE_TAG)
      {
        uint64_t *ts_old = to_start;
        // printf("old heap: \n");
        printf("\nto start: %#018lx\n", to_start);
        printf("cur_word: %#018lx\n", *cur_word);
        // printStack(*cur_word, top_stack, bottom_frame, 0);
        to_start = copy_if_needed(cur_word, to_start, 0);
        printf("\nto start: %#018lx\n", to_start);
        // printf("new heap: \n");
      }
      // print(*cur_word);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * [top_frame + 8] is the return address, and
     * [top_frame + 16] is therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t *)(*top_frame);
  } while (old_top_frame < bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return to_start;
}
