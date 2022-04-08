#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t SNAKEVAL;

void printHelp(FILE *out, SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t NUM_TAG;
extern uint64_t NIL;
extern uint64_t BOOL_TRUE;
extern uint64_t BOOL_FALSE;
extern uint64_t tupleCounter;
extern uint64_t *STACK_BOTTOM;
extern uint64_t *FROM_S;
extern uint64_t *FROM_E;
extern uint64_t *TO_S;
extern uint64_t *TO_E;

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
  printf("from heap: ");
  for (uint64_t i = 0; i < (uint64_t)(from_end - from_start); i += 1)
  {
    printf("  %ld/%p: %p -> ", i, (from_start + i), (uint64_t *)(*(from_start + i)));
    printHelp(stdout, *(from_start + i));
    printf("\n");
  }
  printf("to heap: ");
  for (uint64_t i = 0; i < (uint64_t)(to_end - to_start); i += 1)
  {
    printf("  %ld/%p: %p -> ", i, (to_start + i), (uint64_t *)(*(to_start + i)));
    printHelp(stdout, *(to_start + i));
    printf("\n");
  }

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
uint64_t *copy_if_needed(uint64_t *garter_val_addr, uint64_t *heap_top)
{
  "break [gc.c]:[75]";
  SNAKEVAL val = *garter_val_addr;
  if ((val == NIL) || ((val & NUM_TAG_MASK) == NUM_TAG) || (val == BOOL_TRUE) || (val == BOOL_FALSE))
  {
    return heap_top;
  }
  if ((val & TUPLE_TAG_MASK) == 3)
  {
    fprintf(val, "forwarding to ");
    fflush(val);
    fprintf(val, "%p", (int *)(val - 3));
    fflush(val);
  }
  else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG)
  {
  }
  else if ((val & TUPLE_TAG_MASK) == 3)
  {
    *garter_val_addr = val - 2;
  }

  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG)
  {
    uint64_t *heap_thing_addr = (uint64_t *)(val - TUPLE_TAG);
    *garter_val_addr = heap_top;
    uint64_t len = heap_thing_addr[0];
    len /= 2; // length is encoded
    if (len % 2 != 0)
    {
      len += 1;
    }
    uint64_t *heap_bottom = heap_top;
    heap_top[0] = len * 2;
    for (uint64_t i = 1; i <= len; i++)
    {
      heap_top[i] = heap_thing_addr[i];
      // uint64_t *ht = addr + len;
      // uint64_t *new_ht = copy_if_needed(heap_top[i], ht);
    }
    *heap_thing_addr = (uint64_t *)((uint64_t)(heap_top) + 3); // make fwd pointer
    uint64_t new_heap_top = heap_top + len;
    for (uint64_t i = 1; i <= len; i++)
    {
      new_heap_top = copy_if_needed(heap_bottom[i], new_heap_top);
    }
    return new_heap_top;
  }
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
uint64_t *gc(uint64_t *bottom_frame, uint64_t *top_frame, uint64_t *top_stack, uint64_t *from_start, uint64_t *from_end, uint64_t *to_start)
{

  uint64_t *old_top_frame = top_frame;
  do
  {
    for (uint64_t *cur_word = top_stack /* maybe need a +1 here? */; cur_word < top_frame; cur_word++)
    {
      to_start = copy_if_needed(cur_word, to_start);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * [top_frame + 8] is the return address, and
     * [top_frame + 16] is therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t *)(*top_frame);
  } while (old_top_frame <= bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return to_start;
}
