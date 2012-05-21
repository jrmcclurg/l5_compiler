#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#define HEAP_SIZE 1048576  // one megabyte
//#define HEAP_SIZE 20       // small heap size for testing
#define ENABLE_GC          // uncomment this to enable GC
//#define GC_DEBUG           // uncomment this to enable GC debugging

void **heap;      // the current heap
void **heap2;     // the heap for copying
void **heap_temp; // a pointer used for swapping heap/heap2

int *allocptr;           // current allocation position
int words_allocated = 0;

int *stack; // pointer to the bottom of the stack (i.e. value
            // upon program startup)

/*
 * Helper for the print() function
 */
void print_content(void **in, int depth) {
   int i, x, size;
   void **data;

   if(depth >= 4) {
      printf("...");
      return;
   }
   // NOTE: this function crashes quite messily if "in" is 0
   // so we've added this check
   if(in == NULL) {
      printf("nil");
      return;
   }
   x = (int)in;
   if(x & 1) {
      printf("%i", x >> 1);
   } else {
      size= *((int*)in);
      data = in + 1;
      printf("{s:%i", size);
      for(i = 0; i < size; i++) {
         printf(", ");
         print_content(*data, depth + 1);
         data++;
      }
      printf("}");
   }
}


/*
 * Runtime "print" function
 */
int print(void *l) {
   print_content(l, 0);
   printf("\n");

   return 1;
}

/*
 * Runtime function for printing an array as a string
 */
void print_str(int **in) {
   int i, x, size;
   int **data;
   int c;

   if(in == NULL) {
      printf("nil");
      return;
   }
   x = (int)in;
   if(x & 1) {
      printf("%i\n", x >> 1);
   } else {
      size= (int)(*in);
      data = in + 1;
      //fwrite(data,sizeof(char),size,stdout);
      for(i = 0; i < size; i++) {
         c = (int)data[i];
         putchar(c >> 1);
      }
   }
}

/*
 * Helper for the gc() function.
 * Copies (compacts) an object from the old heap into
 * the empty heap
 */
int *gc_copy(int *old)  {
   int i, size;
   int *old_array, *new_array, *first_array_location;

   // If not a pointer or not a pointer to a heap location, return input value
   if((int)old % 4 != 0 || (void**)old < heap2 || (void**)old >= heap2 + HEAP_SIZE) {
       return old;
   }

   old_array = (int*)old;
   size = old_array[0];

   // If the size is negative, the array has already been copied to the
   // new heap, so the first location of array will contain the new address
   if(size == -1) {
       return (int*)old_array[1];
   }

   // Mark the old array as invalid, create the new array
   old_array[0] = -1;
   new_array = allocptr;
   allocptr += (size + 1);
   words_allocated += (size + 1);

   // The value of old_array[1] needs to be handled specially
   // since it holds a pointer to the new heap object
   first_array_location = (int*)old_array[1];
   old_array[1] = (int)new_array;

   // Set the values of new_array handling the first two locations separately
   new_array[0] = size;
   new_array[1] = (int)gc_copy(first_array_location);

   // Call gc_copy on the remaining values of the array
   for (i = 2; i <= size; i++) {
      new_array[i] = (int)gc_copy((int*)old_array[i]);
   }

   return new_array;
}

/*
 * Initiates garbage collection
 */
void gc(int *esp) {
   int i;
   int stack_size = stack - esp + 1;       // calculate the stack size
   int prev_words_alloc = words_allocated;

#ifdef GC_DEBUG
   printf("GC: stack=(%p,%p) (size %d): ", esp, stack, stack_size);
#endif

   // swap in the empty heap to use for storing
   // compacted objects
   heap_temp = heap;
   heap = heap2;
   heap2 = heap_temp;

   // reset heap position
   allocptr = (int*)heap;
   words_allocated = 0;

   // NOTE: the edi/esi register contents could also be
   // roots, but these have been placed in the stack
   // by the allocate() assembly function.  Thus,
   // we only need to look at the stack at this point

   // Then, we need to copy anything pointed at
   // by the stack into our empty heap
   for(i = 0; i < stack_size; i++) {
      esp[i] = (int)gc_copy((int*)esp[i]);
   }

#ifdef GC_DEBUG
   printf("reclaimed %d words\n", (prev_words_alloc - words_allocated));
#endif
}

/*
 * The "allocate" runtime function
 * (assembly stub that calls the 3-argument
 * allocate_helper function)
 */
extern void* allocate(int fw_size, void *fw_fill);
asm(
   ".globl allocate\n"
   ".type allocate, @function\n"
   "allocate:\n"
   "# grab the arguments (into eax,edx)\n"
   "popl %ecx\n" // return val
   "popl %eax\n" // arg 1
   "popl %edx\n" // arg 2
   "# put the original edi/esi on stack instead of args\n"
   "pushl %edi\n" // formerly edx
   "pushl %esi\n" // formerly eax  <-- this is the ESP we want
   "pushl %ecx\n" // ecx (return val)
   "pushl %eax\n" // eax (arg 1)
   "pushl %edx\n" // edx (arg 2)
   "# save the original esp (into ecx)\n"
   "movl %esp, %ecx\n"
   "addl $12, %ecx\n"
   "\n"
   "# save the caller's base pointer (so that LEAVE works)\n"
   "# body begins with base and\n"
   "# stack pointers equal\n"
   "pushl %ebp\n"
   "movl %esp, %ebp\n"
   "# push the first three args on stack\n"
   "pushl %ecx\n"
   "pushl %edx\n"
   "pushl %eax\n"
   "# call the real alloc\n"
   "call allocate_helper\n"
   "addl $12, %esp\n"
   "\n"
   "# restore the original base pointer (from stack)\n"
   "leave\n"
   "# restore esi/edi from stack\n"
   "popl %edx\n"  // arg 2
   "popl %ecx\n"  // arg 1
   "addl $4, %esp\n" // skip over return val (it didn't change)
   "popl %esi\n"  // restore esi
   "popl %edi\n"  // restore edi
   "pushl %edx\n" // put back arg 2
   "pushl %ecx\n" // put back arg 1
   "subl $4, %esp\n" // put back return val
   "ret\n" 
);

/*
 * The real "allocate" runtime function
 * (called by the above assembly stub function)
 */
void* allocate_helper(int fw_size, void *fw_fill, int *esp)
{
   int i, data_size, array_size;
   int *ret;

#ifdef GC_DEBUG
   printf("runtime.c: allocate(): ESP = %p (%d), EDI = %p (%d), ESI = %p (%d)\n",
          esp, (int)esp, (int*)esp[1], esp[1], (int*)esp[0], esp[0]);
#endif

   if(!(fw_size & 1)) {
      printf("allocate called with size input that was not an encoded integer, %i\n",
             fw_size);
      exit(-1);
   }

   data_size = fw_size >> 1;

   if(data_size < 0) {
      printf("allocate called with size of %i\n", data_size);
      exit(-1);
   }

   // Even if there is no data, allocate an array of two words
   // so we can hold a forwarding pointer and an int representing if
   // the array has already been garbage collected
   array_size = (data_size == 0) ? 2 : data_size + 1;

   // Check if the heap has space for the allocation
   if(words_allocated + data_size >= HEAP_SIZE)
   {
#ifdef ENABLE_GC
      // Garbage collect
      gc(esp);

      // Check if the garbage collection free enough space for the allocation
      if(words_allocated + data_size >= HEAP_SIZE) {
#endif
         printf("out of memory\n"); // NOTE: we've added a newline
         exit(-1);
#ifdef ENABLE_GC
      }
#endif
   }

   // Do the allocation
   ret = allocptr;
   allocptr += array_size;
   words_allocated += array_size;

   // Set the size of the array to be the desired size
   ret[0] = data_size;

   // If there is no data, set the value of the array to be a number
   // so it can be properly garbage collected
   if(data_size == 0) {
      ret[1] = 1;
   } else {
      // Fill the array with the fill value
      for(i = 0; i < data_size; i++) {
         ret[i+1] = (int)fw_fill;
      }
   }

   return ret;
}

/*
 * The "print-error" runtime function
 */
int print_error(int *array, int fw_x) {
   printf("attempted to use position %i in an array that only has %i positions\n",
          fw_x >> 1, *array);
   exit(0);
}

/*
 * Program entry-point
 */
int main() {
   heap  = (void*)malloc(HEAP_SIZE * sizeof(void*));
   heap2 = (void*)malloc(HEAP_SIZE * sizeof(void*));
   allocptr = (int*)heap;
   // NOTE: allocptr needs to appear in the following check, because otherwise
   // gcc apparently optimizes away the assignment (i.e. the allocate_helper function
   // sees allocptr as NULL)
   if(!allocptr || !heap2) {
      printf("malloc failed\n");
      exit(-1);
   }

   // Move esp into the bottom-of-stack pointer.
   // The "go" function's boilerplate (as long as one copies it
   // correctly from the lecture notes), in conjunction with
   // the C calling convention dictates that there will be
   // exactly 6 words added to the stack before the
   // body of "go" actually happens
   asm ("movl %%esp, %%eax;"
        "subl $24, %%eax;" // 6 * 4
        "movl %%eax, %0;"
        "call go;"
      : "=m"(stack) // outputs
      :             // inputs (none)
      : "%eax"      // clobbered registers (eax)
   );  

#ifdef GC_DEBUG
   printf("runtime.c: main(): initial ESP value = %p (%d)\n", stack, (int)stack);
#endif

   return 0;
}
