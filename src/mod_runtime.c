#include <stdio.h>
#include <string.h>
#include <stdlib.h>

void *allocate(int, void*);
int   print(void*);
int   print_error(int*, int);
void  print_content(void**, int);
int  *gc_copy(int*);
void  gc();

//#define HEAP_SIZE 1048576  // one megabyte
#define HEAP_SIZE 12  // twelve bytes
#define ENABLE_GC

void** heap;           // the current heap
void** heap2;          // the heap for copying
void** heap_temp;      // a pointer used for swapping heap/heap2
void** allocptr;       // current allocation position
int words_allocated=0; 

int *stack; // pointer to the bottom of the stack (i.e. value
            // upon program startup)

int tries = 0; // number of attempts at allocation

/*
 * Helper for the print() function
 */
void print_content(void** in, int depth) {
   if (depth >= 4) {
      printf("...");
      return;
   }
   int x = (int) in;
   if (x&1) {
      printf("%i",x>>1);
   } else {
      int size= *((int*)in);
      void** data = in+1;
      int i;
      printf("{s:%i", size);
      for (i=0;i<size;i++) {
         printf(", ");
         print_content(*data,depth+1);
         data++;
      }
      printf("}");
   }
}

/*
 * Runtime "print" function
 */
int print(void* l) {
   print_content(l,0);
   printf("\n");

   return 1;
}

/*
 * Helper for the gc() function.
 * Copies (compacts) an object from the old heap into
 * the empty heap
 */
int *gc_copy(int *old) {
   int size;
   int i;
   int *temp;
   int *test;
   void *the_new;

   // if the value actually references into the heap,
   // we know it's a real pointer, since raw numeric
   // values should ALWAYS have the least-significant-bit set
   if((void**)old >= heap && (void**)old < (heap+HEAP_SIZE)) {
      // get the size of the object
      size = old[0];
      // if this object has not already been copied...
      if(size >= 0) {
         // use the allocate function to update the
         // heap allocation position
         the_new = allocate((size<<1)+1, (void*)0);
         // go through the object's data, and recursively
         // copy them into the empty heap
         for(i = 1; i < size; i++) {
            temp = (int*)old[i];
            test = gc_copy(temp);
            if(test != 0) {
               old[i] = (int)test;
            }
         }
         // actually copy the memory from old heap to new heap
         memcpy(the_new,(void*)old,size+1);
         old[0] = -1; // mark this object as copied
         return the_new;
      } else {
         return 0;
      }
   } else {
      return 0;
   }
}

/*
 * Initiates garbage collection
 */
void gc() {
   size_t i;
   int *test;
   int *esp;
   size_t num;

   // grab the esp (top-of-stack) register
   asm ("movl %%esp, %0;"
        :"=r"(esp)        /* output */
        :         /* input */
        :         /* clobbered register */
   );  

   // calculate the stack size
   num = stack-esp;

   //printf("Garbage collection: stack=%p, esp=%p, num=%d\n", stack, esp, num);

   // swap in the empty heap to use for storing
   // compacted objects
   heap_temp = heap;
   heap = heap2;
   heap2 = heap_temp;

   // reset heap position
   allocptr = heap;
   words_allocated = 0;

   #define NUM_REGISTERS 2 // 6
   int *registers[NUM_REGISTERS];

   // the callee-save registers might have roots, so we need to
   // examine them (and possibly update the pointers)
   asm ("movl %%edi, %0;"
        "movl %%esi, %1;"
        //"movl %%eax, %2;"
        //"movl %%ebx, %3;"
        //"movl %%ecx, %4;"
        //"movl %%edx, %5;"
        :"=r"(registers[0]), "=r"(registers[1])
        // ,"=r"(registers[2]), "=r"(registers[3]), "=r"(registers[4]), "=r"(registers[5]) // outputs
        :         // inputs (none)
        :         // clobbered registers (none)
   ); 

   // anything pointed to by the registers
   // gets copied into our empty heap
   for(i = 0; i < NUM_REGISTERS; i++) {
      test = gc_copy(registers[i]);
      if(test != 0) {
         registers[i] = test; // record the updated the pointer
      }
   }

   // write any updated registers back
   asm ("movl %0, %%edi;"
        "movl %1, %%esi;"
        //"movl %2, %%eax;"
        //"movl %3, %%ebx;"
        //"movl %4, %%ecx;"
        //"movl %5, %%edx;"
        :         // outputs (none)
        :"r"(registers[0]), "r"(registers[1])
        // ,"r"(registers[2]), "r"(registers[3]), "r"(registers[4]), "r"(registers[5]) // inputs
        :         // clobbered registers (none)
   );

   // finally, we need to copy anything pointed at
   // by the stack into our empty heap
   for(i = 0; i <= num; i++) {
      //printf("   %d / %d\n", i, num);
      test = gc_copy((int*)esp[i]);
      if(test != 0) {
         esp[i] = (int)test; // update the stack
      }
   }
}

/*
 * The "allocate" runtime function
 */
void* allocate(int fw_size, void *fw_fill) {
   int size = fw_size >> 1;
   void** ret = (void**)allocptr;
   int i;

   if (!(fw_size&1)) {
      printf("allocate called with size input that was not an encoded integer, %i\n",
             fw_size);
   }
   if (size < 0) {
      printf("allocate called with size of %i\n",size);
      exit(-1);
   }

   allocptr+=(size+1);
   words_allocated+=(size+1);

   if (words_allocated < HEAP_SIZE) {
     *((int*)ret)=size;
     void** data = ret+1;
     for (i=0;i<size;i++) {
        *data = fw_fill;
        data++;
     }
     tries = 0;
     return ret;
   }
#ifdef ENABLE_GC
   // if we failed to allocate, do a garbage collection
   else if(tries < 1) {
      ++tries;
      //printf("Garbage collecting!\n");
      gc();
      return allocate(fw_size, fw_fill);
   }
#endif
   else {
      printf("out of memory");
      exit(-1);
   }
}

/*
 * The "print-error" runtime function
 */
int print_error(int* array, int fw_x) {
   printf("attempted to use position %i in an array that only has %i positions\n",
		 fw_x>>1, *array);
   exit(0);
}

/*
 * Program entry-point
 */
int main() {
   // move esp into the bottom-of-stack pointer
   asm ("movl %%esp, %0;"
      : "=r"(stack) // outputs
      :             // inputs (none)
      :             // clobbered registers (none)
   );  

   heap = (void*)malloc(HEAP_SIZE*sizeof(void*));
   heap2 = (void*)malloc(HEAP_SIZE*sizeof(void*));
   if (!heap || !heap2) {
      printf("malloc failed\n");
      exit(-1);
   }
   allocptr = heap;
   go();   // call into the generated code
   return 0;
}
