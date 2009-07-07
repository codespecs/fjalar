#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "../memcheck.h"
#include "leak.h"

int main(void)
{
   int  x;
   int  y = 0;
   int* reachable;
   int* dubious;
   int* leaked;
   DECLARE_LEAK_COUNTERS;

   /* we require these longs to have same size as a machine word */
   assert(sizeof(long) == sizeof(void*));

   /* Error counting */
   printf("errors: %d\n\n", VALGRIND_COUNT_ERRORS);

   if (x == 0) {
      y++;
   } else {
      y--;
   }

   printf("errors: %d\n\n", VALGRIND_COUNT_ERRORS);

   // Get a baseline, after start-up and also after printf (because Darwin
   // printf allocates memory the first time it's called!)
   GET_INITIAL_LEAK_COUNTS;

   /* Leak checking */
   GET_FINAL_LEAK_COUNTS;
   PRINT_LEAK_COUNTS(stdout);
   printf("\n");

   leaked = malloc(77);
   leaked = 0;

   dubious = malloc(88);
   dubious += 10;

   reachable = malloc(99);

   GET_FINAL_LEAK_COUNTS;
   PRINT_LEAK_COUNTS(stdout);
   printf("\n");

   printf("errors: %d\n", VALGRIND_COUNT_ERRORS);

   return 0;
}
