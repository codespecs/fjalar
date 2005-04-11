#include <assert.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

// Regression test for bug 91162:  if a client had a SEGV signal handler,
// and jumped to a bogus address, Valgrind would abort.  With the fix,
// the following test runs to completion correctly.

static jmp_buf myjmpbuf;

static
void SIGSEGV_handler(int signum)
{
   __builtin_longjmp(myjmpbuf, 1);
}

int main(void)
{
   struct sigaction sigsegv_new, sigsegv_saved;
   int res;

   /* Install own SIGSEGV handler */
   sigsegv_new.sa_handler  = SIGSEGV_handler;
   sigsegv_new.sa_flags    = 0;
   sigsegv_new.sa_restorer = NULL;
   res = sigemptyset( &sigsegv_new.sa_mask );
   assert(res == 0);

   res = sigaction( SIGSEGV, &sigsegv_new, &sigsegv_saved );
   assert(res == 0);

   if (__builtin_setjmp(myjmpbuf) == 0) {
      // Jump to zero; will cause seg fault
      void (*fn)(void) = 0;
      fn();
      fprintf(stderr, "Got here??\n");
   } else  {
      fprintf(stderr, "Signal caught, as expected\n");
   }

   return 0;
}

