
/* This is an example of a program which does atomic memory operations
   between two processes which share a page.  Valgrind 3.4.1 and
   earlier produce incorrect answers because it does not preserve
   atomicity of the relevant instructions in the generated code; but
   the post-DCAS-merge versions of Valgrind do behave correctly. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <sys/wait.h>
#include "tests/sys_mman.h"

#define NNN 3456987

#define IS_8_ALIGNED(_ptr)   (0 == (((unsigned long)(_ptr)) & 7))


__attribute__((noinline)) void atomic_add_8bit ( char* p, int n ) 
{
#if defined(VGA_x86)
   unsigned long block[2];
   block[0] = (unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movl 0(%%esi),%%eax"      "\n\t"
      "movl 4(%%esi),%%ebx"      "\n\t"
      "lock; addb %%bl,(%%eax)"  "\n"
      : : "S"(&block[0])/* S means "esi only" */ : "memory","cc","eax","ebx"
   );
#elif defined(VGA_amd64)
   unsigned long block[2];
   block[0] = (unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movq 0(%%rsi),%%rax"      "\n\t"
      "movq 8(%%rsi),%%rbx"      "\n\t"
      "lock; addb %%bl,(%%rax)"  "\n"
      : : "S"(&block[0])/* S means "rsi only" */ : "memory","cc","rax","rbx"
   );
#elif defined(VGA_ppc32)
   /* Nasty hack.  Does correctly atomically do *p += n, but only if p
      is 8-aligned -- guaranteed by caller. */
   unsigned long success;
   do {
      __asm__ __volatile__(
         "lwarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stwcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(((unsigned long)n) << 24)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#elif defined(VGA_ppc64)
   /* Nasty hack.  Does correctly atomically do *p += n, but only if p
      is 8-aligned -- guaranteed by caller. */
   unsigned long success;
   do {
      __asm__ __volatile__(
         "ldarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stdcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(((unsigned long)n) << 56)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#else
# error "Unsupported arch"
#endif
}


__attribute__((noinline)) void atomic_add_16bit ( short* p, int n ) 
{
#if defined(VGA_x86)
   unsigned long block[2];
   block[0] = (unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movl 0(%%esi),%%eax"      "\n\t"
      "movl 4(%%esi),%%ebx"      "\n\t"
      "lock; addw %%bx,(%%eax)"  "\n"
      : : "S"(&block[0])/* S means "esi only" */ : "memory","cc","eax","ebx"
   );
#elif defined(VGA_amd64)
   unsigned long block[2];
   block[0] = (unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movq 0(%%rsi),%%rax"      "\n\t"
      "movq 8(%%rsi),%%rbx"      "\n\t"
      "lock; addw %%bx,(%%rax)"  "\n"
      : : "S"(&block[0])/* S means "rsi only" */ : "memory","cc","rax","rbx"
   );
#elif defined(VGA_ppc32)
   /* Nasty hack.  Does correctly atomically do *p += n, but only if p
      is 8-aligned -- guaranteed by caller. */
   unsigned long success;
   do {
      __asm__ __volatile__(
         "lwarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stwcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(((unsigned long)n) << 16)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#elif defined(VGA_ppc64)
   /* Nasty hack.  Does correctly atomically do *p += n, but only if p
      is 8-aligned -- guaranteed by caller. */
   unsigned long success;
   do {
      __asm__ __volatile__(
         "ldarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stdcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(((unsigned long)n) << 48)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#else
# error "Unsupported arch"
#endif
}

__attribute__((noinline)) void atomic_add_32bit ( int* p, int n ) 
{
#if defined(VGA_x86)
   unsigned long block[2];
   block[0] = (unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movl 0(%%esi),%%eax"       "\n\t"
      "movl 4(%%esi),%%ebx"       "\n\t"
      "lock; addl %%ebx,(%%eax)"  "\n"
      : : "S"(&block[0])/* S means "esi only" */ : "memory","cc","eax","ebx"
   );
#elif defined(VGA_amd64)
   unsigned long block[2];
   block[0] = (unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movq 0(%%rsi),%%rax"       "\n\t"
      "movq 8(%%rsi),%%rbx"       "\n\t"
      "lock; addl %%ebx,(%%rax)"  "\n"
      : : "S"(&block[0])/* S means "rsi only" */ : "memory","cc","rax","rbx"
   );
#elif defined(VGA_ppc32)
   unsigned long success;
   do {
      __asm__ __volatile__(
         "lwarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stwcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(n)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#elif defined(VGA_ppc64)
   /* Nasty hack.  Does correctly atomically do *p += n, but only if p
      is 8-aligned -- guaranteed by caller. */
   unsigned long success;
   do {
      __asm__ __volatile__(
         "ldarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stdcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(((unsigned long)n) << 32)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#else
# error "Unsupported arch"
#endif
}

__attribute__((noinline)) void atomic_add_64bit ( long long int* p, int n ) 
{
#if defined(VGA_x86) || defined(VGA_ppc32)
   /* do nothing; is not supported */
#elif defined(VGA_amd64)
   // this is a bit subtle.  It relies on the fact that, on a 64-bit platform,
   // sizeof(unsigned long long int) == sizeof(unsigned long) == sizeof(void*) 
   unsigned long long int block[2];
   block[0] = (unsigned long long int)(unsigned long)p;
   block[1] = n;
   __asm__ __volatile__(
      "movq 0(%%rsi),%%rax"      "\n\t"
      "movq 8(%%rsi),%%rbx"      "\n\t"
      "lock; addq %%rbx,(%%rax)" "\n"
      : : "S"(&block[0])/* S means "rsi only" */ : "memory","cc","rax","rbx"
   );
#elif defined(VGA_ppc64)
   unsigned long success;
   do {
      __asm__ __volatile__(
         "ldarx  15,0,%1"    "\n\t"
         "add    15,15,%2"   "\n\t"
         "stdcx. 15,0,%1"    "\n\t"
         "mfcr   %0"         "\n\t"
         "srwi   %0,%0,29"   "\n\t"
         "andi.  %0,%0,1"    "\n"
         : /*out*/"=b"(success)
         : /*in*/ "b"(p), "b"(n)
         : /*trash*/ "memory", "cc", "r15"
      );
   } while (success != 1);
#else
# error "Unsupported arch"
#endif
}

int main ( int argc, char** argv )
{
   int    i, status;
   char*  page;
   char*  p8;
   short* p16;
   int*   p32;
   long long int* p64;
   pid_t  child, p2;

   printf("parent, pre-fork\n");

   page = mmap( 0, sysconf(_SC_PAGESIZE),
                   PROT_READ|PROT_WRITE,
                   MAP_ANONYMOUS|MAP_SHARED, -1, 0 );
   if (page == MAP_FAILED) {
      perror("mmap failed");
      exit(1);
   }

   p8  = (char*)(page+0);
   p16 = (short*)(page+256);
   p32 = (int*)(page+512);
   p64 = (long long int*)(page+768);

   assert( IS_8_ALIGNED(p8) );
   assert( IS_8_ALIGNED(p16) );
   assert( IS_8_ALIGNED(p32) );
   assert( IS_8_ALIGNED(p64) );

   memset(page, 0, 1024);

   *p8  = 0;
   *p16 = 0;
   *p32 = 0;
   *p64 = 0;

   child = fork();
   if (child == -1) {
      perror("fork() failed\n");
      return 1;
   }

   if (child == 0) {
      /* --- CHILD --- */
      printf("child\n");
      for (i = 0; i < NNN; i++) {
         atomic_add_8bit(p8, 1);
         atomic_add_16bit(p16, 1);
         atomic_add_32bit(p32, 1);
         atomic_add_64bit(p64, 98765 ); /* ensure we hit the upper 32 bits */
      }
      return 1;
      /* NOTREACHED */

   }

   /* --- PARENT --- */

   printf("parent\n");

   for (i = 0; i < NNN; i++) {
      atomic_add_8bit(p8, 1);
      atomic_add_16bit(p16, 1);
      atomic_add_32bit(p32, 1);
      atomic_add_64bit(p64, 98765 ); /* ensure we hit the upper 32 bits */
   }

   p2 = waitpid(child, &status, 0);
   assert(p2 == child);

   /* assert that child finished normally */
   assert(WIFEXITED(status));

   printf("FINAL VALUES:  8 bit %d,  16 bit %d,  32 bit %d,  64 bit %lld\n",
          (int)(*(signed char*)p8), (int)(*p16), *p32, *p64 );

   if (-74 == (int)(*(signed char*)p8) 
       && 32694 == (int)(*p16) 
       && 6913974 == *p32
       && (0LL == *p64 || 682858642110LL == *p64)) {
      printf("PASS\n");
   } else {
      printf("FAIL -- see source code for expected values\n");
   }

   printf("parent exits\n");

   return 0;
}
