
/*--------------------------------------------------------------------*/
/*--- Entirely standalone libc stuff.                 m_libcbase.c ---*/
/*--------------------------------------------------------------------*/
 
/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Julian Seward 
      jseward@acm.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_core_basics.h"
#include "pub_core_libcbase.h"

/* ---------------------------------------------------------------------
   Char functions.
   ------------------------------------------------------------------ */

Bool VG_(isspace) ( Char c )
{
   return (c == ' '  || c == '\n' || c == '\t' || 
           c == '\f' || c == '\v' || c == '\r');
}

Bool VG_(isdigit) ( Char c )
{
   return (c >= '0' && c <= '9');
}

/* ---------------------------------------------------------------------
   Converting strings to numbers
   ------------------------------------------------------------------ */

Long VG_(atoll) ( Char* str )
{
   Bool neg = False;
   Long n = 0;
   if (*str == '-') { str++; neg = True; };
   while (*str >= '0' && *str <= '9') {
      n = 10*n + (Long)(*str - '0');
      str++;
   }
   if (neg) n = -n;
   return n;
}

Long VG_(atoll36) ( Char* str )
{
   Bool neg = False;
   Long n = 0;
   if (*str == '-') { str++; neg = True; };
   while (True) {
      Char c = *str;
      if (c >= '0' && c <= (Char)'9') {
         n = 36*n + (Long)(c - '0');
      }
      else 
      if (c >= 'A' && c <= (Char)'Z') {
         n = 36*n + (Long)((c - 'A') + 10);
      }
      else 
      if (c >= 'a' && c <= (Char)'z') {
         n = 36*n + (Long)((c - 'a') + 10);
      }
      else {
	break;
      }
      str++;
   }
   if (neg) n = -n;
   return n;
}

/* ---------------------------------------------------------------------
   String functions
   ------------------------------------------------------------------ */

Int VG_(strlen) ( const Char* str )
{
   Int i = 0;
   while (str[i] != 0) i++;
   return i;
}

Char* VG_(strcat) ( Char* dest, const Char* src )
{
   Char* dest_orig = dest;
   while (*dest) dest++;
   while (*src) *dest++ = *src++;
   *dest = 0;
   return dest_orig;
}

Char* VG_(strncat) ( Char* dest, const Char* src, SizeT n )
{
   Char* dest_orig = dest;
   while (*dest) dest++;
   while (*src && n > 0) { *dest++ = *src++; n--; }
   *dest = 0;
   return dest_orig;
}

Char* VG_(strpbrk) ( const Char* s, const Char* accept )
{
   const Char* a;
   while (*s) {
      a = accept;
      while (*a)
         if (*a++ == *s)
            return (Char *) s;
      s++;
   }
   return NULL;
}

Char* VG_(strcpy) ( Char* dest, const Char* src )
{
   Char* dest_orig = dest;
   while (*src) *dest++ = *src++;
   *dest = 0;
   return dest_orig;
}

/* Copy bytes, not overrunning the end of dest and always ensuring
   zero termination. */
void VG_(strncpy_safely) ( Char* dest, const Char* src, SizeT ndest )
{
   Int i = 0;
   while (True) {
      dest[i] = 0;
      if (src[i] == 0) return;
      if (i >= ndest-1) return;
      dest[i] = src[i];
      i++;
   }
}

Char* VG_(strncpy) ( Char* dest, const Char* src, SizeT ndest )
{
   Int i = 0;
   while (True) {
      if (i >= ndest) return dest;     /* reached limit */
      dest[i] = src[i];
      if (src[i++] == 0) {
         /* reached NUL;  pad rest with zeroes as required */
         while (i < ndest) dest[i++] = 0;
         return dest;
      }
   }
}

Int VG_(strcmp) ( const Char* s1, const Char* s2 )
{
   while (True) {
      if (*s1 == 0 && *s2 == 0) return 0;
      if (*s1 == 0) return -1;
      if (*s2 == 0) return 1;

      if (*(UChar*)s1 < *(UChar*)s2) return -1;
      if (*(UChar*)s1 > *(UChar*)s2) return 1;

      s1++; s2++;
   }
}

static Bool isterm ( Char c )
{
   return ( VG_(isspace)(c) || 0 == c );
}

Int VG_(strcmp_ws) ( const Char* s1, const Char* s2 )
{
   while (True) {
      if (isterm(*s1) && isterm(*s2)) return 0;
      if (isterm(*s1)) return -1;
      if (isterm(*s2)) return 1;

      if (*(UChar*)s1 < *(UChar*)s2) return -1;
      if (*(UChar*)s1 > *(UChar*)s2) return 1;

      s1++; s2++;
   }
}

Int VG_(strncmp) ( const Char* s1, const Char* s2, SizeT nmax )
{
   Int n = 0;
   while (True) {
      if (n >= nmax) return 0;
      if (*s1 == 0 && *s2 == 0) return 0;
      if (*s1 == 0) return -1;
      if (*s2 == 0) return 1;

      if (*(UChar*)s1 < *(UChar*)s2) return -1;
      if (*(UChar*)s1 > *(UChar*)s2) return 1;

      s1++; s2++; n++;
   }
}

Int VG_(strncmp_ws) ( const Char* s1, const Char* s2, SizeT nmax )
{
   Int n = 0;
   while (True) {
      if (n >= nmax) return 0;
      if (isterm(*s1) && isterm(*s2)) return 0;
      if (isterm(*s1)) return -1;
      if (isterm(*s2)) return 1;

      if (*(UChar*)s1 < *(UChar*)s2) return -1;
      if (*(UChar*)s1 > *(UChar*)s2) return 1;

      s1++; s2++; n++;
   }
}

Char* VG_(strstr) ( const Char* haystack, Char* needle )
{
   Int n; 
   if (haystack == NULL)
      return NULL;
   n = VG_(strlen)(needle);
   while (True) {
      if (haystack[0] == 0) 
         return NULL;
      if (VG_(strncmp)(haystack, needle, n) == 0) 
         return (Char*)haystack;
      haystack++;
   }
}

Char* VG_(strchr) ( const Char* s, Char c )
{
   while (True) {
      if (*s == c) return (Char*)s;
      if (*s == 0) return NULL;
      s++;
   }
}

Char* VG_(strrchr) ( const Char* s, Char c )
{
   Int n = VG_(strlen)(s);
   while (--n > 0) {
      if (s[n] == c) return (Char*)s + n;
   }
   return NULL;
}

/* ---------------------------------------------------------------------
   A simple string matching routine, purloined from Hugs98.
      '*'    matches any sequence of zero or more characters
      '?'    matches any single character exactly 
      '\c'   matches the character c only (ignoring special chars)
      c      matches the character c only
   ------------------------------------------------------------------ */

/* Keep track of recursion depth. */
static Int recDepth;

// Nb: vg_assert disabled because we can't use it from this module...
static Bool string_match_wrk ( const Char* pat, const Char* str )
{
   //vg_assert(recDepth >= 0 && recDepth < 500);
   recDepth++;
   for (;;) {
      switch (*pat) {
      case '\0':recDepth--;
                return (*str=='\0');
      case '*': do {
                   if (string_match_wrk(pat+1,str)) {
                      recDepth--;
                      return True;
                   }
                } while (*str++);
                recDepth--;
                return False;
      case '?': if (*str++=='\0') {
                   recDepth--;
                   return False;
                }
                pat++;
                break;
      case '\\':if (*++pat == '\0') {
                   recDepth--;
                   return False; /* spurious trailing \ in pattern */
                }
                /* falls through to ... */
      default : if (*pat++ != *str++) {
                   recDepth--;
                   return False;
                }
                break;
      }
   }
}

Bool VG_(string_match) ( const Char* pat, const Char* str )
{
   Bool b;
   recDepth = 0;
   b = string_match_wrk ( pat, str );
   //vg_assert(recDepth == 0);
   /*
   VG_(printf)("%s   %s   %s\n",
	       b?"TRUE ":"FALSE", pat, str);
   */
   return b;
}


/* ---------------------------------------------------------------------
   mem* functions
   ------------------------------------------------------------------ */

void* VG_(memcpy) ( void *dest, const void *src, SizeT sz )
{
   const UChar* s  = (const UChar*)src;
         UChar* d  =       (UChar*)dest;
   const UInt*  sI = (const UInt*)src;
         UInt*  dI =       (UInt*)dest;

   if (VG_IS_4_ALIGNED(dI) && VG_IS_4_ALIGNED(sI)) {
      while (sz >= 16) {
         dI[0] = sI[0];
         dI[1] = sI[1];
         dI[2] = sI[2];
         dI[3] = sI[3];
         sz -= 16;
         dI += 4;
         sI += 4;
      }
      if (sz == 0) 
         return dest;
      while (sz >= 4) {
         dI[0] = sI[0];
         sz -= 4;
         dI += 1;
         sI += 1;
      }
      if (sz == 0) 
         return dest;
      s = (const UChar*)sI;
      d = (UChar*)dI;
   }

   while (sz--)
      *d++ = *s++;

   return dest;
}

void* VG_(memset) ( void *dest, Int c, SizeT sz )
{
   Char *d = (Char *)dest;
   while (sz >= 4) {
      d[0] = c;
      d[1] = c;
      d[2] = c;
      d[3] = c;
      d += 4;
      sz -= 4;
   }
   while (sz > 0) {
      d[0] = c;
      d++;
      sz--;
   }
   return dest;
}

Int VG_(memcmp) ( const void* s1, const void* s2, SizeT n )
{
   Int res;
   const UChar *p1 = s1;
   const UChar *p2 = s2;
   UChar a0;
   UChar b0;

   while (n != 0) {
      a0 = p1[0];
      b0 = p2[0];
      p1 += 1;
      p2 += 1;
      res = a0 - b0;
      if (res != 0)
         return res;
      n -= 1;
   }
   return 0;
}

/* ---------------------------------------------------------------------
   Misc useful functions
   ------------------------------------------------------------------ */

/* Returns the base-2 logarithm of x.  Returns -1 if x is not a power of two. */
Int VG_(log2) ( Int x ) 
{
   Int i;
   /* Any more than 32 and we overflow anyway... */
   for (i = 0; i < 32; i++) {
      if (1 << i == x) return i;
   }
   return -1;
}


// Generic shell sort.  Like stdlib.h's qsort().
void VG_(ssort)( void* base, SizeT nmemb, SizeT size,
                 Int (*compar)(void*, void*) )
{
   Int   incs[14] = { 1, 4, 13, 40, 121, 364, 1093, 3280,
                      9841, 29524, 88573, 265720,
                      797161, 2391484 };
   Int   lo = 0;
   Int   hi = nmemb-1;
   Int   i, j, h, bigN, hp;

   bigN = hi - lo + 1; if (bigN < 2) return;
   hp = 0; while (hp < 14 && incs[hp] < bigN) hp++; hp--;

   #define SORT \
   for ( ; hp >= 0; hp--) { \
      h = incs[hp]; \
      for (i = lo + h; i <= hi; i++) { \
         ASSIGN(v,0, a,i); \
         j = i; \
         while (COMPAR(a,(j-h), v,0) > 0) { \
            ASSIGN(a,j, a,(j-h)); \
            j = j - h; \
            if (j <= (lo + h - 1)) break; \
         } \
         ASSIGN(a,j, v,0); \
      } \
   }

   // Specialised cases
   if (sizeof(ULong) == size) {

      #define ASSIGN(dst, dsti, src, srci) \
      (dst)[(dsti)] = (src)[(srci)];      
      
      #define COMPAR(dst, dsti, src, srci) \
      compar( (void*)(& (dst)[(dsti)]), (void*)(& (src)[(srci)]) )

      ULong* a = (ULong*)base;
      ULong  v[1];

      SORT;

   } else if (sizeof(UInt) == size) {

      UInt* a = (UInt*)base;
      UInt  v[1];

      SORT;

   } else if (sizeof(UShort) == size) {
      UShort* a = (UShort*)base;
      UShort  v[1];

      SORT;

   } else if (sizeof(UChar) == size) {
      UChar* a = (UChar*)base;
      UChar  v[1];

      SORT;

      #undef ASSIGN
      #undef COMPAR

   // General case
   } else {
      char* a = base;
      char  v[size];      // will be at least 'size' bytes

      #define ASSIGN(dst, dsti, src, srci) \
      VG_(memcpy)( &dst[size*(dsti)], &src[size*(srci)], size );

      #define COMPAR(dst, dsti, src, srci) \
      compar( &dst[size*(dsti)], &src[size*(srci)] )

      SORT;

      #undef ASSIGN
      #undef COMPAR
   }
   #undef SORT
}

// This random number generator is based on the one suggested in Kernighan
// and Ritchie's "The C Programming Language".

// A pseudo-random number generator returning a random UInt.  If pSeed
// is NULL, it uses its own seed, which starts at zero.  If pSeed is
// non-NULL, it uses and updates whatever pSeed points at.

static UInt seed = 0;

UInt VG_(random)( /*MOD*/UInt* pSeed )
{
   if (pSeed == NULL) 
      pSeed = &seed;

   *pSeed = (1103515245 * *pSeed + 12345);
   return *pSeed;
}

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/

