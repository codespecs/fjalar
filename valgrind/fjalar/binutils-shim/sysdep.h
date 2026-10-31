/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* Fjalar's replacement for Binutils' binutils/sysdep.h.

   readelf.c, dwarf.c, and elfcomm.c are copies of Binutils files, and they
   include sysdep.h first.  This file provides what they need from it, in a
   form that works in a Valgrind tool, so that the copies need fewer
   changes.  A Valgrind tool cannot call the C library, so this file maps
   each C library function that the copies call to its Valgrind equivalent.
   The macros are function-like, so they affect only a use of the name that
   is followed by "(".  They do not affect VG_(malloc), but they do affect a
   call through a structure field of the same name, such as p->free (q),
   which then fails to compile.  A use of the name that is not a call, such
   as passing free as an argument, refers to the C library function, which
   a Valgrind tool cannot use.

   The directory that contains this file precedes "include" on the include
   path, so this file and the others in the directory hide the Binutils
   headers of the same name.  The directory is not under "include", because
   merge-binutils.sh treats every file there as a copy of a Binutils file.  */

#ifndef FJALAR_BINUTILS_SYSDEP_H
#define FJALAR_BINUTILS_SYSDEP_H

#include "my_libc.h"
#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"
#include <limits.h>

#include "ansidecl.h"

#define ngettext(Msgid1, Msgid2, n) \
  (n == 1 ? Msgid1 : Msgid2)

/* C library functions.  */

#define malloc(size) VG_(malloc) (__FILE__, size)
#define calloc(nmemb, size) VG_(calloc) (__FILE__, nmemb, size)
#define realloc(ptr, size) VG_(realloc) (__FILE__, ptr, size)
#define strdup(s) VG_(strdup) (__FILE__, s)
#define free(ptr) VG_(free) (ptr)

#define memcmp(s1, s2, n) VG_(memcmp) (s1, s2, n)
#define memcpy(dest, src, n) VG_(memcpy) (dest, src, n)
#define memmove(dest, src, n) VG_(memmove) (dest, src, n)
#define memset(s, c, n) VG_(memset) (s, c, n)
#define strcat(dest, src) VG_(strcat) (dest, src)
#define strchr(s, c) VG_(strchr) (s, c)
#define strcmp(s1, s2) VG_(strcmp) (s1, s2)
#define strcpy(dest, src) VG_(strcpy) (dest, src)
#define strlen(s) VG_(strlen) (s)
#define strncmp(s1, s2, n) VG_(strncmp) (s1, s2, n)
#define strncpy(dest, src, n) VG_(strncpy) (dest, src, n)
#define strnlen(s, n) VG_(strnlen) (s, n)
#define strrchr(s, c) VG_(strrchr) (s, c)
#define strstr(haystack, needle) VG_(strstr) (haystack, needle)

#define abort() my_abort ()

#endif /* FJALAR_BINUTILS_SYSDEP_H */
