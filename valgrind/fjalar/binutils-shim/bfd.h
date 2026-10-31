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

/* Fjalar's replacement for Binutils' bfd.h.

   The copies of Binutils files use only a few of the definitions in bfd.h,
   and Fjalar does not link with the BFD library.  This file defines those
   few, so that Fjalar does not depend on the bfd.h of the installed
   Binutils, whose version usually differs from that of the copies.  If a
   newer version of a copy uses a definition that this file lacks,
   compilation fails; then add the definition, from the bfd.h (generated
   from bfd/bfd-in2.h) of the same Binutils version as the copies.  See
   sysdep.h in this directory.  */

#ifndef FJALAR_BINUTILS_BFD_H
#define FJALAR_BINUTILS_BFD_H

#include "ansidecl.h"
#include <stdint.h>
#include <stdbool.h>

#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"

/* A 64-bit BFD, which can read both 32-bit and 64-bit ELF files.  */
#ifndef BFD64
#define BFD64
#endif

/* bucomm.h declares functions that take a pointer to one.  Nothing uses
   its definition.  */
struct stat;

/* elfcomm.h and dwarf.h use it.  Binutils' sysdep.h defines it, as long
   long if that is wider than long, but Fjalar's own files include those
   headers without sysdep.h.  Every file that includes them includes this
   file first.  */
#define HOST_WIDEST_INT long

typedef struct bfd bfd;
typedef struct bfd_section asection;

typedef uint64_t bfd_vma;
typedef int64_t bfd_signed_vma;
typedef uint64_t bfd_size_type;
typedef unsigned char bfd_byte;
typedef int64_t file_ptr;
typedef uint64_t ufile_ptr;
typedef unsigned int flagword;

/* The printf length modifier of bfd_vma.  */
#ifdef __LP64__
#define BFD_VMA_FMT "l"
#else
#define BFD_VMA_FMT "ll"
#endif

#define fprintf_vma(f,x) fprintf (f, "%016" BFD_VMA_FMT "x", x)
#define sprintf_vma(s,x) sprintf (s, "%016" BFD_VMA_FMT "x", x)
#define printf_vma(x) fprintf_vma(stdout,x)

/* dwarf.h declares a function that takes this type.  */
enum bfd_architecture
{
  bfd_arch_unknown
};

/* Return TRUE if the start of STR matches PREFIX, FALSE otherwise.  */
static inline bool
startswith (const char *str, const char *prefix)
{
  return VG_(strncmp) (str, prefix, VG_(strlen) (prefix)) == 0;
}

#endif /* FJALAR_BINUTILS_BFD_H */
