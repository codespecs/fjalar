
/*--------------------------------------------------------------------*/
/*--- Header included by every tool C file.      pub_tool_basics.h ---*/
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

#ifndef __PUB_TOOL_BASICS_H
#define __PUB_TOOL_BASICS_H

//--------------------------------------------------------------------
// PURPOSE: This header should be imported by every single C file in
// tools.  It contains the basic types and other things needed everywhere.
// There is no corresponding C file because this isn't a module
// containing executable code, it's all just declarations.
//--------------------------------------------------------------------

/* ---------------------------------------------------------------------
   Other headers to include
   ------------------------------------------------------------------ */

// VEX defines Char, UChar, Short, UShort, Int, UInt, Long, ULong,
// Addr32, Addr64, HWord, HChar, Bool, False and True.
#include "libvex_basictypes.h"

// For the VG_() macro
#include "pub_tool_basics_asm.h"

// For varargs types
#include <stdarg.h>

// Kernel types.  Might as well have them here, they're used so broadly
// (eg. in pub_core_threadstate.h).
#if defined(VGO_linux)
#  include "vki-linux.h"
#else
#  error Unknown OS
#endif

/* ---------------------------------------------------------------------
   builtin types
   ------------------------------------------------------------------ */

// By choosing the right types, we can get these right for 32-bit and 64-bit
// platforms without having to do any conditional compilation or anything.
// 
// Size in bits on:                          32-bit archs   64-bit archs
//                                           ------------   ------------
typedef unsigned long          UWord;     // 32             64

typedef signed long            Word;      // 32             64

typedef UWord                  Addr;      // 32             64
typedef UWord                  AddrH;     // 32             64

typedef UWord                  SizeT;     // 32             64
typedef  Word                 SSizeT;     // 32             64

typedef  Word                   OffT;     // 32             64

typedef ULong                 Off64T;     // 64             64

#if !defined(NULL)
#  define NULL ((void*)0)
#endif

/* ---------------------------------------------------------------------
   non-builtin types
   ------------------------------------------------------------------ */

// These probably shouldn't be here, but moving them to their logical
// modules results in a lot more #includes...

/* ThreadIds are simply indices into the VG_(threads)[] array. */
typedef UInt ThreadId;

/* An abstraction of syscall return values.
   When .isError == False, val holds the return value.
   When .isError == True,  val holds the error code.
*/
typedef struct { 
   UWord val;
   Bool  isError;
}
SysRes;

/* ---------------------------------------------------------------------
   Miscellaneous (word size, endianness, regparmness, stringification)
   ------------------------------------------------------------------ */

/* Word size: this is going to be either 4 or 8. */
// It should probably be in m_machine.
#define VG_WORDSIZE VEX_HOST_WORDSIZE

/* Endianness */
#undef VG_BIGENDIAN
#undef VG_LITTLEENDIAN

#if defined(VGA_x86) || defined(VGA_amd64)
#  define VG_LITTLEENDIAN 1
#elif defined(VGA_ppc32) || defined(VGA_ppc64)
#  define VG_BIGENDIAN 1
#endif

/* Regparmness */
#if defined(VGA_x86)
#  define VG_REGPARM(n)            __attribute__((regparm(n)))
#elif defined(VGA_amd64) || defined(VGA_ppc32) || defined(VGA_ppc64)
#  define VG_REGPARM(n)            /* */
#else
#  error Unknown arch
#endif

/* Macro games */
#define VG_STRINGIFZ(__str)  #__str
#define VG_STRINGIFY(__str)  VG_STRINGIFZ(__str)

#endif /* __PUB_TOOL_BASICS_H */

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
