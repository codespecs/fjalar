
/*--------------------------------------------------------------------*/
/*--- A header file used by both stage1 and stage2.                ---*/
/*---                                                        ume.h ---*/
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

#ifndef _COREGRIND_UME_H
#define _COREGRIND_UME_H

#include <elf.h>
#include <sys/types.h>

#include "basic_types.h"

/*------------------------------------------------------------*/
/*--- General stuff                                        ---*/
/*------------------------------------------------------------*/

extern
void foreach_map(int (*fn)(char *start, char *end,
			   const char *perm, off_t offset,
			   int maj, int min, int ino, void* extra),
                 void* extra);

/* Jump to 'dst', but first set the stack pointer to 'stack'.  Also,
   clear all the integer registers before entering 'dst'.  It's
   important that the stack pointer is set to exactly 'stack' and not
   (eg) stack - apparently_harmless_looking_small_offset.  Basically
   because the code at 'dst' might be wanting to scan the area above
   'stack' (viz, the auxv array), and putting spurious words on the
   stack confuses it.
*/
extern
__attribute__((noreturn))
void jump_and_switch_stacks ( Addr stack, Addr dst );


/* Call f(arg1), but first switch stacks, using 'stack' as the new
   stack, and use 'retaddr' as f's return-to address.  Also, clear all
   the integer registers before entering f.*/
extern
__attribute__((noreturn))
void call_on_new_stack_0_1 ( Addr stack,
			     Addr retaddr,
			     void (*f)(Word),
                             Word arg1 );


/*------------------------------------------------------------*/
/*--- Loading ELF files                                    ---*/
/*------------------------------------------------------------*/

// Info needed to load and run a program.  IN/INOUT/OUT refers to the
// inputs/outputs of do_exec().
struct exeinfo
{
   Addr map_base;       // IN: if non-zero, base address of mappings
   char** argv;         // IN: the original argv

   Addr exe_base;       // INOUT: lowest (allowed) address of exe
   Addr exe_end;        // INOUT: highest (allowed) address

   Addr phdr;           // OUT: address phdr was mapped at
   int  phnum;          // OUT: number of phdrs
   Addr interp_base;    // OUT: where interpreter (ld.so) was mapped
   Addr entry;          // OUT: entrypoint in main executable
   Addr init_eip;       // OUT: initial eip
   Addr brkbase;        // OUT: base address of brk segment

   // These are the extra args added by #! scripts
   char*  interp_name;  // OUT: the interpreter name
   char*  interp_args;  // OUT: the args for the interpreter
};

// Does everything short of actually running 'exe': finds the file,
// checks execute permissions, sets up interpreter if program is a script, 
// reads headers, maps file into memory, and returns important info about
// the program.
extern int do_exec(const char *exe, struct exeinfo *info);

/*------------------------------------------------------------*/
/*--- Finding and dealing with auxv                        ---*/
/*------------------------------------------------------------*/

struct ume_auxv
{
   Word a_type;
   union {
      void *a_ptr;
      Word a_val;
   } u;
};

extern struct ume_auxv *find_auxv(UWord* orig_esp);

/* Our private auxv entries */
#define AT_UME_PADFD	0xff01	/* padding file fd */
#define AT_UME_EXECFD	0xff02	/* stage1 executable fd */

#endif /* _COREGRIND_UME_H */

/*--------------------------------------------------------------------*/
/*--- end                                                    ume.h ---*/
/*--------------------------------------------------------------------*/
