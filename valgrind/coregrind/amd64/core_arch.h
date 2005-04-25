
/*--------------------------------------------------------------------*/
/*--- Arch-specific stuff for the core.          amd64/core_arch.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Nicholas Nethercote
      njn25@cam.ac.uk

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

#ifndef __AMD64_CORE_ARCH_H
#define __AMD64_CORE_ARCH_H

#include "core_arch_asm.h"    // arch-specific asm  stuff
#include "tool_arch.h"        // arch-specific tool stuff

#include "libvex_guest_amd64.h"

/* ---------------------------------------------------------------------
   Basic properties
   ------------------------------------------------------------------ */

#define VGA_ELF_ENDIANNESS     ELFDATA2LSB
#define VGA_ELF_MACHINE        EM_X86_64
#define VGA_ELF_CLASS          ELFCLASS64

#define VGA_WORD_SIZE         8

/* ---------------------------------------------------------------------
   Interesting registers
   ------------------------------------------------------------------ */

// Vex field names
#define VGA_INSTR_PTR         guest_RIP
#define VGA_STACK_PTR         guest_RSP
#define VGA_FRAME_PTR         guest_RBP

#define VGA_CLREQ_ARGS        guest_RAX
#define VGA_CLREQ_RET         guest_RDX

// Register numbers, for vg_symtab2.c
#define VGA_R_STACK_PTR       4
#define VGA_R_FRAME_PTR       5

// Stack frame layout and linkage
#define VGA_FIRST_STACK_FRAME(rbp)     (rbp)
#define VGA_STACK_FRAME_RET(rbp)       (((UWord*)rbp)[1])
#define VGA_STACK_FRAME_NEXT(rbp)      (((UWord*)rbp)[0])

// Get stack pointer and frame pointer
#define VGA_GET_REAL_STACK_PTR(lval) do {   \
   asm("movq %%rsp, %0" : "=r" (lval));      \
} while (0)

#define VGA_GET_REAL_FRAME_PTR(lval) do {   \
   asm("movq %%rbp, %0" : "=r" (lval));      \
} while (0)


/* ---------------------------------------------------------------------
   Architecture-specific part of a ThreadState
   ------------------------------------------------------------------ */

// Architecture-specific part of a ThreadState
// XXX: eventually this should be made abstract, ie. the fields not visible
//      to the core...
typedef 
   struct {
      /* --- BEGIN vex-mandated guest state --- */

      /* Saved machine context. */
      VexGuestAMD64State vex;

      /* Saved shadow context. */
      VexGuestAMD64State vex_shadow;

      /* Spill area. */
      UChar vex_spill[LibVEX_N_SPILL_BYTES];

      /* --- END vex-mandated guest state --- */
   } 
   ThreadArchState;

typedef VexGuestAMD64State VexGuestArchState;

/* ---------------------------------------------------------------------
   libpthread stuff
   ------------------------------------------------------------------ */

// ToDo XXX???  not at all sure about this...
struct _ThreadArchAux {
  //   void*         tls_data;
  //   int           tls_segment;
  //   unsigned long sysinfo;
};

/* ---------------------------------------------------------------------
   Miscellaneous constants
   ------------------------------------------------------------------ */

// Valgrind's signal stack size, in words.
#define VGA_SIGSTACK_SIZE_W   10000

// Valgrind's stack size, in words.
#define VGA_STACK_SIZE_W      16384

// Base address of client address space.
#define VGA_CLIENT_BASE       0x0ul


#endif   // __AMD64_CORE_ARCH_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/

