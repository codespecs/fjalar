
/*--------------------------------------------------------------------*/
/*--- Machine-related things.                   pub_core_machine.h ---*/
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

#ifndef __PUB_CORE_MACHINE_H
#define __PUB_CORE_MACHINE_H

//--------------------------------------------------------------------
// PURPOSE: This module contains code related to the particular
// architecture, things like accessing guest state, endianness, word size,
// etc.
//--------------------------------------------------------------------

#include "pub_tool_machine.h"

#if defined(VGA_x86)
#  define VG_ELF_DATA2XXX     ELFDATA2LSB
#  define VG_ELF_MACHINE      EM_386
#  define VG_ELF_CLASS        ELFCLASS32
#elif defined(VGA_amd64)
#  define VG_ELF_DATA2XXX     ELFDATA2LSB
#  define VG_ELF_MACHINE      EM_X86_64
#  define VG_ELF_CLASS        ELFCLASS64
#elif defined(VGA_ppc32)
#  define VG_ELF_DATA2XXX     ELFDATA2MSB
#  define VG_ELF_MACHINE      EM_PPC
#  define VG_ELF_CLASS        ELFCLASS32
#elif defined(VGA_ppc64)
#  define VG_ELF_DATA2XXX     ELFDATA2MSB
#  define VG_ELF_MACHINE      EM_PPC64
#  define VG_ELF_CLASS        ELFCLASS64
#else
#  error Unknown arch
#endif

#if defined(VGA_x86)
#  define VG_INSTR_PTR        guest_EIP
#  define VG_STACK_PTR        guest_ESP
#  define VG_FRAME_PTR        guest_EBP
#elif defined(VGA_amd64)
#  define VG_INSTR_PTR        guest_RIP
#  define VG_STACK_PTR        guest_RSP
#  define VG_FRAME_PTR        guest_RBP
#elif defined(VGA_ppc32)
#  define VG_INSTR_PTR        guest_CIA
#  define VG_STACK_PTR        guest_GPR1
#  define VG_FRAME_PTR        guest_GPR1   // No frame ptr for PPC
#elif defined(VGA_ppc64)
#  define VG_INSTR_PTR        guest_CIA
#  define VG_STACK_PTR        guest_GPR1
#  define VG_FRAME_PTR        guest_GPR1   // No frame ptr for PPC
#else
#  error Unknown arch
#endif


// Offsets for the Vex state
#define VG_O_STACK_PTR        (offsetof(VexGuestArchState, VG_STACK_PTR))


//-------------------------------------------------------------
/* Details about the capabilities of the underlying (host) CPU.  These
   details are acquired by (1) enquiring with the CPU at startup, or
   (2) from the AT_SYSINFO entries the kernel gave us (ppc cache
   line size).  It's a bit nasty in the sense that there's no obvious
   way to stop uses of some of this info before it's ready to go.

   Current dependencies are:

   x86:   initially:  call VG_(machine_get_hwcaps)

          then safe to use VG_(machine_get_VexArchInfo) 
                       and VG_(machine_x86_have_mxcsr)
   -------------
   amd64: initially:  call VG_(machine_get_hwcaps)

          then safe to use VG_(machine_get_VexArchInfo) 
   -------------
   ppc32: initially:  call VG_(machine_get_hwcaps)
                      call VG_(machine_ppc32_set_clszB)

          then safe to use VG_(machine_get_VexArchInfo) 
                       and VG_(machine_ppc32_has_FP)
                       and VG_(machine_ppc32_has_VMX)
   -------------
   ppc64: initially:  call VG_(machine_get_hwcaps)
                      call VG_(machine_ppc64_set_clszB)

          then safe to use VG_(machine_get_VexArchInfo) 
                       and VG_(machine_ppc64_has_VMX)

   VG_(machine_get_hwcaps) may use signals (although it attempts to
   leave signal state unchanged) and therefore should only be
   called before m_main sets up the client's signal state.
*/

/* Determine what insn set and insn set variant the host has, and
   record it.  To be called once at system startup.  Returns False if
   this a CPU incapable of running Valgrind. */
extern Bool VG_(machine_get_hwcaps)( void );

/* Fetch host cpu info, as per above comment. */
extern void VG_(machine_get_VexArchInfo)( /*OUT*/VexArch*,
                                          /*OUT*/VexArchInfo* );

/* Notify host cpu cache line size, as per above comment. */
#if defined(VGA_ppc32)
extern void VG_(machine_ppc32_set_clszB)( Int );
#endif

#if defined(VGA_ppc64)
extern void VG_(machine_ppc64_set_clszB)( Int );
#endif

/* X86: set to 1 if the host is able to do {ld,st}mxcsr (load/store
   the SSE control/status register), else zero.  Is referenced from
   assembly code, so do not change from a 32-bit int. */
#if defined(VGA_x86)
extern UInt VG_(machine_x86_have_mxcsr);
#endif

/* PPC32: set to 1 if FP instructions are supported in user-space,
   else 0.  Is referenced from assembly code, so do not change from a
   32-bit int. */
#if defined(VGA_ppc32)
extern UInt VG_(machine_ppc32_has_FP);
#endif

/* PPC32: set to 1 if Altivec instructions are supported in
   user-space, else 0.  Is referenced from assembly code, so do not
   change from a 32-bit int. */
#if defined(VGA_ppc32)
extern UInt VG_(machine_ppc32_has_VMX);
#endif

/* PPC64: set to 1 if Altivec instructions are supported in
   user-space, else 0.  Is referenced from assembly code, so do not
   change from a 64-bit int. */
#if defined(VGA_ppc64)
extern ULong VG_(machine_ppc64_has_VMX);
#endif

#endif   // __PUB_CORE_MACHINE_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
