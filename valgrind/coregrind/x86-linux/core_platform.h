
/*--------------------------------------------------------------------*/
/*--- Platform-specific stuff for the core.                        ---*/
/*---                                    x86-linux/core_platform.h ---*/
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

#ifndef __X86_LINUX_CORE_PLATFORM_H
#define __X86_LINUX_CORE_PLATFORM_H

//#include "core_platform_asm.h"    // platform-specific asm  stuff
//#include "platform_arch.h"        // platform-specific tool stuff

/* ---------------------------------------------------------------------
   Dealing with registers
   ------------------------------------------------------------------ */

// Accessors for the ThreadArchState
#define VGP_SYSCALL_NUM       guest_EAX
#define VGP_SYSCALL_ARG1      guest_EBX
#define VGP_SYSCALL_ARG2      guest_ECX
#define VGP_SYSCALL_ARG3      guest_EDX
#define VGP_SYSCALL_ARG4      guest_ESI
#define VGP_SYSCALL_ARG5      guest_EDI
#define VGP_SYSCALL_ARG6      guest_EBP
#define VGP_SYSCALL_RET       guest_EAX

// Setting a syscall result
#define VGP_SET_SYSCALL_RESULT(regs, val)    ((regs).vex.guest_EAX = (val))

// Setting thread regs and shadow regs from within the core
#define SET_SYSCALL_RETVAL(zztid, zzval) \
   SET_THREAD_REG(zztid, zzval, SYSCALL_RET, post_reg_write, \
                  Vg_CoreSysCall, zztid, O_SYSCALL_RET, sizeof(UWord))

/* ---------------------------------------------------------------------
   Exports of vg_ldt.c
   ------------------------------------------------------------------ */

// XXX: eventually all these should be x86-private, and not visible to the
// core (except maybe do_useseg()?)

/* Simulate the modify_ldt syscall. */
extern Int VG_(sys_modify_ldt) ( ThreadId tid,
                                 Int func, void* ptr, UInt bytecount );

/* Simulate the {get,set}_thread_area syscalls. */
extern Int VG_(sys_set_thread_area) ( ThreadId tid,
                                      vki_modify_ldt_t* info );
extern Int VG_(sys_get_thread_area) ( ThreadId tid,
                                      vki_modify_ldt_t* info );

/* Called from generated code.  Given a segment selector and a virtual
   address, return a linear address, and do limit checks too. */
extern Addr VG_(do_useseg) ( UInt seg_selector, Addr virtual_addr );

/* ---------------------------------------------------------------------
   ucontext stuff
   ------------------------------------------------------------------ */

#define VGP_UCONTEXT_INSTR_PTR(uc)     ((uc)->uc_mcontext.eip)
#define VGP_UCONTEXT_STACK_PTR(uc)     ((uc)->uc_mcontext.esp)
#define VGP_UCONTEXT_FRAME_PTR(uc)     ((uc)->uc_mcontext.ebp)
#define VGP_UCONTEXT_SYSCALL_NUM(uc)   ((uc)->uc_mcontext.eax)
#define VGP_UCONTEXT_SYSCALL_RET(uc)   ((uc)->uc_mcontext.eax)

/* ---------------------------------------------------------------------
   mmap() stuff
   ------------------------------------------------------------------ */

#define VGP_DO_MMAP(ret, start, length, prot, flags, fd, offset) {      \
   UWord __args[6];                                                     \
                                                                        \
   __args[0] = (UWord)(start);                                          \
   __args[1] = (length);                                                \
   __args[2] = (prot);                                                  \
   __args[3] = (flags);                                                 \
   __args[4] = (fd);                                                    \
   __args[5] = (offset);                                                \
                                                                        \
   ret = VG_(do_syscall1)(__NR_mmap, (UWord)(&(__args[0])) );           \
} while (0)

#define VGP_GET_MMAP_ARGS(tst, a1, a2, a3, a4, a5, a6) do {     \
   UInt *arg_block = (UInt*)SYSCALL_ARG1(tst->arch);            \
   PRE_MEM_READ( "old_mmap(args)", (Addr)arg_block, 6*sizeof(UWord) );\
   a1 = arg_block[0];                                           \
   a2 = arg_block[1];                                           \
   a3 = arg_block[2];                                           \
   a4 = arg_block[3];                                           \
   a5 = arg_block[4];                                           \
   a6 = arg_block[5];                                           \
} while (0)

/* ---------------------------------------------------------------------
   Inline asm for atomic operations for use with futexes
   Taken from futex-2.2/i386.h
   ------------------------------------------------------------------ */
/* (C) Matthew Kirkwood <matthew@hairy.beasts.org>
   (C) 2002 Rusty Russell IBM <rusty@rustcorp.com.au>
 */

/* Atomic dec: return new value. */
static __inline__ Int __futex_down(Int *counter)
{
   Int val;
   UChar eqz;

   /* Don't decrement if already negative. */
   val = *counter;
   if (val < 0)
      return val;

   /* Damn 386: no cmpxchg... */
   __asm__ __volatile__(
      "lock; decl %0; sete %1"
      :"=m" (*counter), "=qm" (eqz)
      :"m" (*counter) : "memory");

   /* We know if it's zero... */
   if (eqz) return 0;
   /* Otherwise, we have no way of knowing value.  Guess -1 (if
      we're wrong we'll spin). */
   return -1;
}

/* Atomic inc: return 1 if counter incremented from 0 to 1. */
static __inline__ Int __futex_up(Int *c)
{
   Int r = 1;

   /* This actually tests if result >= 1.  Damn 386. --RR */
   __asm__ __volatile__ (
      "	lock; incl %1\n"
      "	jg 1f\n"
      "	decl %0\n"
      "1:\n"
      : "=q"(r), "=m"(*c) : "0"(r)
      );
   return r;
}

/* Simple atomic increment. */
static __inline__ void __atomic_inc(Int *c)
{
   __asm__ __volatile__(
      "lock; incl %0"
      :"=m" (*c)
      :"m" (*c));
}


/* Commit the write, so it happens before we send the semaphore to
   anyone else */
static __inline__ void __futex_commit(void)
{
   /* Probably overkill, but some non-Intel clones support
      out-of-order stores, according to 2.5.5-pre1's
      linux/include/asm-i386/system.h */
   __asm__ __volatile__ ("lock; addl $0,0(%%esp)": : :"memory");
}

/* Use libc setjmp/longjmp.  longjmp must not restore signal mask
   state, but does need to pass though "val". */
#include <setjmp.h>       /* for jmp_buf         */

#define VGP_SETJMP(env)       setjmp(env)
#define VGP_LONGJMP(env, val) longjmp(env, val)

#endif   // __X86_LINUX_CORE_PLATFORM_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
