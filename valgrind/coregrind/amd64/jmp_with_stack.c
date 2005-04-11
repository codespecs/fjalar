
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

#include "ume.h"


#define ZERO_ALL_INT_REGS \
   "   movq $0, %rax\n"  \
   "   movq $0, %rbx\n"  \
   "   movq $0, %rcx\n"  \
   "   movq $0, %rdx\n"  \
   "   movq $0, %rsi\n"  \
   "   movq $0, %rdi\n"  \
   "   movq $0, %rbp\n"  \
   "   movq $0, %r8\n"   \
   "   movq $0, %r9\n"   \
   "   movq $0, %r10\n"  \
   "   movq $0, %r11\n"  \
   "   movq $0, %r12\n"  \
   "   movq $0, %r13\n"  \
   "   movq $0, %r14\n"  \
   "   movq $0, %r15\n"


/* Jump to 'dst', but first set the stack pointer to 'stack'.  Also,
   clear all the integer registers before entering 'dst'.  It's
   important that the stack pointer is set to exactly 'stack' and not
   (eg) stack - apparently_harmless_looking_small_offset.  Basically
   because the code at 'dst' might be wanting to scan the area above
   'stack' (viz, the auxv array), and putting spurious words on the
   stack confuses it.
*/
/*
__attribute__((noreturn))
void jump_and_switch_stacks ( Addr stack, Addr dst );

  %rdi == stack
  %rsi == dst
*/
asm(
".global jump_and_switch_stacks\n"
"jump_and_switch_stacks:\n"
"   movq   %rdi, %rsp\n"  /* set stack */
"   pushq  %rsi\n"        /* f to stack*/
    ZERO_ALL_INT_REGS
"   ret\n"                /* jump to f */
"   ud2\n"                /* should never get here */
);



/* Call f(arg1), but first switch stacks, using 'stack' as the new
   stack, and use 'retaddr' as f's return-to address.  Also, clear all
   the integer registers before entering f.*/
/*
__attribute__((noreturn))
void call_on_new_stack_0_1 ( Addr stack,
			     Addr retaddr,
			     void (*f)(Word),
                             Word arg1 );
   %rdi == stack
   %rsi == retaddr
   %rdx == f
   %rcx == arg1
*/
asm(
".global call_on_new_stack_0_1\n"
"call_on_new_stack_0_1:\n"
"   movq   %rdi, %rsp\n"  /* set stack */
"   pushq  %rsi\n"        /* retaddr to stack */
"   pushq  %rdx\n"        /* f to stack*/
"   pushq  %rcx\n"        /* arg1 to stack*/
    ZERO_ALL_INT_REGS
"   popq   %rdi\n"        /* arg1 to correct arg reg */
"   ret\n"                /* jump to f */
"   ud2\n"                /* should never get here */
);


#undef ZERO_ALL_INT_REGS
