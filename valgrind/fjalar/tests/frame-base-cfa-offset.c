/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

// The function whose frame base frame-base-cfa-offset-test.sh rewrites to
// (DW_OP_call_frame_cfa; DW_OP_consts N; DW_OP_plus).  It is a compilation
// unit of its own, so that every DW_OP_fbreg offset in the generated assembly
// belongs to this function and the test can shift them all.  main is in
// frame-base-cfa-offset-main.c.  See frame-base-cfa-offset-test.sh.

// Unoptimized, cfa_offset stores its formal parameters in its stack frame,
// and their locations are offsets from the frame base.
//
// The names of the formal parameters are not arbitrary.  The longer frame
// base expression needs three more bytes than the one GCC emits, and the test
// pays for them by shortening "abc" to "a" and "de" to "d", so that the size
// of the debugging information does not change.  Only a name of at most three
// characters can pay: GCC emits one of those inline in .debug_info, but puts a
// longer name in .debug_str, where shortening it frees no .debug_info bytes.
__attribute__((noinline)) int cfa_offset(int abc, int de) {
  int sum = abc + de;
  return sum;
}
