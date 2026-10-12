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

// A C program that, when compiled with optimization, has formal parameters
// whose locations Fjalar cannot read.  Fjalar omits them from both the .decls
// and .dtrace files.  See omitted-params-test.sh.

struct pair { long first; long second; };

volatile long sink;

// p is split across two registers (DW_OP_piece), which Fjalar does not
// support, so p is omitted.
__attribute__((noinline)) void split(struct pair p) {
  sink = p.first;
  sink = p.second;
}

// d is in a register (DW_OP_reg*), which Fjalar does not support, so d is
// omitted.
__attribute__((noinline)) double identity(double d) {
  return d;
}

// Unoptimized, x is in the stack frame (DW_OP_fbreg).  omitted-params-test.sh
// rewrites x's location to "DW_OP_fbreg -8; DW_OP_stack_value", which Fjalar
// does not support, so x is omitted.
__attribute__((noinline, optimize("O0"))) void stack_value(long x) {
  // buf makes x's frame offset large enough to need 2 bytes.
  volatile char buf[200];
  buf[0] = 1;
  sink = x + buf[0];
}

int main(void) {
  struct pair p = {5, 2};
  split(p);
  stack_value(7);
  return (int)identity(1.5) == 12345;
}
