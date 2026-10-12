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

// d is in a register, which Fjalar does not trace, so d is omitted.
__attribute__((noinline)) double identity(double d) {
  return d;
}

int main(void) {
  struct pair p = {5, 2};
  split(p);
  return (int)identity(1.5) == 12345;
}
