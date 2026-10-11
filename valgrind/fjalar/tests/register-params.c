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
// whose location is a register (DW_OP_reg*) throughout the function.
// See register-params-test.sh.

// a and b are comparable to each other and to the result.
__attribute__((noinline)) int add(int a, int b) {
  return a + b;
}

// x is comparable to neither factor nor the result.
__attribute__((noinline)) int scale(int x, int factor) {
  return factor * 2;
}

struct pair { long first; long second; };

volatile long sink;

// p is split across two registers (DW_OP_piece), which Fjalar does not
// support, so p is omitted.
__attribute__((noinline)) void split(struct pair p) {
  sink = p.first;
  sink = p.second;
}

// d is in a floating-point register, which Fjalar cannot read, so d is
// omitted.
__attribute__((noinline)) double identity(double d) {
  return d;
}

int main(void) {
  int t = 0;
  for (int i = 1; i < 4; i++) {
    t += add(i, 3);
    t += scale(i, 7);
  }
  struct pair p = {5, 2};
  split(p);
  t += (int)identity(1.5);
  return t == 12345;
}
