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

// Formal parameters in the stack frame (DW_OP_fbreg), whose locations
// register-params-test.sh rewrites.  register-params-test.sh compiles this
// file without optimization, separately from register-params.c.

extern volatile long sink;

// v is in the stack frame (DW_OP_fbreg).  register-params-test.sh
// rewrites v's location to "DW_OP_fbreg -8; DW_OP_stack_value", which Fjalar
// does not support, so v is omitted.
void stack_value(long v) {
  // buf makes v's frame offset large enough to need 2 bytes.
  volatile char buf[200];
  buf[0] = 1;
  sink = v + buf[0];
}

// y is in the stack frame (DW_OP_fbreg), which Fjalar supports,
// so y is not omitted.
void kept(long y) {
  sink = y;
}

// c and l are in the stack frame (DW_OP_fbreg).  register-params-test.sh
// rewrites c's location to "DW_OP_const1u 17; DW_OP_stack_value" and l's
// location to "DW_OP_lit5; DW_OP_stack_value", which Fjalar does not support,
// so c and l are omitted.
void constant_value(long c) {
  // buf makes c's frame offset large enough to need 2 bytes.
  volatile char buf[200];
  buf[0] = 1;
  sink = c + buf[0];
}

void literal_value(long l) {
  sink = l;
}
