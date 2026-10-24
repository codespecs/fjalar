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

// A C program whose variables and formal parameters have type _Float128
// (IEEE 754 binary128), and one of whose functions returns a _Float128.
// See float128-test.sh.

// 0.1 is not exactly representable, so its value is rounded to a double.
// 1e400 is too large for a double, and 1e-320 is a subnormal double.
_Float128 quads[5] = { -2.25f128, 0.1f128, 1e400f128, 1e-320f128,
                       __builtin_nanf128("") };
_Float128 quad = 1.5f128;

__attribute__((noinline)) _Float128 multiply(_Float128 a, _Float128 b) {
  return a * b;
}

int main(void) {
  quad = multiply(quad, 3);
  return 0;
}
