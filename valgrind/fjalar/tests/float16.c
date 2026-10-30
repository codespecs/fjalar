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

// A C program whose variables, formal parameters, and return values have
// the 2-byte floating-point types _Float16 (IEEE 754 binary16) and __bf16
// (bfloat16).  See float16-test.sh.

// The largest finite value, the smallest positive subnormal value,
// infinity, and NaN, which have special encodings.
_Float16 halves[6] = { 0.5, -2, 65504, 0x1p-24, __builtin_inff16(),
                       __builtin_nanf16("") };
_Float16 half = 1.5;

// 3.140625 is the bfloat16 value nearest to pi.
__bf16 bfloats[3] = { 1, -0.5, 3.140625 };
__bf16 bfloat = 0.75;

__attribute__((noinline)) _Float16 scale_half(_Float16 x, _Float16 factor) {
  return x * factor;
}

__attribute__((noinline)) __bf16 negate_bfloat(__bf16 b) {
  return -b;
}

int main(void) {
  half = scale_half(half, 3);
  bfloat = negate_bfloat(bfloat);
  return 0;
}
