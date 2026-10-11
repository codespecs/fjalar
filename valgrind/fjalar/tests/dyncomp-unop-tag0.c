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

// Functions whose results DynComp computes with unary operations that give
// tag 0:  a count (Ctz) or a mask (GetMSBs) computed from the bits of the
// operand.  The result of each function should not be comparable to its
// parameters, but the parameters that interact (via a comparison or an
// addition) should be comparable to each other.
// See dyncomp-unop-tag0-test.sh.

#include <emmintrin.h>

// a and b are comparable; x and the result are comparable.
int shift_by_lt(int a, int b, int x) {
  return x << (a < b);
}

// a and b are comparable; the result is comparable to neither.
int ctz_of_sum(unsigned int a, unsigned int b) {
  return __builtin_ctz(a + b);
}

// The result is not comparable to x.
int ctz(unsigned int x) {
  return __builtin_ctz(x);
}

// The result is comparable to neither a nor b.
int movemask(long a, long b) {
  __m128i v = _mm_set_epi64x(a, b);
  return _mm_movemask_epi8(v);
}

int main(void) {
  int r = 0;
  // j is computed independently of i, so ctz_of_sum's a and b become
  // comparable only through the addition within ctz_of_sum.
  unsigned int j = 7;
  for (int i = 1; i < 5; i++) {
    j = j * 3 + 1;
    r += shift_by_lt(i, 3, 5);
    r += ctz_of_sum(i, j);
    r += ctz(i * 4);
    r += movemask(i, -i);
  }
  return r == 12345;
}
