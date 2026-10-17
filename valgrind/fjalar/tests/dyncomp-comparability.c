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

// Functions whose parameters DynComp should make comparable, or not.
// See dyncomp-comparability-test.sh.

#include <emmintrin.h>

// a and b are comparable, because they are compared, even though the shift
// discards the tag of the comparison's result; x and the result are
// comparable.
int shift_by_lt(int a, int b, int x) {
  return x << (a < b);
}

// a, b, and c are comparable; d is not.  The packed SSE2 add is a Triop
// (rounding mode, a, b) in VEX IR, unlike a scalar double add, which is a
// Binop.
int add_pd_lt(double a, double b, double c, double d) {
  __m128d sum = _mm_add_pd(_mm_set1_pd(a), _mm_set1_pd(b));
  return _mm_cvtsd_f64(sum) < c;
}

// a and c are comparable; d is not.  One operand of the Triop is a constant.
int add_pd_const_lt(double a, double c, double d) {
  __m128d sum = _mm_add_pd(_mm_set1_pd(a), _mm_set1_pd(2.0));
  return _mm_cvtsd_f64(sum) < c;
}

int main(void) {
  int r = 0;
  for (int i = 1; i < 5; i++) {
    r += shift_by_lt(i, 3, 5);
    r += add_pd_lt(i, 2.0, 3.0, 4.0);
    r += add_pd_const_lt(i, 3.0, 4.0);
  }
  return r == 12345;
}
