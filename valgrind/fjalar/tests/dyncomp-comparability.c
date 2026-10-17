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

// a and b are comparable, because they are compared, even though the shift
// discards the tag of the comparison's result; x and the result are
// comparable.
int shift_by_lt(int a, int b, int x) {
  return x << (a < b);
}

int main(void) {
  int r = 0;
  for (int i = 1; i < 5; i++) {
    r += shift_by_lt(i, 3, 5);
  }
  return r == 12345;
}
