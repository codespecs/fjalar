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

// A C program that, when compiled with optimization, has variables whose
// locations are given by location lists.  GCC then also emits location view
// pairs (DW_AT_GNU_locviews) in the .debug_loc section, before the location
// lists.
// See location-views-test.sh.

__attribute__((noinline)) int sink(int x) {
  return x + 1;
}

// The location of a is a location list:  a is in a register at first, and
// sink() may overwrite that register.
__attribute__((noinline)) int observe(int a) {
  int r = sink(a);
  return r + sink(a * 2);
}

int main(void) {
  int t = 0;
  for (int i = 1; i < 4; i++) {
    t += observe(i);
  }
  return t == 12345;
}
