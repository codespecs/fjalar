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

// A C++ program with a formal parameter whose location is a location list.
// See param-location-list-test.sh.

struct C {
  int x;
  int m(int a);
};

__attribute__((noinline)) int ext(int a) { return a * 3; }

// When optimized, m uses this only to read x, so this is in a register only
// at the beginning of m, and its location is a location list.
__attribute__((noinline)) int C::m(int a) {
  int s = x;
  for (int i = 0; i < a; i++) {
    s += ext(i);
  }
  return s;
}

int main() {
  C c;
  c.x = 42;
  return c.m(5) == 72 ? 0 : 1;
}
