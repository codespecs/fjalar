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

// A C program whose variables and formal parameters have type long double,
// and one of whose functions returns a long double.  See
// long-double-test.sh.

#include <stdlib.h>

// 0.1 is not exactly representable, so its value is rounded to a double.
long double extendeds[3] = { -2.25L, 0.1L, 1e-310L };
long double extended = 1.5L;

// On amd64, a long double has 10 bytes of value and 6 bytes of padding,
// which the program never writes.
long double* heap;

__attribute__((noinline)) long double add(long double a, long double b) {
  return a + b;
}

int main(void) {
  heap = malloc(sizeof(long double));
  *heap = 3;
  extended = add(extended, *heap);
  return 0;
}
