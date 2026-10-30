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

// A C program whose variables, struct members, formal parameters, and
// return values have _Complex types.  See complex-test.sh.

_Complex double z = 1.5 + 2i;
_Complex float zs[2] = { 1, 2i };
_Complex double* zp = &z;

// The struct's other member is reported.
struct pair { _Complex _Float16 h; int n; } pair = { 3, 4 };

// z is passed in memory, before factor and count, which are also in memory
// or in registers.  Fjalar reports factor and count but not z.
__attribute__((noinline)) _Complex long double
scale(_Complex long double z, long double factor, int count) {
  return z * factor * count;
}

int main(void) {
  _Complex long double result = scale(z, 2, 3);
  return (int)__real__ result - 9;
}
