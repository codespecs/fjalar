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

// A C program whose functions return doubles that are partly uninitialized.
// See double-return-shadow-test.sh.

union bits {
  double d;
  unsigned int halves[2];  // halves[0] is the low 4 bytes of d.
};

// The return value is initialized.
__attribute__((noinline)) double initialized(void) {
  union bits u;
  u.halves[0] = 0;
  u.halves[1] = 0x3ff80000;  // 1.5
  return u.d;
}

// The low 4 bytes of the return value are uninitialized.
__attribute__((noinline)) double low_uninitialized(void) {
  union bits u;
  u.halves[1] = 0x3ff80000;
  return u.d;
}

// The high 4 bytes of the return value are uninitialized.
__attribute__((noinline)) double high_uninitialized(void) {
  union bits u;
  u.halves[0] = 0;
  return u.d;
}

int main(void) {
  double sum = initialized();
  sum += low_uninitialized();
  sum += high_uninitialized();
  return sum == 12345.0;
}
