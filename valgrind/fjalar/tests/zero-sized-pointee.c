/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

// A C program that passes a pointer whose target type occupies 0 bytes and
// whose value is in the middle of a statically-sized global array.  When
// Fjalar computes the number of elements of the array that the pointer
// refers to, the number of bytes between elements is 0.
// Rust's `*const ()` has the same two properties.
// See zero-sized-pointee-test.sh.

// A type that occupies 0 bytes (a GNU C extension).
struct empty { };

int global_array[10] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 };

int observe(struct empty *p) {
  return (p == 0) ? 0 : 1;
}

int main(void) {
  // The cast target is in the middle of global_array, so Fjalar looks for the
  // extent of the array that surrounds it.
  return observe((struct empty *)&global_array[3]) - 1;
}
