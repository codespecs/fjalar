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

// A C program whose functions' frame bases are location lists.
// See frame-base-location-list-test.sh.

// Unoptimized, f stores its formal parameters in its stack frame, and their
// locations are offsets from the frame base.
__attribute__((noinline)) int f(int a, int b) {
  return a - b;
}

int main(void) {
  return f(5678, 1234) == 4444 ? 0 : 1;
}
