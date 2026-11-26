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

// main for frame-base-cfa-offset.c, in a separate compilation unit so that
// the test rewrites only cfa_offset's debugging information.
// See frame-base-cfa-offset-test.sh.

int cfa_offset(int abc, int de);

int main(void) {
  return cfa_offset(5678, 1234) == 6912 ? 0 : 1;
}
