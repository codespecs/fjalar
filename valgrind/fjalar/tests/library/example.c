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

// A C program that lives in a directory named "library", so that its
// DW_AT_name is "library/example.c".  Compilation units of the Rust runtime
// library have names that start with "library/", so Fjalar must use the
// compilation unit's language, not only its name, to decide whether the
// compilation unit is part of the Rust runtime library.
// See library-compilation-unit-test.sh.

int addOne(int x) {
  return x + 1;
}

int main(void) {
  return (addOne(41) == 42) ? 0 : 1;
}
