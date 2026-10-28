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

// A C program whose functions return structs, some small enough to be
// returned in registers.  See small-struct-return-test.sh.

struct one_int { int a; };
struct two_ints { int a; int b; };
struct long_int { long a; int b; };
struct two_longs { long a; long b; };
struct three_longs { long a; long b; long c; };

// Returned in the low 4 bytes of RAX.
__attribute__((noinline)) struct one_int return_one_int(void) {
  struct one_int s;
  s.a = -1;
  return s;
}

// Returned in RAX.
__attribute__((noinline)) struct two_ints return_two_ints(void) {
  struct two_ints s;
  s.a = 1;
  s.b = -2;
  return s;
}

// Returned in RAX and the low 4 bytes of RDX.
__attribute__((noinline)) struct long_int return_long_int(void) {
  struct long_int s;
  s.a = -3;
  s.b = 4;
  return s;
}

// Returned in RAX and RDX.
__attribute__((noinline)) struct two_longs return_two_longs(void) {
  struct two_longs s;
  s.a = 5;
  s.b = -6;
  return s;
}

// Returned in memory, at the address in RAX.
__attribute__((noinline)) struct three_longs return_three_longs(void) {
  struct three_longs s;
  s.a = 7;
  s.b = -8;
  s.c = 9;
  return s;
}

__attribute__((noinline)) long long return_long_long(void) {
  return -10;
}

int main(void) {
  long sum = return_one_int().a;
  sum += return_two_ints().b;
  sum += return_long_int().a;
  sum += return_two_longs().b;
  sum += return_three_longs().c;
  sum += return_long_long();
  return sum == 12345;
}
