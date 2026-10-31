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
// returned in registers, and some partly uninitialized.  See
// small-struct-return-test.sh.

// At -O0, GCC copies a struct that it returns in XMM registers through RAX
// and RDX too, so reading RAX and RDX in place of the XMM registers might
// give the right answer.  This attribute avoids that.
#define OPTIMIZED __attribute__((noinline, optimize("O1")))

struct one_int { int a; };
struct two_ints { int a; int b; };
struct long_int { long a; int b; };
struct two_longs { long a; long b; };
struct three_longs { long a; long b; long c; };
struct two_floats { float a; float b; };
struct two_doubles { double a; double b; };
struct three_floats { float a[3]; };
struct double_long { double a; long b; };
struct long_double { long a; double b; };
struct int_float { int a; float b; };
union double_or_long { double a; long b; };
struct nested { struct two_floats a; double b; };
struct __attribute__((packed)) packed { char a; long b; };
struct with_long_double { long double a; };

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

// Returned in the low 8 bytes of XMM0.
OPTIMIZED struct two_floats return_two_floats(void) {
  struct two_floats s;
  s.a = 1.5;
  s.b = -2.5;
  return s;
}

// Returned in the low 8 bytes of XMM0 and of XMM1.
OPTIMIZED struct two_doubles return_two_doubles(void) {
  struct two_doubles s;
  s.a = 3.5;
  s.b = -4.5;
  return s;
}

// Returned in the low 8 bytes of XMM0 and the low 4 bytes of XMM1.
OPTIMIZED struct three_floats return_three_floats(void) {
  struct three_floats s;
  s.a[0] = 5.5;
  s.a[1] = -6.5;
  s.a[2] = 7.5;
  return s;
}

// Returned in the low 8 bytes of XMM0, and in RAX.
OPTIMIZED struct double_long return_double_long(void) {
  struct double_long s;
  s.a = 8.5;
  s.b = -9;
  return s;
}

// Returned in RAX, and in the low 8 bytes of XMM0.
OPTIMIZED struct long_double return_long_double(void) {
  struct long_double s;
  s.a = 10;
  s.b = -11.5;
  return s;
}

// Returned in RAX, because an int and a float share its eightbyte.
__attribute__((noinline)) struct int_float return_int_float(void) {
  struct int_float s;
  s.a = 12;
  s.b = -13.5;
  return s;
}

// Returned in RAX, because a double and a long share its eightbyte.
__attribute__((noinline)) union double_or_long return_double_or_long(void) {
  union double_or_long u;
  u.b = 14;
  return u;
}

// Returned in the low 8 bytes of XMM0 and of XMM1.
OPTIMIZED struct nested return_nested(void) {
  struct nested s;
  s.a.a = 15.5;
  s.a.b = -16.5;
  s.b = 17.5;
  return s;
}

// Returned in memory, at the address in RAX, because b is unaligned.
__attribute__((noinline)) struct packed return_packed(void) {
  struct packed s;
  s.a = 18;
  s.b = -19;
  return s;
}

// Returned in %st(0), which Fjalar does not read.
OPTIMIZED struct with_long_double return_with_long_double(void) {
  struct with_long_double s;
  s.a = 20.5;
  return s;
}

// The field is uninitialized.
__attribute__((noinline)) struct one_int return_one_int_uninitialized(void) {
  struct one_int s;
  return s;
}

// Field b, in the high 4 bytes of RAX, is uninitialized.
__attribute__((noinline)) struct two_ints return_two_ints_b_uninitialized(void) {
  struct two_ints s;
  s.a = 11;
  return s;
}

// Field b, in RDX, is uninitialized.
__attribute__((noinline)) struct long_int return_long_int_b_uninitialized(void) {
  struct long_int s;
  s.a = 12;
  return s;
}

// Field a, in RAX, is uninitialized.
__attribute__((noinline)) struct two_longs return_two_longs_a_uninitialized(void) {
  struct two_longs s;
  s.b = 13;
  return s;
}

// Field c is uninitialized.
__attribute__((noinline)) struct three_longs return_three_longs_c_uninitialized(void) {
  struct three_longs s;
  s.a = 14;
  s.b = 15;
  return s;
}

// Field b, in XMM1, is uninitialized.
__attribute__((noinline)) struct two_doubles return_two_doubles_b_uninitialized(void) {
  struct two_doubles s;
  s.a = 21.5;
  return s;
}

int main(void) {
  long sum = return_one_int().a;
  sum += return_two_ints().b;
  sum += return_long_int().a;
  sum += return_two_longs().b;
  sum += return_three_longs().c;
  sum += return_long_long();
  sum += return_two_floats().b;
  sum += return_two_doubles().b;
  sum += return_three_floats().a[2];
  sum += return_double_long().b;
  sum += return_long_double().a;
  sum += return_int_float().a;
  sum += return_double_or_long().b;
  sum += return_nested().b;
  sum += return_packed().b;
  sum += return_with_long_double().a;
  return_one_int_uninitialized();
  sum += return_two_ints_b_uninitialized().a;
  sum += return_long_int_b_uninitialized().a;
  sum += return_two_longs_a_uninitialized().b;
  sum += return_three_longs_c_uninitialized().b;
  sum += return_two_doubles_b_uninitialized().a;
  return sum == 12345;
}
