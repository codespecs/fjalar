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

// A C program whose functions return structs and unions of at most 16
// bytes.  The System V amd64 ABI returns each one in a different
// combination of registers, or in memory.  See struct-return-test.sh.

// %rax, %rdx
struct two_longs { long a; long b; };
// %xmm0, %xmm1
struct two_doubles { double x; double y; };
// %rax, %xmm0
struct long_double { long a; double b; };
// %xmm0, %rax
struct double_long { double a; long b; };
// %xmm0, %xmm1 (the second eightbyte holds one float)
struct three_floats { float a; float b; float c; };
// %rax:  an eightbyte that holds an int and a float is INTEGER
struct int_float { int i; float f; };
// %xmm0, %rax:  a bit-field is INTEGER
struct double_bitfield { double d; unsigned int bits : 3; };
// in memory:  the long is unaligned
struct __attribute__((packed)) packed { char c; long l; };
// %st(0)
struct x87 { long double ld; };
// %rax:  INTEGER and SSE members of a union merge to INTEGER
union double_or_long { double d; long l; };
// %xmm0, %xmm1:  a nested struct and an array
struct nested { struct { float a; float b; } p; float q[2]; };

__attribute__((noinline)) struct two_longs get_two_longs(void) {
  struct two_longs r = {1, 2};
  return r;
}

__attribute__((noinline)) struct two_doubles get_two_doubles(void) {
  struct two_doubles r = {3.5, 4.5};
  return r;
}

__attribute__((noinline)) struct long_double get_long_double(void) {
  struct long_double r = {5, 6.5};
  return r;
}

__attribute__((noinline)) struct double_long get_double_long(void) {
  struct double_long r = {7.5, 8};
  return r;
}

__attribute__((noinline)) struct three_floats get_three_floats(void) {
  struct three_floats r = {9.5f, 10.5f, 11.5f};
  return r;
}

__attribute__((noinline)) struct int_float get_int_float(void) {
  struct int_float r = {12, 13.5f};
  return r;
}

__attribute__((noinline)) struct double_bitfield get_double_bitfield(void) {
  struct double_bitfield r = {14.5, 5};
  return r;
}

__attribute__((noinline)) struct packed get_packed(void) {
  struct packed r = {'p', 16};
  return r;
}

__attribute__((noinline)) struct x87 get_x87(void) {
  struct x87 r = {17.5L};
  return r;
}

__attribute__((noinline)) union double_or_long get_double_or_long(void) {
  union double_or_long r;
  r.l = 18;
  return r;
}

__attribute__((noinline)) struct nested get_nested(void) {
  struct nested r = {{19.5f, 20.5f}, {21.5f, 22.5f}};
  return r;
}

int main(void) {
  get_two_longs();
  get_two_doubles();
  get_long_double();
  get_double_long();
  get_three_floats();
  get_int_float();
  get_double_bitfield();
  get_packed();
  get_x87();
  get_double_or_long();
  get_nested();
  return 0;
}
