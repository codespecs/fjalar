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

// A C++ program whose functions return 16-byte classes.  The ABI returns
// some of them in memory, because they are not trivially copyable.  See
// class-return-test.sh.

// At -O0, GCC copies a class that it returns in XMM registers through RAX
// and RDX too, so reading RAX and RDX in place of the XMM registers might
// give the right answer.  This attribute avoids that.
#define OPTIMIZED __attribute__((noinline, optimize("O1")))

// Returned in RAX and RDX.
struct Trivial { long a; long b; };

// Returned in memory, because of its destructor.
struct WithDestructor {
  long a;
  long b;
  ~WithDestructor() { a = 0; }
};

// Returned in memory, because of its copy constructor.  Fjalar knows a
// constructor only if the program defines it, so main() copies an object.
struct WithCopyConstructor {
  long a;
  long b;
  WithCopyConstructor() : a(0), b(0) {}
  WithCopyConstructor(const WithCopyConstructor& other) : a(other.a), b(other.b) {}
};

// Returned in memory, because of its superclass's destructor.
struct WithDestructorSuperclass : WithDestructor {};

// Returned in memory, because of its member's destructor.
struct WithDestructorMember { WithDestructor a; };

// Returned in memory, because of its virtual function table pointer.
struct WithVirtualFunction {
  long a;
  virtual long get() { return a; }
};

// Returned in the low 8 bytes of XMM0 and of XMM1.
struct DoubleSuperclass { double a; };
struct WithDoubleSuperclass : DoubleSuperclass { double b; };

__attribute__((noinline)) Trivial return_trivial() {
  Trivial t;
  t.a = 1;
  t.b = -2;
  return t;
}

__attribute__((noinline)) WithDestructor return_with_destructor() {
  WithDestructor t;
  t.a = 3;
  t.b = -4;
  return t;
}

__attribute__((noinline)) WithCopyConstructor return_with_copy_constructor() {
  WithCopyConstructor t;
  t.a = 5;
  t.b = -6;
  return t;
}

__attribute__((noinline)) WithDestructorSuperclass return_with_destructor_superclass() {
  WithDestructorSuperclass t;
  t.a = 7;
  t.b = -8;
  return t;
}

__attribute__((noinline)) WithDestructorMember return_with_destructor_member() {
  WithDestructorMember t;
  t.a.a = 9;
  t.a.b = -10;
  return t;
}

__attribute__((noinline)) WithVirtualFunction return_with_virtual_function() {
  WithVirtualFunction t;
  t.a = 11;
  return t;
}

OPTIMIZED WithDoubleSuperclass return_with_double_superclass() {
  WithDoubleSuperclass t;
  t.a = 12.5;
  t.b = -13.5;
  return t;
}

int main() {
  long sum = return_trivial().b;
  sum += return_with_destructor().b;
  WithCopyConstructor returned = return_with_copy_constructor();
  WithCopyConstructor copy(returned);
  sum += copy.b;
  sum += return_with_destructor_superclass().b;
  sum += return_with_destructor_member().a.b;
  sum += return_with_virtual_function().get();
  sum += return_with_double_superclass().b;
  return sum == 12345;
}
