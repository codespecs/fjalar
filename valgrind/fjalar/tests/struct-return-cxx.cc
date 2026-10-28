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

// A C++ program whose functions return classes of at most 16 bytes.  The
// Itanium C++ ABI returns a class that is non-trivial for the purposes of
// calls in memory, and the System V amd64 ABI returns any other one in
// registers.  See struct-return-test.sh.

// Registers:  every special member function is trivial.
struct Trivial { long a; double b; };
// Registers:  defaulted on its first declaration, so trivial
struct Defaulted {
  long a; double b;
  Defaulted() = default;
  Defaulted(const Defaulted&) = default;
  ~Defaulted() = default;
};
// Memory:  a user-provided destructor
struct Destructor { long a; double b; ~Destructor(); };
Destructor::~Destructor() {}
// Memory:  a user-provided copy constructor
struct CopyConstructor {
  long a; double b;
  CopyConstructor() : a(0), b(0) {}
  CopyConstructor(const CopyConstructor& o);
};
CopyConstructor::CopyConstructor(const CopyConstructor& o) : a(o.a), b(o.b) {}
// Memory:  a user-provided move constructor
struct MoveConstructor {
  long a; double b;
  MoveConstructor() : a(0), b(0) {}
  MoveConstructor(MoveConstructor&& o);
};
MoveConstructor::MoveConstructor(MoveConstructor&& o) : a(o.a), b(o.b) {}
// Memory:  a virtual function
struct Virtual { long a; virtual void f(); };
void Virtual::f() {}
// Memory:  a member variable whose class has a user-provided destructor
struct HoldsDestructor { Destructor d; };
// Memory:  a base class that has a user-provided destructor
struct DerivedDestructor : Destructor { };
// Registers:  a trivial base class
struct DerivedTrivial : Trivial { };
// Registers:  a user-provided default constructor does not matter
struct DefaultConstructor { long a; double b; DefaultConstructor(); };
DefaultConstructor::DefaultConstructor() : a(0), b(0) {}
// Memory:  its only copy or move constructor is deleted
struct DeletedCopy {
  long a; double b;
  DeletedCopy(long a0, double b0) : a(a0), b(b0) {}
  DeletedCopy(const DeletedCopy&) = delete;
};

__attribute__((noinline)) Trivial getTrivial() {
  Trivial r = {1, 2.5};
  return r;
}

__attribute__((noinline)) Defaulted getDefaulted() {
  Defaulted r;
  r.a = 3;
  r.b = 4.5;
  return r;
}

__attribute__((noinline)) Destructor getDestructor() {
  Destructor r;
  r.a = 5;
  r.b = 6.5;
  return r;
}

__attribute__((noinline)) CopyConstructor getCopyConstructor() {
  CopyConstructor r;
  r.a = 7;
  r.b = 8.5;
  return r;
}

__attribute__((noinline)) MoveConstructor getMoveConstructor() {
  MoveConstructor r;
  r.a = 9;
  r.b = 10.5;
  return r;
}

__attribute__((noinline)) Virtual getVirtual() {
  Virtual r;
  r.a = 11;
  return r;
}

__attribute__((noinline)) HoldsDestructor getHoldsDestructor() {
  HoldsDestructor r;
  r.d.a = 12;
  r.d.b = 13.5;
  return r;
}

__attribute__((noinline)) DerivedDestructor getDerivedDestructor() {
  DerivedDestructor r;
  r.a = 14;
  r.b = 15.5;
  return r;
}

__attribute__((noinline)) DerivedTrivial getDerivedTrivial() {
  DerivedTrivial r;
  r.a = 16;
  r.b = 17.5;
  return r;
}

__attribute__((noinline)) DefaultConstructor getDefaultConstructor() {
  DefaultConstructor r;
  r.a = 18;
  r.b = 19.5;
  return r;
}

__attribute__((noinline)) DeletedCopy getDeletedCopy() {
  return DeletedCopy(20, 21.5);
}

int main() {
  getTrivial();
  getDefaulted();
  getDestructor();
  getCopyConstructor();
  getMoveConstructor();
  getVirtual();
  getHoldsDestructor();
  getDerivedDestructor();
  getDerivedTrivial();
  getDefaultConstructor();
  getDeletedCopy();
  return 0;
}
