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

// A C++ program with formal parameters that lie in the caller's frame,
// beyond the part of the stack that Fjalar copies at function entrance
// by default, and whose function body changes them.  See
// caller-frame-param-test.sh.

// A class with a user-provided copy constructor is passed by invisible
// reference:  the caller passes a pointer to a temporary copy in its own
// frame.  The padding makes the copies large, so that they extend beyond
// the part of the stack that Fjalar copies by default.  last is the last
// word of an object, so that the test checks that Fjalar copies all of it,
// not only its first word.
struct Counted {
  long count;
  long padding[14];
  long last;
  Counted(long c) : count(c), last(10 * c) {}
  Counted(const Counted& other) : count(other.count), last(other.last) {}
};

// Changes the callee's copies, which the caller cannot observe.
__attribute__((noinline)) void mutate(Counted a, Counted b) {
  a.count = 5;
  b.count = 6;
  a.last = 50;
  b.last = 60;
}

int main() {
  Counted a(1);
  Counted b(2);
  mutate(a, b);
  return 0;
}
