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

// A C++ program with a formal parameter whose location is
// "DW_OP_fbreg N; DW_OP_deref", and whose function body overwrites the
// stack slot at DW_OP_fbreg N.  See deref-param-test.sh.

// A class with a user-provided copy constructor is passed by invisible
// reference:  the caller passes a pointer to a temporary copy, and the
// callee saves that pointer in a stack slot.
struct Counted {
  long count;
  Counted(long c) : count(c) {}
  Counted(const Counted& other) : count(other.count) {}
};

Counted decoy(2);

// Overwrites the stack slot in which the unoptimized callee saved the
// pointer to c, as an optimized callee might reuse that slot.  Returns
// true if it found the slot.
//
// It overwrites every slot that holds the pointer, because a stale copy
// of the pointer (say, from the copy constructor's frame) may precede the
// slot.  The unoptimized callee computes &c by reading the slot, so the
// slot always matches, and after the slot is overwritten, &c is &decoy.
__attribute__((noinline)) bool observe(Counted c) {
  void** frame = (void**)__builtin_frame_address(0);
  bool found = false;
  for (int i = -16; i < 0; i++) {
    if (frame[i] == &c) {
      frame[i] = &decoy;
      found = true;
    }
  }
  return found;
}

int main() {
  Counted c(1);
  return observe(c) ? 0 : 3;
}
