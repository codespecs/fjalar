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

// A C program whose variables, struct members, formal parameters, and
// return values have types whose values Fjalar does not report:  decimal
// floating-point types, GCC's complex integer types, and _BitInt(N) for
// N > 128.  See omitted-types-test.sh.

_Decimal64 price = 1.5DD;
_Decimal32 prices[2] = { 1, 2 };
_Decimal64* pricep = &price;

// GCC names this type "complex int" in the debugging information, but it
// leaves _Complex signed char unnamed.
_Complex int gaussian = 1 + 2i;
_Complex signed char small = 3;

_BitInt(200) big = 4;
unsigned _BitInt(300) bigs[2] = { 5, 6 };

// The struct's other member is reported.
struct record { _BitInt(256) id; _Decimal128 amount; int count; } record =
  { 7, 8, 9 };

// big is passed in memory, before count.  Fjalar reports count only.
__attribute__((noinline)) _Decimal64
total(_BitInt(200) big, _Decimal64 each, _Complex int ci, int count) {
  return each * count + (_Decimal64)(big + __real__ ci);
}

int main(void) {
  _Decimal64 sum = total(big, price, gaussian, 3);
  return (sum == 9.5DD) ? 0 : 1;
}
