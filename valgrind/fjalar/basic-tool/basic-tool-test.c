/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2018 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

// Small test program for basic-tool and Fjalar

// Creates arrays in global, stack, and heap regions.  The tool should
// be able to figure out the sizes of all arrays passed as pointer
// parameters to the two functions.

#include <stdlib.h>

typedef struct {
  char* name;
  int age;
} Person;

Person globalPersonArray[15];
int globalIntArray[15];

void pass_an_int_pointer(int* intPtr) {}

void pass_a_struct_pointer(Person* personPtr) {}


int main() {
  Person* dynamicPersonArray = (Person*)calloc(5, sizeof(*dynamicPersonArray));
  Person localPersonArray[10];
  int i;

  int* dynamicIntArray = (int*)calloc(5, sizeof(*dynamicIntArray));
  int localIntArray[10];

  for (i = 0; i < 10; i++) {
    localPersonArray[i].name = "noname";
    localPersonArray[i].age = 20 + i;
    localIntArray[i] = i;
  }

  pass_an_int_pointer(globalIntArray);
  pass_an_int_pointer(localIntArray);
  pass_an_int_pointer(dynamicIntArray);

  pass_a_struct_pointer(globalPersonArray);
  pass_a_struct_pointer(localPersonArray);
  pass_a_struct_pointer(dynamicPersonArray);

  return 0;
}
