/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_dwarf.h:
   Aspects of the DWARF debugging information that are particularly
   relevant for fjalar.
*/

#ifndef FJALAR_DWARF_H
#define FJALAR_DWARF_H

// Type information data structures
#define MAX_DWARF_STACK  10

typedef struct _dwarf_location {
  unsigned int atom;
  long long atom_offset;
} dwarf_location;

#endif /* FJALAR_DWARF_H */

