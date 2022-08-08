/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_dwarf:
   Aspects of the DWARF debugging information that are particularly
   relevant for fjalar.
*/

#ifndef FJALAR_DWARF_H
#define FJALAR_DWARF_H

#include "elfcomm.h"
#include "dwarf.h"
#include "dwarf2.h"

// Vendor specific extensions to the DWARF spec
#define DW_OP_list (DW_OP_lo_user+1)

// Type information data structures
#define MAX_DWARF_OPS  10

typedef struct _dwarf_location {
  unsigned int atom;
  long long atom_offset;
} dwarf_location;

// A conversion between DWARF location atoms and a string representation
const char* location_expression_to_string(enum dwarf_location_atom op);

#endif /* FJALAR_DWARF_H */
