/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
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

// One more than the largest DWARF register number that Fjalar can
// read.
#if defined(VGA_amd64)
#define FJALAR_NUM_DWARF_REGS 16
#else
#define FJALAR_NUM_DWARF_REGS 9
#endif

// The kinds of operation that visitVariableGroup evaluates in the
// location expression of a formal parameter.
typedef enum {
  LOC_OP_UNSUPPORTED,  // any operation not listed below
  LOC_OP_DEREF,        // DW_OP_deref
  LOC_OP_CONST,        // DW_OP_const*
  LOC_OP_PLUS_UCONST,  // DW_OP_plus_uconst
  LOC_OP_REG,          // DW_OP_reg* or DW_OP_breg*, for a register Fjalar can read
  LOC_OP_FBREG         // DW_OP_fbreg
} location_op_kind;

// Returns the kind of op.  decode_location_expression marks a formal
// parameter's location unsupported if it contains an op of kind
// LOC_OP_UNSUPPORTED, so visitVariableGroup never evaluates such an op.
location_op_kind location_op_kind_of(unsigned int op);

#endif /* FJALAR_DWARF_H */
