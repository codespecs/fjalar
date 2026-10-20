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

// The kinds of operation that visitVariableGroup evaluates in the
// location expression of a formal parameter.  Fjalar omits a formal
// parameter whose location expression has any other operation.
typedef enum {
  LOC_OP_UNSUPPORTED,  // any operation not listed below
  LOC_OP_NOP,          // DW_OP_nop, which dwarf.c does not record
  LOC_OP_DEREF,        // DW_OP_deref
  LOC_OP_CONST,        // DW_OP_const*
  LOC_OP_PLUS_UCONST,  // DW_OP_plus_uconst
  LOC_OP_REG,          // DW_OP_reg*
  LOC_OP_BREG,         // DW_OP_breg*
  LOC_OP_FBREG         // DW_OP_fbreg
} location_op_kind;

// Returns the kind of op.
static __inline__ location_op_kind location_op_kind_of(enum dwarf_location_atom op) {
  if ((op >= DW_OP_reg0) && (op <= DW_OP_reg31)) {
    return LOC_OP_REG;
  }
  if ((op >= DW_OP_breg0) && (op <= DW_OP_breg31)) {
    return LOC_OP_BREG;
  }
  if (op == DW_OP_nop) {
    return LOC_OP_NOP;
  }
  if (op == DW_OP_deref) {
    return LOC_OP_DEREF;
  }
  if ((op >= DW_OP_const1u) && (op <= DW_OP_consts)) {
    return LOC_OP_CONST;
  }
  if (op == DW_OP_plus_uconst) {
    return LOC_OP_PLUS_UCONST;
  }
  if (op == DW_OP_fbreg) {
    return LOC_OP_FBREG;
  }
  return LOC_OP_UNSUPPORTED;
}

#endif /* FJALAR_DWARF_H */
