// dyncomp_runtime.h
// Contains the code to perform the run-time processing of variable
// comparability which occurs at every program point

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2009 Julian
  Seward, jseward@acm.org)

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

#ifndef DYNCOMP_RUNTIME_H
#define DYNCOMP_RUNTIME_H

#include "../fjalar_include.h"

// Maps tags to comparability numbers, which are assigned sequentially
// for every program point.  This is only used for DynComp.
// Key: tag (unsigned int)
// Value: comparability number (int) - notice that this is SIGNED because that
//                                     is what Daikon requires
struct genhashtable* g_compNumberMap;

// This is the current sequential comparability number (only for
// DynComp).  It increments after it has been assigned as a value in
// g_compNumberMap, and it is reset back to 1 during every program
// point.
int g_curCompNumber;

void allocate_ppt_structures(DaikonFunctionEntry* funcPtr,
                             char isEnter,
                             int numDaikonVars);

void destroy_ppt_structures(DaikonFunctionEntry* funcPtr, char isEnter);


void DC_post_process_for_variable(DaikonFunctionEntry* funcPtr,
                                  char isEnter,
                                  VariableOrigin varOrigin,
                                  int daikonVarIndex,
                                  Addr a);

void DC_extra_propagation_post_process(DaikonFunctionEntry* funcPtr,
                                       char isEnter,
                                       int daikonVarIndex);

int DC_get_comp_number_for_var(DaikonFunctionEntry* funcPtr,
                               char isEnter,
                               int daikonVarIndex);

int equivalentTags(UInt t1, UInt t2);

void DC_extra_propagate_val_to_var_sets(void);

void debugPrintTagsInRange(Addr low, Addr high);

// Tag garbage collector
void check_whether_to_garbage_collect(void);

void garbage_collect_tags(void);

// DynComp detailed mode (--dyncomp-detailed-mode):
UInt bitarraySize(UInt n);
char isMarked(UChar* bitarray, UInt n, UInt i, UInt j);
void mark(UChar* bitarray, UInt n, UInt i, UInt j);

void DC_detailed_mode_process_ppt_execution(DaikonFunctionEntry* funcPtr,
                                            Bool isEnter);

void DC_convert_bitmatrix_to_new_tag_leaders(DaikonFunctionEntry* funcPtr,
                                             char isEnter);
void DC_convert_bitmatrix_to_sets(DaikonFunctionEntry* funcPtr,
                                  char isEnter);
#endif
