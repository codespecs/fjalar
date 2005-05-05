// dyncomp_runtime.h
// Contains the code to perform the run-time processing of variable
// comparability which occurs at every program point

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

  Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

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

#include "generate_daikon_data.h"

void allocate_ppt_structures(DaikonFunctionInfo* funcPtr,
                             char isEnter,
                             int numDaikonVars);

void destroy_ppt_structures(DaikonFunctionInfo* funcPtr, char isEnter);


void DC_post_process_for_variable(DaikonFunctionInfo* funcPtr,
                                  char isEnter,
                                  int daikonVarIndex,
                                  Addr a);

int equivalentTags(UInt t1, UInt t2);

#endif
