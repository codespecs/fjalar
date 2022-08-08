/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_select.h:

Implements selective tracing of particular program points and
variables.

*/

#ifndef FJALAR_SELECT_H
#define FJALAR_SELECT_H

#include "generate_fjalar_entries.h"
#include "fjalar_include.h"

const char COMMENT_CHAR;
const char* ENTRY_DELIMETER;
const int ENTRY_DELIMETER_LEN;
const char* GLOBAL_STRING;
const int GLOBAL_STRING_LEN;
const char* MANGLED_TOKEN;

// Output file pointer for dumping program point names
FILE* prog_pt_dump_fp;
// Output file pointer for dumping variable names
FILE* var_dump_fp;

// Input file pointer for list of program points to trace
FILE* trace_prog_pts_input_fp;
// Input file pointer for list of variables to trace
FILE* trace_vars_input_fp;

// For use by vars_tree:
typedef struct {
  char* function_fjalar_name;
  char* function_variables_tree; // A GNU binary tree of variable names (strings)
} FunctionTree;


int compareFunctionTrees(const void *a, const void *b);
int compareStrings(const void *a, const void *b);

void initializeProgramPointsTree(void);
void initializeVarsTree(void);

void outputProgramPointsToFile(void);
void outputVariableNamesToFile(void);

#endif
