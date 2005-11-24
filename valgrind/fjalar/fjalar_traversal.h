/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_traversal.h:
   Functions for traversing through data structures at run time
*/

#ifndef FJALAR_TRAVERSAL_H
#define FJALAR_TRAVERSAL_H


#include "fjalar_main.h"
#include "fjalar_runtime.h"
#include "generate_fjalar_entries.h"

#include "fjalar_traversal.h"

#define MAXIMUM_ARRAY_SIZE_TO_EXPAND 10

// String stack:
#define MAX_STRING_STACK_SIZE 100
char* fullNameStack[MAX_STRING_STACK_SIZE];
int fullNameStackSize;

void stringStackPush(char** stringStack, int* pStringStackSize, char* str);
char* stringStackPop(char** stringStack, int* pStringStackSize);
char* stringStackTop(char** stringStack, int stringStackSize);
void stringStackClear(int* pStringStackSize);
int stringStackStrLen(char** stringStack, int stringStackSize);
char* stringStackStrdup(char** stringStack, int stringStackSize);

typedef enum {
  DERIVED_VAR, // Always switches to this after one recursive call
  DERIVED_FLATTENED_ARRAY_VAR, // A derived variable as a result of flattening an array
  GLOBAL_VAR,
  FUNCTION_ENTER_FORMAL_PARAM,
  FUNCTION_EXIT_FORMAL_PARAM,
  FUNCTION_RETURN_VAR // Assume for function exits only
} VariableOrigin;

typedef enum {
  INVALID_RESULT = 0,
  // When we don't care about deriving further values by dereferencing
  // pointers.  All values of variables derived from the visited
  // variable will simply be null.  However, we will still continue to
  // derive variables by traversing inside of structs and arrays:
  DO_NOT_DEREF_MORE_POINTERS,
  // Attempt to derive more values by dereferencing pointers after
  // visiting the current variable:
  DEREF_MORE_POINTERS,
  // Stop the traversal after this variable and do not derive anything
  // further:
  STOP_TRAVERSAL
} TraversalResult;

void visitAllVariablesInList(FunctionEntry* funcPtr, // 0 for unspecified function
                             char isEnter,           // 1 for function entrance, 0 for exit
			     VariableOrigin varOrigin,
			     char* stackBaseAddr,
                             // This function performs an action for each variable visited:
                             TraversalResult (*performAction)(VariableEntry*,
                                                              char*,
                                                              VariableOrigin,
                                                              UInt,
                                                              UInt,
                                                              char,
                                                              DisambigOverride,
                                                              char,
                                                              void*,
                                                              void**,
                                                              UInt,
                                                              FunctionEntry*,
                                                              char));

void visitVariable(VariableEntry* var,
                   // Pointer to the location of the variable's
                   // current value in memory:
                   void* pValue,
                   // We only use overrideIsInit when we pass in
                   // things (e.g. return values) that cannot be
                   // checked by the Memcheck A and V bits. Never have
                   // overrideIsInit when you derive variables (make
                   // recursive calls) because their addresses are
                   // different from the original's
                   char overrideIsInit,
                   // This function performs an action for each variable visited:
                   TraversalResult (*performAction)(VariableEntry*,
                                                    char*,
                                                    VariableOrigin,
                                                    UInt,
                                                    UInt,
                                                    char,
                                                    DisambigOverride,
                                                    char,
                                                    void*,
                                                    void**,
                                                    UInt,
                                                    FunctionEntry*,
                                                    char),
                   VariableOrigin varOrigin,
                   FunctionEntry* varFuncInfo,
                   char isEnter) {

#endif
