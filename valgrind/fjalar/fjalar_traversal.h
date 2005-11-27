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
#include "fjalar_select.h"
#include "generate_fjalar_entries.h"
#include "disambig.h"

// This increments every time a call to visitSingleVar() or
// visitSequence() is made.  It is up to the caller to reset this
// properly!
int g_variableIndex;

#define MAXIMUM_ARRAY_SIZE_TO_EXPAND 10

typedef enum {
  DERIVED_VAR, // Always switches to this after one recursive call
  DERIVED_FLATTENED_ARRAY_VAR, // A derived variable as a result of flattening an array
  GLOBAL_VAR,
  FUNCTION_FORMAL_PARAM,
  FUNCTION_RETURN_VAR // Only relevant for function exits
} VariableOrigin;

// These result values control the actions of the data structure
// traversal machinery:
typedef enum {
  INVALID_RESULT = 0,
  // When we don't really care about pointer dereferences at all
  // (not the same as DO_NOT_DEREF_MORE_POINTERS!)
  DISREGARD_PTR_DEREFS,

  // When we don't want to derive further values by dereferencing
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

char* DEREFERENCE;
char* ZEROTH_ELT;
char* DOT;
char* ARROW;
char* STAR;


// Takes a TypeEntry* and (optionally, a pointer to its memory
// location), and traverses through all of the members of the
// specified class (or struct/union).  This should also traverse
// inside of the class's superclasses and visit variables in them:
void visitClassMemberVariables(TypeEntry* class,
                               Addr objectAddr,
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

// Visits an entire group of variables, depending on the value of varOrigin:
// If varOrigin == GLOBAL_VAR, then visit all global variables
// If varOrigin == FUNCTION_FORMAL_PARAM, then visit all formal parameters
// of the function denoted by funcPtr
// If varOrigin == FUNCTION_RETURN_VAR, then visit the return value variable
// of the function denoted by funcPtr
void visitVariableGroup(VariableOrigin varOrigin,
                        FunctionEntry* funcPtr, // 0 for unspecified function
                        char isEnter,           // 1 for function entrance, 0 for exit
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

void visitReturnValue(FunctionExecutionState* e,
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
                   char isEnter);

#endif
