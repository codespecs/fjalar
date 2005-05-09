/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* decls-output.h:
   Functions for creating .decls and .dtrace files and outputting
   name and type information into a Daikon-compatible .decls file
*/

#ifndef DECLS_OUTPUT_H
#define DECLS_OUTPUT_H

#include "generate_daikon_data.h"
#include "disambig.h"
#include <stdio.h>

#define MAXIMUM_ARRAY_SIZE_TO_EXPAND 10

// The stack which represents the full name of the variable
// that we currently want to print out
#define MAX_STRING_STACK_SIZE 100

int g_daikonVarIndex;

char* fullNameStack[MAX_STRING_STACK_SIZE];
int fullNameStackSize;

// For use by printOneDaikonVariableAndDerivatives
typedef enum VariableOrigin {
  DERIVED_VAR, // Always switches to this after one recursive call
  DERIVED_FLATTENED_ARRAY_VAR, // A derived variable as a result of flattening an array
  GLOBAL_VAR,
  FUNCTION_ENTER_FORMAL_PARAM,
  FUNCTION_EXIT_FORMAL_PARAM,
  FUNCTION_RETURN_VAR // Assume for function exits only
} VariableOrigin;

// For use by printVariablesInVarList() and other functions
typedef enum OutputFileType {
  DECLS_FILE,
  DTRACE_FILE,
  DISAMBIG_FILE,
  DYNCOMP_EXTRA_PROP, // only for DynComp
  FAUX_DECLS_FILE     // only for DynComp - temporarily redirect decls_fp to '/dev/null'
} OutputFileType;

// For use by vars_tree:
typedef struct {
  char* function_daikon_name;
  char* function_variables_tree; // A GNU binary tree of variable names (strings)
} FunctionTree;

const char* ENTRY_DELIMETER;
const char* GLOBAL_STRING;
const char* ENTER_PPT;
const char* EXIT_PPT;

extern int MAX_NUM_STRUCTS_TO_DEREFERENCE;

void stringStackPush(char** stringStack, int* stringStackSizePtr, char* str);
char* stringStackPop(char** stringStack, int* stringStackSizePtr);
char* stringStackTop(char** stringStack, int stringStackSize);
void stringStackClear(int* stringStackSizePtr);
int stringStackStrLen(char** stringStack, int stringStackSize);
char* strdupFullNameString(char** stringStack, int stringStackSize);
char* strdupFullNameStringReverse(char** stringStack, int stringStackSize);

char createDeclsAndDtraceFiles(char* appname);
char splitDirectoryAndFilename(const char* input, char** dirnamePtr, char** filenamePtr);

void printDeclsHeader();
void printOneFunctionDecl(DaikonFunctionInfo* funcPtr, char isEnter, char faux_decls);

void printAllFunctionDecls(char faux_decls);
void printAllObjectAndClassDecls(char faux_decls);

int compareStrings(const void *a, const void *b);
void initializeProgramPointsTree();

int compareFunctionTrees(const void *a, const void *b);
void initializeVarsTree();

void outputDeclsFile(char faux_decls);
void DC_outputDeclsAtEnd();
void openTheDtraceFile(void);

void printVariablesInVarList(DaikonFunctionInfo* funcPtr,
                             char isEnter,
			     VariableOrigin varOrigin,
			     char* stackBaseAddr,
			     OutputFileType outputType,
			     char allowVarDumpToFile,
			     char* trace_vars_tree,
                             char printClassProgramPoint,
                             char stopAfterFirstVar);

void outputDaikonVar(DaikonVariable* var,
		     VariableOrigin varOrigin,
		     int numDereferences,
		     char isArray,
		     char stopExpandingArrays,
		     char stopDerivingMemberVars,
		     char allowVarDumpToFile,
		     char* trace_vars_tree, // Binary tree within FunctionTree struct
		     OutputFileType outputType,
		     DisambigOverride disambigOverride, // Only relevant for .disambig
		     // only valid if isDtraceFilePrint:
		     void* basePtrValue,
		     char overrideIsInitialized,
		     char isDummy,
		     unsigned long upperBound,
		     unsigned long bytesBetweenElts,
		     char structParentAlreadySetArrayInfo,
                     int numStructsDereferenced,
                     DaikonFunctionInfo* varFuncInfo, char isEnter);

#endif
