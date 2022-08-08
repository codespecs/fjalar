/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

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

/* decls-output.h:
   Functions for creating .decls and .dtrace files and outputting
   name and type information into a Daikon-compatible .decls file
*/

#ifndef DECLS_OUTPUT_H
#define DECLS_OUTPUT_H

#include "../my_libc.h"

#include "../fjalar_include.h"

typedef enum {
  R_NO_TYPE, // Create padding
  R_INT,
  R_DOUBLE,
  R_HASHCODE,
  R_STRING,
  R_BOOLEAN
} DaikonRepType;

const char* ENTER_PPT;
const char* EXIT_PPT;
const char* SIMPLE_EXIT_PPT;

void initDecls(void);
void cleanupDecls(void);
void outputDeclsFile(char faux_decls);
void DC_outputDeclsAtEnd(void);
void debug_print_decls(void);

DaikonRepType decTypeToDaikonRepType(DeclaredType decType,
                                     char isString);

void printOneFunctionDecl(FunctionEntry* funcPtr,
                          char isEnter,
                          char faux_decls);

// For new .decls format (designed in April 2006)
void printDaikonFunctionName(FunctionEntry* f, FILE* fp);
void printDaikonExternalVarName(VariableEntry* var, const HChar* fjalarName, FILE* fp);
const HChar* removeSuperElements(char** stringArr, VariableEntry* var);
void getUsedObjects(VariableEntry* ent, struct genhashtable* ht);
char* getParentId(char* typeName);
void traverseNestedClasses(AggregateType* agg, struct genhashtable *ht);
char* stringArrayFlatten(char** stringStack, int start, int end);

//Utility functions
int stringArrayLen(char** stringArr,int start, int end);

#endif
