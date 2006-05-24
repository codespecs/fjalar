/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
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

#include "../fjalar_include.h"
#include <stdio.h>

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

void outputDeclsFile(char faux_decls);
void DC_outputDeclsAtEnd(void);

DaikonRepType decTypeToDaikonRepType(DeclaredType decType,
                                     char isString);

void printOneFunctionDecl(FunctionEntry* funcPtr,
                          char isEnter,
                          char faux_decls);

// For new .decls format (designed in April 2006)
void printDaikonFunctionName(FunctionEntry* f, FILE* fp);
void printDaikonExternalVarName(char* fjalarName, FILE* fp);

#endif
