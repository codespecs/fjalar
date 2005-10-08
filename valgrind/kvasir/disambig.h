/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* disambig.h:
   Implements the pointer-type disambiguation feature of Kvasir
   (--disambig and --disambig-file=<string> command-line options)
*/

#ifndef DISAMBIG_H
#define DISAMBIG_H

#include "tool.h"
#include "generate_daikon_data.h"
#include <stdio.h>

FILE* disambig_fp;
Bool disambig_writing;

typedef enum DisambigEntryType {
  NONE,
  FUNCTION,  // function entry
  GLOBAL,    // global variables
  USERTYPE   // ie. struct
} DisambigEntryType;

typedef enum DisambigOverride {
  OVERRIDE_NONE,
  OVERRIDE_CHAR_AS_STRING, // 'C' for base "char" and "unsigned char" types
  OVERRIDE_STRING_AS_ONE_CHAR_STRING, // 'C' for pointer to "char" and "unsigned char"
  OVERRIDE_STRING_AS_INT_ARRAY, // 'A' for pointer to "char" and "unsigned char"
  OVERRIDE_STRING_AS_ONE_INT,   // 'P' for pointer to "char" and "unsigned char"
  OVERRIDE_ARRAY_AS_POINTER     // 'P' for pointer to anything
} DisambigOverride;

void generateDisambigFile();
void printOneFunctionDisambig(DaikonFunctionInfo* funcPtr);
Bool shouldOutputVarToDisambig(DaikonVariable* var);
void processDisambigFile();

#endif
