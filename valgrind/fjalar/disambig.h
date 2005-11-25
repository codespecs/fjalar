/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

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
#include "generate_fjalar_entries.h"
#include <stdio.h>

FILE* disambig_fp;
Bool disambig_writing; // True if we are writing out to a .disambig file,
                       // False if we are reading in from a .disambig file

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

void handleDisambigFile();
DisambigOverride returnDisambigOverride(VariableEntry* var);
void generateDisambigFile();

#endif
