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

/* disambig.h:
   Implements the pointer-type disambiguation feature of Fjalar
   (--disambig and --disambig-file=<string> command-line options)
*/

#ifndef DISAMBIG_H
#define DISAMBIG_H

#include "fjalar_include.h"

FILE* disambig_fp;
Bool disambig_writing; // True if we are writing out to a .disambig file,
                       // False if we are reading in from a .disambig file

typedef enum DisambigEntryType {
  NONE,
  FUNCTION,  // function entry
  GLOBAL,    // global variables
  USERTYPE   // ie. struct
} DisambigEntryType;


void handleDisambigFile(void);
DisambigOverride returnDisambigOverride(VariableEntry* var);
void generateDisambigFile(void);

#endif
