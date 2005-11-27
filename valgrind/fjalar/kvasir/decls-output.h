/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

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

#include "../generate_fjalar_entries.h"

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

void outputDeclsFile(char faux_decls);
void DC_outputDeclsAtEnd();

DaikonRepType decTypeToDaikonRepType(DeclaredType decType,
                                     char isString);

#endif
