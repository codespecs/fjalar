/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

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
#include "fjalar_include.h"

#define MAXIMUM_ARRAY_SIZE_TO_EXPAND 10

void stringStackPush(char** stringStack, int* pStringStackSize, char* str);
char* stringStackPop(char** stringStack, int* pStringStackSize);
char* stringStackTop(char** stringStack, int stringStackSize);
void stringStackClear(int* pStringStackSize);
int stringStackStrLen(char** stringStack, int stringStackSize);
void stringStackPrint(char** stringStack, int stringStackSize);
char* stringStackStrdup(char** stringStack, int stringStackSize);

#endif
