/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_tool.h:

This file contains all of the functions that a tool built upon Fjalar
must implement

*/

#ifndef FJALAR_TOOL_H
#define FJALAR_TOOL_H

#include "generate_fjalar_entries.h"


// Initialization and tear-down code:
void fjalar_tool_pre_clo_init();
void fjalar_tool_post_clo_init();
void fjalar_tool_finish();


// Constructors and destructors for classes that can be sub-classed:

// Default constructor that should return a particular sub-class of an
// object.  This should call VG_(calloc) the proper amount of space
// for the object and initialize it with whatever initial state is
// necessary.
VariableEntry* constructVariableEntry();
TypeEntry* constructTypeEntry();
FunctionEntry* constructFunctionEntry();

// Destructors that should call VG_(free) on the respective entries.
void destroyVariableEntry(VariableEntry* v);
void destroyTypeEntry(TypeEntry* t);
void destroyFunctionEntry(FunctionEntry* f);


#endif
