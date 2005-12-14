/*
   This file is part of Fjalar, a dynamic analysis framework for
   C and C++ programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/*********************************************************************
fjalar_tool.h

These are the functions that every tool built upon Fjalar must
implement in order to compile properly
**********************************************************************/

#ifndef FJALAR_TOOL_H
#define FJALAR_TOOL_H

#include "generate_fjalar_entries.h"
#include "fjalar_traversal.h"
#include "tool.h"


/*********************************************************************
Functions that run at specific times during execution:
**********************************************************************/

// Runs before command-line options are processed:
void fjalar_tool_pre_clo_init();
// Runs after command-line options are processed:
void fjalar_tool_post_clo_init();
// Prints instructions for the tool when the --help option is used:
void fjalar_tool_print_usage();

// Processes command-line options:
// Returns True if a command-line option has been successfully
// matched, False otherwise.  It's very important that you return
// False if a command-line option doesn't match because otherwise
// Fjalar will fail silently when a command-line option is mis-typed.
Bool fjalar_tool_process_cmd_line_option(Char* arg);

// Runs when the program is about to exit:
void fjalar_tool_finish();

// These functions are called during every instance of a function
// entrance and exit, respectively:
void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state);
void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state);


/*********************************************************************
Constructors and destructors for classes that can be sub-classed:
**********************************************************************/

// Constructor should return a particular sub-class of an object.
// This should call VG_(calloc) the proper amount of space for the
// object and initialize it with whatever initial state is necessary.
// DO NOT USE libc malloc/calloc, use the Valgrind versions provided
// in tool.h instead.
VariableEntry* constructVariableEntry();
TypeEntry* constructTypeEntry();
FunctionEntry* constructFunctionEntry();

// Destructors that should clean-up and then call VG_(free) on the
// respective entries.
void destroyVariableEntry(VariableEntry* v);
void destroyTypeEntry(TypeEntry* t);
void destroyFunctionEntry(FunctionEntry* f);


#endif
