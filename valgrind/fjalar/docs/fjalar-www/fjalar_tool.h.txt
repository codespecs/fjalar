/*
   This file is part of Fjalar, a dynamic analysis framework for
   C and C++ programs.

   Copyright (C) 2004-2006 Philip Guo <pgbovine (@) alum (.) mit (.) edu>,
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/*********************************************************************
fjalar_tool.h

These are the functions that every tool built upon Fjalar must
implement in order to compile properly.

**********************************************************************/

#ifndef FJALAR_TOOL_H
#define FJALAR_TOOL_H

#include "generate_fjalar_entries.h"
#include "fjalar_traversal.h"


/*********************************************************************
Functions that run at specific times during execution:
**********************************************************************/

// Runs before command-line options are processed:
void fjalar_tool_pre_clo_init(void);
// Runs after command-line options are processed:
void fjalar_tool_post_clo_init(void);
// Prints instructions for the tool when the --help option is used:
void fjalar_tool_print_usage(void);

// Processes command-line options:
// Returns True if a command-line option has been successfully
// matched, False otherwise.  It's very important that you return
// False if a command-line option doesn't match because otherwise
// Fjalar will fail silently when a command-line option is mis-typed.
//
// The format for a command-line option is as follows, as shown by an
// example implementation of this function:
//
// Bool fjalar_tool_process_cmd_line_option(Char* arg) {
//   // Options come in pairs of strings and variables:
//
//   // String option:
//   VG_STR_CLO(arg, "--string-option", string_var)
//   // Need an 'else' on all except the first macro because it's an 'if'
//   else VG_STR_CLO(arg, "--another-string-option", another_string_var)
//   // Boolean option:
//   else VG_YESNO_CLO("bool-option", bool_var)
//   // Bounded numerical option (this one accepts parameters from 1 to 1000):
//   else VG_BNUM_CLO(arg, "--numerical-option", numerical_var, 1, 1000)
//   else
//     return False;   // If no options match, return False so that an error
//                     // message can be reported by the Valgrind core.
//
//   // Return True to indicate success if at least one option has been matched
//   return True;
// }
//
// On the command-line, options are passed as string/value pairs with
// '--' appended to the front of every option string and values
// assigned after '='.  In the example above, here are possible
// options:
//
// "--string-option=helloworld"  --> assigns "helloworld" to char* string_var
// "--another-string-option=foobarbaz" --> assigns "foobarbaz" to char* another_string_var
// "--bool-option" --> assigns True (or 1) to Bool bool_var
// "--numerical-option=42" --> assigns 42 to Int numerical_var
//
// If any options are omitted, their respective variables take on
// default values of whatever they are initialized to in the source.
Bool fjalar_tool_process_cmd_line_option(Char* arg);


// Helper macro for command-line option processing
/* Like VG_BOOL_CLO, but of the form "--foo", "--no-foo" rather than
   "--foo=yes", "--foo=no". Note that qq_option should not have a
   leading "--". */
#define VG_YESNO_CLO(qq_option, qq_var) \
   if (VG_CLO_STREQ(arg, "--"qq_option)) { (qq_var) = True; } \
   else if (VG_CLO_STREQ(arg, "--no-"qq_option))  { (qq_var) = False; }


// Runs when the program is about to exit:
void fjalar_tool_finish(void);

// These functions are called during every instance of a function
// entrance and exit, respectively:
void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state);
void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state);


/*********************************************************************
Constructors and destructors for classes that can be subclassed:
**********************************************************************/

/*
These three main types represent the compile-time information in the
target program: FunctionEntry, VariableEntry, TypeEntry

FunctionEntry - functions
VariableEntry - variables: globals, function params, member variables
TypeEntry     - types: base types, structs, unions, C++ classes, enums

These three 'classes' can be 'subclassed' by tools, so tools should
only create and destroy instances using the 'constructor' and
'destructor' functions listed below and not directly use VG_(malloc)
and VG_(free).

Each tool can make at most one subclass of each of these classes by
creating a struct with an instance of one of these classes inlined as
the first field (structural inheritance) and then specifying for the
constructor and destructor to allocate and deallocate memory regions
of the size of the subclass instance (not the base class instance):

Example of subclassing by structural inheritance:

typedef struct _CustomTypeEntry {
  TypeEntry tE;  // Must be the FIRST member
  // All additional fields of the subclass
  int foo;
  char* bar;
  double baz;

} CustomTypeEntry

TypeEntry* constructTypeEntry() {
  return (TypeEntry*)(VG_(calloc)(1, sizeof(CustomTypeEntry)));
}

void destroyTypeEntry(TypeEntry* t) {
  VG_(free)((CustomTypeEntry*)t);
}
*/

// Constructor should return a particular sub-class of an object.
// This should call VG_(calloc) the proper amount of space for the
// object and initialize it with whatever initial state is necessary.
// DO NOT USE libc malloc/calloc; instead use the Valgrind versions
// provided in ../include/pub_tool_mallocfree.h.
VariableEntry* constructVariableEntry(void);
TypeEntry* constructTypeEntry(void);
FunctionEntry* constructFunctionEntry(void);

// Destructors that should clean-up and then call VG_(free) on the
// respective entries.  Make sure to cast the type to the subclass's
// type before calling VG_(free) or else not enough memory may be
// freed.
void destroyVariableEntry(VariableEntry* v);
void destroyTypeEntry(TypeEntry* t);
void destroyFunctionEntry(FunctionEntry* f);


#endif
