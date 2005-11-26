/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_main.h:
   This file contains mostly prototypes that interface with
   the Memcheck code (most notably, mc_main.c).
*/

#ifndef FJALAR_MAIN_H
#define FJALAR_MAIN_H

#include <assert.h>
#include "tool.h"
#include "mc_translate.h"

#include "generate_fjalar_entries.h"

// Global variables that are set by command-line options

// Boolean flags
Bool fjalar_debug;
Bool fjalar_with_gdb;
Bool fjalar_ignore_globals;
Bool fjalar_ignore_static_vars;
Bool fjalar_limit_static_vars;
Bool fjalar_default_disambig;
Bool fjalar_smart_disambig;
Bool fjalar_output_struct_vars;
Bool fjalar_flatten_arrays;
Bool fjalar_func_disambig_ptrs;
Bool fjalar_disambig_ptrs;
int  fjalar_array_length_limit;

UInt MAX_VISIT_STRUCT_DEPTH;
UInt MAX_VISIT_NESTING_DEPTH;

// These are used as both strings and boolean flags -
// They are initialized to 0 upon initiation so if they are
// never filled with values by the respective command-line
// options, then they can be treated as False
char* fjalar_dump_prog_pt_names_filename;
char* fjalar_dump_var_names_filename;
char* fjalar_trace_prog_pts_filename;
char* fjalar_trace_vars_filename;
char* fjalar_disambig_filename;
char* fjalar_program_stdout_filename;
char* fjalar_program_stderr_filename;
char* fjalar_xml_output_filename;

// The filename of the target executable:
char* executable_filename;

#define FJALAR_DPRINTF(...) do { if (fjalar_debug) \
      VG_(printf)(__VA_ARGS__); } while (0)

/* #define DABORT(...) do { if (kvasir_asserts_aborts_on) { \ */
/*       VG_(printf)(__VA_ARGS__); abort();} } while (0) */

/* #define DASSERT(target) do { if (kvasir_asserts_aborts_on) \ */
/*       tl_assert(target); } while (0) */


void handle_possible_entry(MCEnv* mce, Addr64 addr);
void handle_possible_exit(MCEnv* mce, IRJumpKind jk);


extern VGA_REGPARM(1) void enter_function(FunctionEntry* f);
extern VGA_REGPARM(1) void exit_function(FunctionEntry* f);


void fjalar_pre_clo_init();
void fjalar_post_clo_init();
void fjalar_finish();
void fjalar_print_usage();
Bool fjalar_process_cmd_line_option(Char* arg);

void printFunctionEntryStack();

// The stack should never grow this deep!
#define FN_STACK_SIZE 1000

FunctionExecutionState FunctionExecutionStateStack[FN_STACK_SIZE];
int fn_stack_first_free_index;

__inline__ FunctionExecutionState* fnStackTop();


/*
Requires:
Modifies: lowestESP of the top entry in FunctionExecutionStateStack
Returns:
Effects: Compares the current ESP with the lowestESP from the current
         function and sets lowestESP to current ESP if current ESP
         is lower.  This will provide an indicator of how far down
         the function has ever reached on the stack.

This is called from hooks within mac_shared.h

  //Okay, this is called everytime somebody tries to allocate space
  //on the stack, but the function on the top of the stack is the
  //function that we are recording.  The problem is that if the
  //function that we are recording calls another function that
  //we do not record, that new function will mess around with the
  //stack all it wants, but those values aren't accurately reflected
  //by the lowestESP of the function we are currently recording.
  //For example, if my function "foo" drives the stack down to 100,000
  //and then it calls printf which calls other crap, driving the stack
  //down to 50,000, as far as foo is concerned, it only drove
  //the stack down to 100,000 but check_ESP() thinks it drove the
  //stack down to 50,000.

  //AD HOC solution: DON'T DEAL WITH THIS AT ALL!!!
*/
// Macro version to improve speed:
// (Remember that this code will be inserted in mc_main.c so it needs to have
//  the proper extern variables declared.)
#define CHECK_ESP(currentESP)                                           \
  FunctionExecutionState* curFunc = fnStackTop();			\
  if (curFunc &&							\
      (currentESP < curFunc->lowestESP)) {				\
    curFunc->lowestESP = currentESP;					\
  }

// Slower because we need to explicitly get the ESP
#define CHECK_ESP_SLOW()                                                \
  FunctionExecutionState* curFunc = fnStackTop();			\
  if (curFunc) {							\
    Addr currentESP = VG_(get_SP)(VG_(get_running_tid)());		\
    if (currentESP < curFunc->lowestESP) {				\
      curFunc->lowestESP = currentESP;					\
    }									\
  }


#endif
