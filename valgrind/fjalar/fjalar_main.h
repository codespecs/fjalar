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

/* fjalar_main.h:
   This file contains mostly prototypes that interface with
   the Memcheck code (most notably, mc_main.c).
*/

#ifndef FJALAR_MAIN_H
#define FJALAR_MAIN_H

#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_mallocfree.h"

#include "mc_translate.h"

#include "fjalar_include.h"
#include "generate_fjalar_entries.h"

#define FJALAR_DPRINTF(...) do { if (fjalar_debug) \
      VG_(printf)(__VA_ARGS__); } while (0)

void handle_possible_entry(MCEnv* mce, Addr64 addr);
void handle_possible_exit(MCEnv* mce, IRJumpKind jk);


extern VG_REGPARM(1) void enter_function(FunctionEntry* f);
extern VG_REGPARM(1) void exit_function(FunctionEntry* f);


void fjalar_pre_clo_init(void);
void fjalar_post_clo_init(void);
void fjalar_finish(void);
void fjalar_print_usage(void);
Bool fjalar_process_cmd_line_option(Char* arg);

void printFunctionEntryStack(void);

// The stack should never grow this deep!
#define FN_STACK_SIZE 1000

FunctionExecutionState FunctionExecutionStateStack[FN_STACK_SIZE];
int fn_stack_first_free_index;

__inline__ FunctionExecutionState* fnStackTop(void);


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


// Even though these aren't used anywhere, for some really bizarre
// reason, if you take them out, things will fail strangely ... weird!
char* fjalar_program_stdout_filename;
char* fjalar_program_stderr_filename;

__inline__ FunctionExecutionState* fnStackPush(void);
__inline__ FunctionExecutionState* fnStackPop(void);
__inline__ FunctionExecutionState* fnStackTop(void);

#endif
