/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* kvasir_main.h:
   This file contains mostly prototypes that interface with
   the Memcheck skin code (most notably, mc_main.c).
*/

#ifndef KVASIR_MAIN_H
#define KVASIR_MAIN_H

// Comment this out when we want to release Kvasir to end-users:
// #define KVASIR_DEVEL_BUILD

#include <assert.h>
#include "tool.h"
#include "kvasir_runtime.h"

// Global variables that are set by command-line options
char* kvasir_decls_filename;
char* kvasir_dtrace_filename;
Bool kvasir_print_debug_info;
Bool kvasir_ignore_globals;
Bool kvasir_ignore_static_vars;
Bool kvasir_dtrace_append;
Bool kvasir_dtrace_gzip;
Bool kvasir_output_fifo;
Bool kvasir_asserts_aborts_on;
Bool kvasir_decls_only;
Bool kvasir_limit_static_vars;
Bool kvasir_default_disambig;
Bool kvasir_use_bit_level_precision;
int kvasir_array_length_limit;
// These are used as both strings and boolean flags -
// They are initialized to 0 upon initiation so if they are
// never filled with values by the respective command-line
// options, then they can be treated as False
char* kvasir_dump_prog_pt_names_filename;
char* kvasir_dump_var_names_filename;
char* kvasir_trace_prog_pts_filename;
char* kvasir_trace_vars_filename;
char* kvasir_disambig_filename;
char *kvasir_program_stdout_filename;
char *kvasir_program_stderr_filename;

Bool actually_output_separate_decls_dtrace;

// Turn this off to not have DPRINTFs expand to anything, just in
// case you want to optimize for performance,
// but leave it on if you want the --debug command-line option to work
#define USE_DPRINTFS

#ifdef USE_DPRINTFS
#define DPRINTF(...) do { if (kvasir_print_debug_info) \
      VG_(printf)(__VA_ARGS__); } while (0)
#endif

#ifndef USE_DPRINTFS
#define DPRINTF(...)
#endif

#define DABORT(...) do { if (kvasir_asserts_aborts_on) { \
      VG_(printf)(__VA_ARGS__); abort();} } while (0)

#define DASSERT(target) do { if (kvasir_asserts_aborts_on) \
      tl_assert(target); } while (0)

unsigned int get_ESP();

extern VGA_REGPARM(2) void enter_function(Char* fnname, Addr StartPC);
extern VGA_REGPARM(1) void exit_function(Char* fnname);
void check_ESP();

void kvasir_pre_clo_init();
void kvasir_post_clo_init();
void kvasir_finish();

void printFunctionEntryStack();
void kvasir_print_usage();
Bool kvasir_process_cmd_line_option(Char* arg);


/*
Requires:
Modifies: fn_stack[ fn_stack_top - 1 ].lowestESP
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
   if (fn_stack_top > 0) {                                              \
      FunctionEntry* curFunc = &(fn_stack[ fn_stack_top - 1]);          \
      if (currentESP < curFunc->lowestESP) {                            \
         fn_stack[ fn_stack_top - 1].lowestESP = currentESP;            \
      }                                                                 \
   }

// Slower because we need to explicitly get the ESP
#define CHECK_ESP_SLOW()                                                \
   if (fn_stack_top > 0) {                                              \
      FunctionEntry* curFunc = &(fn_stack[ fn_stack_top - 1]);          \
      Addr  currentESP = VG_(get_SP)(VG_(get_running_tid)());           \
      if (currentESP < curFunc->lowestESP) {                            \
         fn_stack[ fn_stack_top - 1].lowestESP = currentESP;            \
      }                                                                 \
   }


#endif
