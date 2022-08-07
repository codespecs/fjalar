/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
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

// The following comment is to set up the main page of the
// Doxygen generated html doucmentation files for Fjalar.

/*! \mainpage Fjalar/Kvasir Documentation
 *
 *  Click on "Data Structures" or "Files" above to get started
 *  browsing the documention.
 */

#ifndef FJALAR_MAIN_H
#define FJALAR_MAIN_H

#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"

#include "mc_translate.h"

#include "fjalar_include.h"
#include "generate_fjalar_entries.h"

#define FJALAR_DPRINTF(...) do { if (fjalar_debug) \
      printf(__VA_ARGS__); } while (0)
#if 0
#define SECTION_NAME(X) ((X) == NULL ? "<none>" : \
                         ((X)->sh_name >= string_table_length \
                         ? "<corrupt>" : string_table + (X)->sh_name))

// Given st_shndx I, map to section_headers index
#define SECTION_HEADER_INDEX(I) \
  ((I) < SHN_LORESERVE          \
   ? (I)                        \
   : ((I) <= SHN_HIRESERVE      \
      ? 0                       \
      : (I) - (SHN_HIRESERVE + 1 - SHN_LORESERVE)))

// Reverse of the above
#define SECTION_HEADER_NUM(N)   \
  ((N) < SHN_LORESERVE          \
   ? (N)                        \
   : (N) + (SHN_HIRESERVE + 1 - SHN_LORESERVE))

#define SECTION_HEADER(I) (section_headers + SECTION_HEADER_INDEX (I))

#define GET_ELF_SYMBOLS(file, section)                  \
  (is_32bit_elf ? get_32bit_elf_symbols (file, section) \
   : get_64bit_elf_symbols (file, section))
#endif

#define ARRAY_SIZE(a) (sizeof (a) / sizeof ((a)[0]))

void handle_possible_entry(MCEnv* mce, Addr64 addr, IRSB* sb_orig);
void handle_possible_exit(MCEnv* mce, IRJumpKind jk);

// The master location_list. This is fully explained in
// typedata.c
extern struct genhashtable* loc_list_map;

extern VG_REGPARM(1) void prime_function(FunctionEntry* f);
extern VG_REGPARM(1) void enter_function(FunctionEntry* f);
extern VG_REGPARM(1) void exit_function(FunctionEntry* f);


void fjalar_pre_clo_init(void);
void fjalar_post_clo_init(void);
void fjalar_finish(void);
void fjalar_print_usage(void);
Bool fjalar_process_cmd_line_option(const HChar* arg);

void printFunctionEntryStack(void);

// The stack should never grow this deep!
#define FN_STACK_SIZE 1000

typedef FunctionExecutionState FunctionExecutionStateStack1d[FN_STACK_SIZE];
FunctionExecutionStateStack1d *FunctionExecutionStateStack;
int *fn_stack_first_free_index;

// "Pushes" a new entry onto the stack by returning a pointer to it
// and incrementing fn_stack_first_free_index (Notice that this has
// slightly has different semantics than a normal stack push)
static __inline__ FunctionExecutionState* fnStackPush(ThreadId tid) {
  tl_assert(tid != VG_INVALID_THREADID);
  tl_assert(fn_stack_first_free_index[tid] < FN_STACK_SIZE);
  fn_stack_first_free_index[tid]++;
  return &(FunctionExecutionStateStack[tid][fn_stack_first_free_index[tid] - 1]);
}

// Returns the top element of the stack and pops it off
static __inline__ FunctionExecutionState* fnStackPop(ThreadId tid) {
  tl_assert(tid != VG_INVALID_THREADID);
  tl_assert(fn_stack_first_free_index[tid] > 0);
  fn_stack_first_free_index[tid]--;
  return &(FunctionExecutionStateStack[tid][fn_stack_first_free_index[tid]]);
}

// Returns the top element of the stack
static __inline__ FunctionExecutionState* fnStackTop(ThreadId tid) {
  tl_assert(tid != VG_INVALID_THREADID);
  tl_assert(fn_stack_first_free_index[tid] >= 0);
  return &(FunctionExecutionStateStack[tid][fn_stack_first_free_index[tid] - 1]);
}

/*
Requires:
Modifies: lowestSP of the top entry in FunctionExecutionStateStack
Returns:
Effects: Compares the current SP with the lowestSP from the current
         function and sets lowestSP to current SP if current SP
         is lower.  This will provide an indicator of how far down
         the function has ever reached on the stack.

This is called from hooks within mac_shared.h

  //Okay, this is called everytime somebody tries to allocate space
  //on the stack, but the function on the top of the stack is the
  //function that we are recording.  The problem is that if the
  //function that we are recording calls another function that
  //we do not record, that new function will mess around with the
  //stack all it wants, but those values aren't accurately reflected
  //by the lowestSP of the function we are currently recording.
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
#define CHECK_SP(currentSP)                                           \
  ThreadId tid = VG_(get_running_tid)();                                \
  FunctionExecutionState* curFunc = fnStackTop(tid);			\
  if (curFunc &&							\
      (currentSP < curFunc->lowestSP)) {				\
    curFunc->lowestSP = currentSP;					\
  }

// Slower because we need to explicitly get the ESP
#define CHECK_SP_SLOW()                                                \
  ThreadId tid = VG_(get_running_tid)();                                \
  FunctionExecutionState* curFunc = fnStackTop(tid);			\
  if (curFunc) {							\
    Addr currentSP = VG_(get_SP)(VG_(get_running_tid)());		\
    if (currentSP < curFunc->lowestSP) {				\
      curFunc->lowestSP = currentSP;					\
    }									\
  }


// Even though these aren't used anywhere, for some really bizarre
// reason, if you take them out, things will fail strangely ... weird!
char* fjalar_program_stdout_filename;
char* fjalar_program_stderr_filename;

// Mapping between Dwarf Register numbers and
// valgrind function to return the value

#if defined(VGA_amd64)
// AMD64 Dwarf to Architecture mapping is (thankfully) specified
// in the AMD64 ABI (http://x86-64.org/documentation/abi.pdf)
extern Addr (*get_reg[16])( ThreadId tid );
#else
extern Addr (*get_reg[11])( ThreadId tid );
#endif

// For debugging purposes, a mapping between
// DWARF location atoms and their string
// representation

extern const HChar* dwarf_reg_string[9];


/*
   It is not at all clear how we should number the FP stack registers
   for the x86 architecture.  If the version of SDB on x86/svr4 were
   a bit less brain dead with respect to floating-point then we would
   have a precedent to follow with respect to DWARF register numbers
   for x86 FP registers, but the SDB on x86/svr4 is so completely
   broken with respect to FP registers that it is hardly worth thinking
   of it as something to strive for compatibility with.
   The version of x86/svr4 SDB I have at the moment does (partially)
   seem to believe that DWARF register number 11 is associated with
   the x86 register %st(0), but that's about all.  Higher DWARF
   register numbers don't seem to be associated with anything in
   particular, and even for DWARF regno 11, SDB only seems to under-
   stand that it should say that a variable lives in %st(0) (when
   asked via an `=' command) if we said it was in DWARF regno 11,
   but SDB still prints garbage when asked for the value of the
   variable in question (via a `/' command).
   (Also note that the labels SDB prints for various FP stack regs
   when doing an `x' command are all wrong.)
   Note that these problems generally don't affect the native SVR4
   C compiler because it doesn't allow the use of -O with -g and
   because when it is *not* optimizing, it allocates a memory
   location for each floating-point variable, and the memory
   location is what gets described in the DWARF AT_location
   attribute for the variable in question.
   Regardless of the severe mental illness of the x86/svr4 SDB, we
   do something sensible here and we use the following DWARF
   register numbers.  Note that these are all stack-top-relative
   numbers.
	11 for %st(0) (gcc regno = 8)
	12 for %st(1) (gcc regno = 9)
	13 for %st(2) (gcc regno = 10)
	14 for %st(3) (gcc regno = 11)
	15 for %st(4) (gcc regno = 12)
	16 for %st(5) (gcc regno = 13)
	17 for %st(6) (gcc regno = 14)
	18 for %st(7) (gcc regno = 15)
*/

#endif
