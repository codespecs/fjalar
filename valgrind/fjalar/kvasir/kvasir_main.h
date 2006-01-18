/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* kvasir_main.h:
   Initialization code and command-line option handling
*/

#ifndef KVASIR_MAIN_H
#define KVASIR_MAIN_H

#include "../fjalar_include.h"
#include <stdio.h>

FILE* decls_fp; // File pointer for .decls file (this will point
                // to the same thing as dtrace_fp by default since
                // both .decls and .dtrace are outputted to .dtrace
                // unless otherwise noted by the user)

FILE* dtrace_fp; // File pointer for dtrace file (from dtrace-output.c)

// Sub-class of FunctionEntry from generate_fjalar_entries.h Remember
// to implement constructFunctionEntry() and destroyFunctionEntry()
// correctly!
typedef struct {
  // Superclass:
  FunctionEntry funcEntry; // This must be INLINED, not a pointer

  // Additional fields only in the sub-class:

  // For DynComp - union-find data structures for all relevant variables
  //               at the entry and exit program points of this function

  // Important! Make sure to only initialize these only ONCE (when you
  // are outputting .decls) or else you'll get nasty duplicate
  // variable names and sets!!!

  // ALSO VERY IMPORTANT:  We have two separate sets of data structures,
  // one for function entry and the other for exit.  However, the default
  // behavior should be to only initialize the EXIT set of structures
  // and just use those because Daikon expects variables to belong to
  // the same comparability sets at the entry and exit program points.
  // We will only use the ENTRY structures when the
  // --separate-entry-exit-comp option is invoked.
  // (We choose to use the EXIT structures by default because
  //  it contains all of the variables present at ENTRY plus the
  //  return value derived variables)

  // TODO: WARNING!  This hashtable-within-hashtable structure may
  // blow up in my face and cause a huge memory overload!!!  Remember
  // that each hashtable is initialized to a constant number!  I'll
  // try to keep them fairly small by calling
  // genallocateSMALLhashtable, but they still take up room
  // nonetheless.

  // var_uf_map:
  // Key: tag which is the leader of some entry in val_uf
  // Value: uf_object

  // Define a function (implemented as a non-null hashtable get)
  // var_uf_map.exists(val_uf leader entry) returns true if entry from
  // val_uf exists in var_uf_map.

  // var_uf_map is the variable analogue to val_uf, which is the union-find
  // for all values ever created in a program.
  struct genhashtable* ppt_entry_var_uf_map; // Inactive unless --separate-entry-exit-comp is on
  struct genhashtable* ppt_exit_var_uf_map;

  // var_tags: A fixed-sized array (indexed by the serial # of Daikon
  // variables at that program point) which contains tags which are the
  // leaders of the comparability sets of their value's tags at that
  // program point.
  UInt* ppt_entry_var_tags; // Inactive unless --separate-entry-exit-comp is on
  UInt* ppt_exit_var_tags;

  // new_tags: A fixed-sized array (also indexed by # of Daikon variables)
  // of the tags extracted by a certain Daikon variable's value at this
  // program point.  This structure is updated EVERY TIME the program
  // executes a program point by querying val_uf with the address of the
  // variable's value being observed and getting back the tag.
  UInt* ppt_entry_new_tags; // Inactive unless --separate-entry-exit-comp is on
  UInt* ppt_exit_new_tags;

  // The size of var_tags and new_tags can be initialized during the .decls
  // run because we can count up how many Daikon variables exist at that
  // program point.  The number of Daikon variables as well as their order
  // is maintained during all program point executions in the .dtrace run
  // because the same traversal function is executing for both .decls and
  // .dtrace (and more importantly, because Daikon expects the front-end
  // output to maintain these variables in the same order).

  // This tells the sizes of ppt_[entry|exit]_[var|new]_tags
  UInt num_entry_daikon_vars; // Inactive unless --separate-entry-exit-comp is on
  UInt num_exit_daikon_vars;

} DaikonFunctionEntry;

// Kvasir/DynComp-specific global variables that are set by
// command-line options
char* kvasir_decls_filename;
char* kvasir_dtrace_filename;
char* kvasir_program_stdout_filename;
char* kvasir_program_stderr_filename;
Bool kvasir_dtrace_append;
Bool kvasir_dtrace_no_decs;
Bool kvasir_dtrace_gzip;
Bool kvasir_output_fifo;
Bool kvasir_decls_only;
Bool kvasir_repair_format;
Bool kvasir_print_debug_info;
Bool actually_output_separate_decls_dtrace;
Bool print_declarations;

Bool kvasir_with_dyncomp;
Bool dyncomp_no_gc;
Bool dyncomp_fast_mode;
int  dyncomp_gc_after_n_tags;
Bool dyncomp_without_dtrace;
Bool dyncomp_print_debug_info;
Bool dyncomp_print_incremental;
Bool dyncomp_separate_entry_exit_comp;
Bool dyncomp_units_mode;
Bool dyncomp_dataflow_only_mode;
Bool dyncomp_dataflow_comparisons_mode;

#define DPRINTF(...) do { if (kvasir_print_debug_info) \
      VG_(printf)(__VA_ARGS__); } while (0)

#define DYNCOMP_DPRINTF(...) do { if (kvasir_with_dyncomp && dyncomp_print_debug_info) \
      VG_(printf)(__VA_ARGS__); } while (0)

#endif
