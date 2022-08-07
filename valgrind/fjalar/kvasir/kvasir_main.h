/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

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

/* kvasir_main.h:
   Initialization code and command-line option handling
*/

#ifndef KVASIR_MAIN_H
#define KVASIR_MAIN_H

#include "../fjalar_include.h"

#include "../my_libc.h"

#include "pub_tool_libcassert.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_xarray.h" //for clientstate
#include "pub_tool_clientstate.h"
#include "pub_tool_libcprint.h"

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
  // --dyncomp-separate-entry-exit option is invoked.
  // (We choose to use the EXIT structures by default because
  //  it contains all of the variables present at ENTRY plus the
  //  return value derived variables)

  // (comment added 2005)  
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
  // (null if --dyncomp-detailed-mode is on)
  struct genhashtable* ppt_entry_var_uf_map; // Inactive unless --dyncomp-separate-entry-exit is on
  struct genhashtable* ppt_exit_var_uf_map;

  // var_tags: A fixed-sized array (indexed by the serial # of Daikon
  // variables at that program point) which contains tags which are the
  // leaders of the comparability sets of their value's tags at that
  // program point.
  // (If --dyncomp-detailed-mode is on, this is used to store the results
  //  of the conversion of relations from bitmatrix to sets, as performed
  //  in DC_convert_bitmatrix_to_sets().)
  UInt* ppt_entry_var_tags; // Inactive unless --dyncomp-separate-entry-exit is on
  UInt* ppt_exit_var_tags;

  // bitmatrix: For DynComp detailed mode (see the relevant section in
  // dyncomp_runtime.c), this represents the matrix of variables that
  // are comparable based upon comparable values they shared
  // throughout execution.  (Only non-null if --dyncomp-detailed-mode
  // is on.)
  UChar* ppt_entry_bitmatrix; // Inactive unless --dyncomp-separate-entry-exit is on
  UChar* ppt_exit_bitmatrix;

  // new_tag_leaders: A fixed-sized array (also indexed by # of Daikon
  // variables) of the leaders of the tags extracted by a certain
  // Daikon variable's value at this program point.  This structure is
  // updated EVERY TIME the program executes a program point by
  // querying val_uf with the address of the variable's value being
  // observed and getting back the tag.  (Only non-null if
  // --dyncomp-detailed-mode is on)
  UInt* ppt_entry_new_tag_leaders; // Inactive unless --dyncomp-separate-entry-exit is on
  UInt* ppt_exit_new_tag_leaders;

  // The size of var_tags and new_tags can be initialized during the .decls
  // run because we can count up how many Daikon variables exist at that
  // program point.  The number of Daikon variables as well as their order
  // is maintained during all program point executions in the .dtrace run
  // because the same traversal function is executing for both .decls and
  // .dtrace (and more importantly, because Daikon expects the front-end
  // output to maintain these variables in the same order).

  // This tells the sizes of ppt_[entry|exit]_[var|new]_tags
  // I think that num_exit_daikon_vars >= num_entry_daikon_vars
  // because at exit points, there are return values
  UInt num_entry_daikon_vars; // Inactive unless --dyncomp-separate-entry-exit is on
  UInt num_exit_daikon_vars;

  // The number of invocations of this function
  UInt num_invocations;

} DaikonFunctionEntry;

// Kvasir/DynComp-specific global variables that are set by
// command-line options
const HChar* kvasir_decls_filename;
const HChar* kvasir_dtrace_filename;
const HChar* kvasir_program_stdout_filename;
const HChar* kvasir_program_stderr_filename;
Bool kvasir_dtrace_append;
Bool kvasir_dtrace_no_decls;
Bool kvasir_dtrace_gzip;
Bool kvasir_output_fifo;
Bool kvasir_decls_only;
Bool kvasir_print_debug_info;
Bool actually_output_separate_decls_dtrace;
Bool print_declarations;
Bool kvasir_object_ppts;

Bool kvasir_with_dyncomp;
Bool dyncomp_no_gc;
Bool dyncomp_approximate_literals;
Bool dyncomp_detailed_mode;
int  dyncomp_gc_after_n_tags;
Bool dyncomp_without_dtrace;
Bool dyncomp_print_debug_info;
Bool dyncomp_print_trace_info;
Bool dyncomp_print_trace_all;
Bool dyncomp_print_incremental;
Bool dyncomp_separate_entry_exit;
Bool dyncomp_trace_startup;
Bool dyncomp_delayed_print_IR;
Bool dyncomp_delayed_trace;
Bool dyncomp_units_mode;
Bool dyncomp_dataflow_only_mode;
Bool dyncomp_dataflow_comparisons_mode;

// Define MAX_DEBUG_INFO to turn on all sorts of
// debugging printouts.  WARNING: you will get
// a LOT of data.
// #define MAX_DEBUG_INFO 1

#define DPRINTF(...) do { if (kvasir_print_debug_info) \
      printf(__VA_ARGS__); } while (0)

#define DYNCOMP_DPRINTF(...) do { if (kvasir_with_dyncomp && dyncomp_print_debug_info) \
      printf(__VA_ARGS__); } while (0)

#define DYNCOMP_TPRINTF(...) do { if (kvasir_with_dyncomp && dyncomp_print_trace_info) \
      printf(__VA_ARGS__); } while (0)

#endif
