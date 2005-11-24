/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* kvasir_main.c:
   Initialization code and command-line option handling
*/

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <search.h>

#include "tool.h"
#include "generate_daikon_data.h"
#include "kvasir_main.h"
#include "decls-output.h"
#include "dtrace-output.h"
#include "dyncomp_main.h"
#include "dyncomp_runtime.h"

#include "../fjalar_tool.h"

// Global variables that are set by command-line options
char* kvasir_decls_filename = 0;
char* kvasir_dtrace_filename = 0;
Bool kvasir_dtrace_append = False;
Bool kvasir_dtrace_no_decs = False;
Bool kvasir_dtrace_gzip = False;
Bool kvasir_output_fifo = False;
Bool kvasir_decls_only = False;
Bool kvasir_repair_format = False;
Bool kvasir_print_debug_info = False;
Bool actually_output_separate_decls_dtrace = 0;
Bool print_declarations = 1;

Bool kvasir_with_dyncomp = False;
Bool dyncomp_no_gc = False;
Bool dyncomp_fast_mode = False;
int  dyncomp_gc_after_n_tags = 10000000;
Bool dyncomp_without_dtrace = False;
Bool dyncomp_print_debug_info = False;
Bool dyncomp_print_incremental = False;
Bool dyncomp_separate_entry_exit_comp = False;


void fjlar_tool_pre_clo_init()
{
  // Nothing to do here
}

// Initialize kvasir after processing command-line options
void fjalar_tool_post_clo_init()
{
  // Special-case .dtrace handling if kvasir_dtrace_filename ends in ".gz"
  if (kvasir_dtrace_filename) {
    int filename_len = VG_(strlen)(kvasir_dtrace_filename);
    if VG_STREQ(kvasir_dtrace_filename + filename_len - 3, ".gz") {
      DPRINTF("\nFilename ends in .gz\n");
      // Chop off '.gz' from the end of the filename
      kvasir_dtrace_filename[filename_len - 3] = '\0';
      // Activate kvasir_dtrace_gzip
      kvasir_dtrace_gzip = True;
    }
  }

  // Output separate .decls and .dtrace files if:
  // --decls-only is on OR --decls-file=<filename> is on
  // OR kvasir_with_dyncomp is ON (since DynComp needs to create .decls
  // at the END of the target program's execution so that it can include
  // the comparability info)
  if (kvasir_decls_only || kvasir_decls_filename || kvasir_with_dyncomp) {
    DPRINTF("\nSeparate .decls\n\n");
    actually_output_separate_decls_dtrace = True;
  }

  // Special handling for BOTH kvasir_with_dyncomp and kvasir_decls_only
  // We need to actually do a full .dtrace run but just not output anything
  // to the .dtrace file
  if (kvasir_decls_only && kvasir_with_dyncomp) {
     kvasir_decls_only = False;
     dyncomp_without_dtrace = True;
  }

  // If we are only printing .dtrace and have --dtrace-no-decs,
  // then do not print out declarations
  if (!actually_output_separate_decls_dtrace && kvasir_dtrace_no_decs) {
     print_declarations = 0;
  }

  // If we are using DynComp with the garbage collector, initialize
  // g_oldToNewMap:
  extern UInt* g_oldToNewMap;
  if (kvasir_with_dyncomp && !kvasir_dyncomp_no_gc) {
     g_oldToNewMap = VG_(shadow_alloc)((dyncomp_gc_after_n_tags + 1) * sizeof(*g_oldToNewMap));
  }

  createDeclsAndDtraceFiles(filename);
}

void fjalar_tool_print_usage()
{
   VG_(printf)("\n  User options for Kvasir and DynComp:\n");

   VG_(printf)(
"\n  Output file format:\n"
"    --decls-file=<string>    The output .decls file location\n"
"                             (forces generation of separate .decls file)\n"
"    --decls-only             Exit after creating .decls file [--no-decls-only]\n"
"    --dtrace-file=<string>   The output .dtrace file location\n"
"                             [daikon-output/PROGRAM_NAME.dtrace]\n"
"    --dtrace-no-decs         Do not include declarations in .dtrace file\n"
"                             [--no-dtrace-no-decs]\n"
"    --dtrace-append          Appends .dtrace data to the end of an existing .dtrace file\n"
"                             [--no-dtrace-append]\n"
"    --dtrace-gzip            Compresses .dtrace data [--no-dtrace-gzip]\n"
"                             (Automatically ON if --dtrace-file string ends in '.gz')\n"
"    --output-fifo            Create output files as named pipes [--no-output-fifo]\n"
"    --program-stdout=<file>  Redirect instrumented program stdout to file\n"
"                             [Kvasir's stdout, or /dev/tty if --dtrace-file=-]\n"
"    --program-stderr=<file>  Redirect instrumented program stderr to file\n"

"\n  DynComp dynamic comparability analysis\n"
"    --with-dyncomp           Enables DynComp comparability analysis\n"
"    --gc-num-tags            The number of tags that get assigned between successive runs\n"
"                             of the garbage collector (between 1 and INT_MAX)\n"
"                             (The default is to garbage collect every 10,000,000 tags created)\n"
"    --no-dyncomp-gc          Do NOT use the tag garbage collector for DynComp.  (Faster\n"
"                             but may run out of memory for long-running programs)\n"
"    --dyncomp-fast-mode      Approximates the handling of literals for comparability.\n"
"                             (Loses some precision but faster and takes less memory)\n"
"    --separate-entry-exit-comp  Allows variables to have distinct comparability\n"
"                                numbers at function entrance/exit when run with\n"
"                                DynComp.  This provides more accuracy, but may\n"
"                                sometimes lead to output that Daikon cannot accept.\n"

"\n  Misc. options:\n"
"    --repair-format          Output format for data structure repair tool (internal use)\n"

"\n  Debugging:\n"
"    --asserts-aborts         Turn on safety asserts and aborts (OFF BY DEFAULT)\n"
"                             [--no-asserts-aborts]\n"
"    --kvasir-debug           Print Kvasir-internal debug messages [--no-debug]\n"
"    --dyncomp-debug          Print DynComp debug messages (--with-dyncomp must also be on)\n"
"                             [--no-dyncomp-debug]\n"
"    --dyncomp-print-inc      Print DynComp comp. numbers at the execution\n"
"                             of every program point (for debug only)\n"
   );
}

/* Like VG_BOOL_CLO, but of the form "--foo", "--no-foo" rather than
   "--foo=yes", "--foo=no". Note that qq_option should not have a
   leading "--". */

#define VG_YESNO_CLO(qq_option, qq_var) \
   if (VG_CLO_STREQ(arg, "--"qq_option)) { (qq_var) = True; } \
   else if (VG_CLO_STREQ(arg, "--no-"qq_option))  { (qq_var) = False; }

// Processes command-line options
Bool fjalar_tool_process_cmd_line_option(Char* arg)
{
  VG_STR_CLO(arg, "--decls-file", kvasir_decls_filename)
  else VG_STR_CLO(arg, "--dtrace-file",    kvasir_dtrace_filename)
  else VG_YESNO_CLO("dtrace-append",  kvasir_dtrace_append)
  else VG_YESNO_CLO("dtrace-no-decs",  kvasir_dtrace_no_decs)
  else VG_YESNO_CLO("dtrace-gzip",    kvasir_dtrace_gzip)
  else VG_YESNO_CLO("output-fifo",    kvasir_output_fifo)
  else VG_YESNO_CLO("decls-only",     kvasir_decls_only)
  else VG_YESNO_CLO("repair-format", kvasir_repair_format)
  else VG_YESNO_CLO("kvasir-debug",      kvasir_print_debug_info)

  else VG_YESNO_CLO("with-dyncomp",   kvasir_with_dyncomp)
  else VG_YESNO_CLO("no-dyncomp-gc",     kvasir_dyncomp_no_gc)
  else VG_YESNO_CLO("dyncomp-fast-mode", kvasir_dyncomp_fast_mode)
  else VG_BNUM_CLO(arg, "--gc-num-tags", dyncomp_gc_after_n_tags,
		   1, 0x7fffffff)
  else VG_YESNO_CLO("dyncomp-debug",  dyncomp_print_debug_info)
  else VG_YESNO_CLO("dyncomp-print-inc",  dyncomp_print_incremental)
  else VG_YESNO_CLO("separate-entry-exit-comp",  dyncomp_separate_entry_exit_comp)
  else
    return True;
}


void fjalar_tool_finish() {
  extern UInt nextTag;

  if (kvasir_with_dyncomp) {
     // Do one extra propagation of variable comparability at the end
     // of execution once all of the value comparability sets have
     // been properly updated:
     DC_extra_propagate_val_to_var_sets();

     // Now print out the .decls file at the very end of execution:
     DC_outputDeclsAtEnd();
  }

  DYNCOMP_DPRINTF("\n*** nextTag: %u ***\n\n", nextTag);

  if (!dyncomp_without_dtrace) {
     finishDtraceFile();
  }
}


// If it's the first time you've ever handled a possible function
// entrance, then you better run outputDeclsAndCloseFile so that
// Kvasir can take advantage of all of Valgrind's name demangling
// functionality while still producing a complete .decls file before
// the .dtrace file in order to allow streaming feeds into Daikon:
void fjalar_tool_handle_first_function_entrance() {
  // Remember to not actually output the .decls right now when we're
  // running DynComp.  We need to wait until the end to actually
  // output .decls, but we need to make a fake run in order to set up
  // the proper data structures
  outputDeclsFile(kvasir_with_dyncomp);

  if (actually_output_separate_decls_dtrace && !dyncomp_without_dtrace) {
    openTheDtraceFile();
  }
}

void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state) {

  // TODO: Call out to kvasir_runtime.c
}

void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state) {

  if (kvasir_with_dyncomp) {
    // For DynComp, update tags of saved register values
    int i;

    UInt EAXtag = 0;
    UInt EDXtag = 0;
    UInt FPUtag = 0;

    EAXtag = VG_(get_EAX_tag)(currentTID);
    EDXtag = VG_(get_EDX_tag)(currentTID);
    FPUtag = VG_(get_FPU_stack_top_tag)(currentTID);

    for (i = 0; i < 4; i++) {
      set_tag((Addr)(&(f_state->EAX)) + (Addr)i, EAXtag);
      set_tag((Addr)(&(f_state->EDX)) + (Addr)i, EDXtag);
      set_tag((Addr)(&(f_state->FPU)) + (Addr)i, FPUtag);
    }

    for (i = 4; i < 8; i++) {
      set_tag((Addr)(&(top->FPU)) + (Addr)i, FPUtag);
    }
  }

  // TODO: Call out to kvasir_runtime.c
}
