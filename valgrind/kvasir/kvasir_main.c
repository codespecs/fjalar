/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   2005-04-28:
   Ported over to Valgrind 3 and integrated with the DynComp dynamic
   comparability analysis tool for C/C++.

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* kvasir_main.c:

   This file contains most of the code to interact with the Valgrind
   core.  It is called from mc_main.c since mc_main.c is the
   launching-point for Kvasir.
*/

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>

#include "tool.h"
#include "generate_daikon_data.h"
#include "kvasir_main.h"
#include "decls-output.h"
#include "dtrace-output.h"
#include "mc_include.h"
#include "disambig.h"

// Global variables that are set by command-line options
char* kvasir_decls_filename = 0;
char* kvasir_dtrace_filename = 0;
Bool kvasir_print_debug_info = False;
Bool kvasir_ignore_globals = False;
Bool kvasir_ignore_static_vars = False;
Bool kvasir_dtrace_append = False;
Bool kvasir_dtrace_gzip = False;
Bool kvasir_output_fifo = False;
#ifdef KVASIR_DEVEL_BUILD
Bool kvasir_asserts_aborts_on = True;
#else
Bool kvasir_asserts_aborts_on = False;
#endif
Bool kvasir_decls_only = False;
Bool kvasir_limit_static_vars = False;
Bool kvasir_default_disambig = False;
Bool kvasir_use_bit_level_precision = False;
int kvasir_array_length_limit = -1;
char* kvasir_dump_prog_pt_names_filename = 0;
char* kvasir_dump_var_names_filename = 0;
char* kvasir_trace_prog_pts_filename = 0;
char* kvasir_trace_vars_filename = 0;
char* kvasir_disambig_filename = 0;
char *kvasir_program_stdout_filename = 0;
char *kvasir_program_stderr_filename = 0;

Bool actually_output_separate_decls_dtrace = 0;

// Stores the floating-point return value:
// NOTE: Make this initialize to NaN in the future!
double fpuReturnValue = 0;

// DON'T USE THIS FOR NOW!!!
/*------------------------------------------------------------*/
/*--- ignoreESPChangesStack                                ---*/
/*------------------------------------------------------------*/
// Stack of booleans for ignoring ESP changes depending on which
// function we are in - set MAX_IGNORE_STACK_SIZE to a reasonable
// number that represents how big our function stack is expected
// to grow
/*
#define MAX_IGNORE_STACK_SIZE 500

int ignoreESPChangesStackSize = 0;
char ignoreESPChangesStack[MAX_IGNORE_STACK_SIZE];
*/

/*------------------------------------------------------------*/
/*--- Command line stuff                                   ---*/
/*------------------------------------------------------------*/

// Show all functions?  Default: NO
Bool sp_clo_show_all_funcs = False;


/*------------------------------------------------------------*/
/*--- Function stack                                       ---*/
/*------------------------------------------------------------*/
// TODO: Should I MAKE THIS HUGE??? or dynamically-allocate??? (original = 10000)
#define FN_STACK_SIZE 10000

FunctionEntry fn_stack[FN_STACK_SIZE];
Int   fn_stack_top;       // actually just above top -- next free slot

/*------------------------------------------------------------*/
/*--- Printing                                             ---*/
/*------------------------------------------------------------*/

void printFunctionEntryStack()
{
   int i;
   for (i = fn_stack_top - 1; i >= 0; i--)
      {
         FunctionEntry* cur_fn = &fn_stack[i];
         VG_(printf)("fn_stack[%d] %s - EBP: 0x%x, lowestESP: 0x%x, localArrayVarPtr: %p\n",
                i,
                cur_fn->name,
                cur_fn->EBP,
                cur_fn->lowestESP,
                cur_fn->localArrayVariablesPtr);
      }
}

/*------------------------------------------------------------*/
/*--- ignoreESPChangesStack ops                            ---*/
/*------------------------------------------------------------*/

// Standard lazy fixed-sized stack implementation
/*
char ignoreESPChangesStackTop()
{
   if (ignoreESPChangesStackSize > 0)
      {
         return ignoreESPChangesStack[ignoreESPChangesStackSize - 1];
      }
   else
      return 0;
}

char ignoreESPChangesStackPop()
{
   if (ignoreESPChangesStackSize > 0)
      {
         ignoreESPChangesStackSize--;
         return ignoreESPChangesStack[ignoreESPChangesStackSize];
      }
   else
      return 0;
}

void ignoreESPChangesStackClear()
{
   memset(ignoreESPChangesStack, 0, sizeof(ignoreESPChangesStack));
   ignoreESPChangesStackSize = 0;
}

void ignoreESPChangesStackPush(char i)
{
   if (ignoreESPChangesStackSize < MAX_IGNORE_STACK_SIZE)
      {
         ignoreESPChangesStack[ignoreESPChangesStackSize] = i;
         ignoreESPChangesStackSize++;
      }
}
*/

/*------------------------------------------------------------*/
/*--- Function stack ops                                   ---*/
/*------------------------------------------------------------*/

/*
Requires: stackEntry is allocated to hold one FunctionEntry
Modifies: *stackEntry
Returns: success
Effects: *stackEntry initiated with contents on the top of fn_stack
*/
static Bool top(FunctionEntry *stackEntry)
{
  if (fn_stack_top < 1) return False;

  if (stackEntry)
    *stackEntry = fn_stack[ fn_stack_top - 1 ];

  DPRINTF("TOP %s, fn_stack_top: %d\n", stackEntry->name, fn_stack_top);

  return True;
}

/*
Requires:
Modifies: fn_stack[ fn_stack_top ], fn_stack_top
Returns:
Effects: top of fn_stack initialized with parameters - called on function entrance
since EAX, EDX, and FPU are not known until function exit time
*/
static void push(Char* f, Addr EBP, Addr startPC,
                 char* virtualStack, int virtualStackByteSize,
                 VarList* localArrayVariablesPtr)
{
   if (fn_stack_top >= FN_STACK_SIZE) VG_(tool_panic)("overflowed fn_stack");

   fn_stack[ fn_stack_top ].name = f;
   fn_stack[ fn_stack_top ].EBP = EBP;
   fn_stack[ fn_stack_top ].startPC = startPC;
   fn_stack[ fn_stack_top ].lowestESP = EBP + 4;
   fn_stack[ fn_stack_top ].EAX = 0;
   fn_stack[ fn_stack_top ].EDX = 0;
   fn_stack[ fn_stack_top ].FPU = 0;
   fn_stack[ fn_stack_top ].EAXvalid = 0;
   fn_stack[ fn_stack_top ].EDXvalid = 0;
   fn_stack[ fn_stack_top ].virtualStack = virtualStack;
   fn_stack[ fn_stack_top ].virtualStackByteSize = virtualStackByteSize;
   fn_stack[ fn_stack_top ].localArrayVariablesPtr = localArrayVariablesPtr;

   fn_stack_top++;

   DPRINTF("PUSH %s, fn_stack_top: %d\n", f, fn_stack_top);
}

/*
Requires: stackEntry is allocated to hold one FunctionEntry
Modifies: fn_stack_top, *stackEntry
Returns:
Effects: *stackEntry initiated with contents on the top of fn_stack,
         top entry of fn_stack "popped" by decrementing fn_stack_top
*/
static void pop(FunctionEntry *stackEntry)
{
  if (fn_stack_top < 1) {
    VG_(tool_panic)("underflowed fn_stack");
  }

   fn_stack_top--;

   if (stackEntry)
     *stackEntry = fn_stack[ fn_stack_top ];

   DPRINTF("POP %s, fn_stack_top: %d\n", stackEntry->name, fn_stack_top);
}

/*------------------------------------------------------------*/
/*--- Function entry/exit                                  ---*/
/*------------------------------------------------------------*/

/*
Requires:
Modifies: fn_stack, fn_stack_top, tempEntry
Returns:
Effects: pops a FunctionEntry off of the top of fn_stack and initializes
         it with EAX, EDX, and FPU values. Then calls handleFunctionExit()
         to generate .dtrace file output at function exit time
// %EAX -> EAX
// %EDX -> EDX
// %ST(0) -> FPU
*/
void pop_fn(Char* s, int EAX, int EDX, double FPU_top, char EAXvalid, char EDXvalid)
{
   FunctionEntry tempEntry;

   // s is null if an "unwind" is popped off the stack
   // Only do something if this function name matches what's on the top of the stack
   if (!s || (!VG_STREQ(fn_stack[fn_stack_top - 1].name, s))) {
      return;
   }

   top(&tempEntry); // Don't pop it yet because we want to keep fn_stack_top
                   // unchanged during handleFunctionExit

   tempEntry.EAX = EAX;
   tempEntry.EDX = EDX;
   tempEntry.FPU = FPU_top;
   tempEntry.EAXvalid = EAXvalid;
   tempEntry.EDXvalid = EDXvalid;

   DPRINTF("------ POP_FN: fn_stack_top: %d, s: %s\n", fn_stack_top, s);

   handleFunctionExit(&tempEntry);

   // Destroy the memory allocated by virtualStack
   if (tempEntry.virtualStack) {
      // Let's just use normal calloc here because otherwise it crashes for some reason
      // so we have to use normal free
      free(tempEntry.virtualStack);
   }

   fn_stack_top--; // Now pop it off by decrementing fn_stack_top
}

/*
Requires:
Modifies: fn_stack, fn_stack_top, tempEntry
Returns:
Effects: pushes a FunctionEntry onto the top of fn_stack and initializes
         it with function name (f), and EBP values.
         This is called during function entrance.  Initializes "virtual
         stack" in tempEntry and then calls handleFunctionEntrance()
         to generate .dtrace file output at function entrance time
*/
void push_fn(Char* s, Char* f, Addr EBP, Addr startPC)
{
  DaikonFunctionInfo* daikonFuncPtr =
    findFunctionInfoByAddr(startPC);

  int formalParamStackByteSize = 0;

  FunctionEntry tempEntry;

  tempEntry.name = f;
  tempEntry.EBP = EBP;
  tempEntry.lowestESP = EBP + 4;
  tempEntry.startPC = startPC;

  formalParamStackByteSize = determineFormalParametersStackByteSize(daikonFuncPtr);

  DPRINTF("formalParamStackByteSize is %d\n", formalParamStackByteSize);

  // Initialize virtual stack and copy parts of the Valgrind
  // stack into that virtual stack

  // Let's just use normal calloc here because otherwise it crashes for some reason
  tempEntry.virtualStack = calloc(formalParamStackByteSize, sizeof(char));
  tempEntry.virtualStackByteSize = formalParamStackByteSize;

  VG_(memcpy)(tempEntry.virtualStack, (void*)(tempEntry.EBP), formalParamStackByteSize);
  // VERY IMPORTANT!!! Copy all the A & V bits over from EBP to virtualStack!!!
  mc_copy_address_range_state(tempEntry.EBP, (Addr)tempEntry.virtualStack, formalParamStackByteSize);

  // Initialize the FunctionEntry.localArrayVariablesPtr field:
  tempEntry.localArrayVariablesPtr = &(daikonFuncPtr->localArrayVariables);
  //  VG_(printf)("tempEntry.localArrayVariablesPtr = %p\n", tempEntry.localArrayVariablesPtr);

  push(f, EBP, startPC, tempEntry.virtualStack,
       tempEntry.virtualStackByteSize, tempEntry.localArrayVariablesPtr);

  // We used to do this BEFORE the push - does it make a difference???

  DPRINTF("-- PUSH_FN: fn_stack_top: %d, f: %s\n", fn_stack_top, f);

  // Do this AFTER initializing virtual stack and lowestESP
  handleFunctionEntrance(&tempEntry);
}

/*
Requires:
Modifies:
Returns: The Valgrind virtual ESP
Effects:
*/
/* unsigned int get_ESP() */
/* { */
/*    return VG_(get_archreg)(R_ESP); */
/* } */

/*
Requires:
Modifies: fn_stack, fn_stack_top, tempEntry, ignoreESPChangesStack
Returns:
Effects: This is the hook into Valgrind that is called whenever the target
         program enters a function.  Calls push_fn() if all goes well.
*/
// Rudimentary function entrance/exit tracking
VGA_REGPARM(2)
void enter_function(Char* fnname, Addr StartPC)
{
   Addr  ESP = VG_(get_SP)(VG_(get_running_tid)());
   // Assign %esp - 4 to %ebp - empirically tested to be
   // correct for calling conventions
   Addr  EBP = ESP - 4;

   VG_(printf)("Enter function: %s - StartPC: %p\n",
	   fnname, (void*)StartPC);

   // Check for longjmps (if the ESP is less than the that of the call on
   // the top of the stack)
   //   while ( top(&topEntry) && (ESP > (topEntry.EBP + 4)) ) { // ESP = EBP + 4
   //      unwinds++;
   //      pop_fn("unwc", 0, 0, 0, 0, 0);
   //   }

   DPRINTF("Calling push_fn for %s\n", fnname);

   push_fn("call", fnname, EBP, StartPC);
}

/*
Requires:
Modifies: fn_stack, fn_stack_top, topEntry, ignoreESPChangesStack
Returns:
Effects: This is the hook into Valgrind that is called whenever the target
         program exits a function.  Initializes topEntry of fn_stack with
         return values from EAX, EDX, and FPU.  Calls pop_fn() if all goes well.
*/
VGA_REGPARM(1)
void exit_function(Char* fnname)
{
   ThreadId currentTID = VG_(get_running_tid)();

   double localFpuReturnVal;
   //   Addr  ESP = VG_(get_archreg)(R_ESP)-4;

   // Get the value at the simulated %EAX (integer and pointer return
   // values are stored here upon function exit)
   //   Addr EAX = VG_(get_archreg)(R_EAX);
   Addr EAX = VG_(get_EAX)(currentTID);

   // Get the value of the simulated %EDX (the high 32-bits of the
   // long long int return value is stored here upon function exit)
   //   Addr EDX = VG_(get_archreg)(R_EDX);
   Addr EDX = VG_(get_EDX)(currentTID);

   //   int i;
   //   int *intPtr;
   //   float *floatPtr;

   // Use SHADOW values of Valgrind simulated registers to get V-bits
   // The core returns the results in a BASS-ACKWARDS format:
   // ZERO for valid and NON-ZERO for invalid so FLIP IT!!!
   int EAXvalid;
   int EDXvalid;

   //   if (VG_(get_shadow_archreg)(R_EAX))
   if (VG_(get_shadow_EAX)(currentTID))
      {
         EAXvalid = 0;
      }
   else
      {
         EAXvalid = 1;
      }

   //   if (VG_(get_shadow_archreg)(R_EDX))
   if (VG_(get_shadow_EDX)(currentTID))
      {
         EDXvalid = 0;
      }
   else
      {
         EDXvalid = 1;
      }

   // Ok, in Valgrind 2.X, we needed to directly code some assembly to grab
   // the top of the floating-point stack, but Valgrind 3.0 provides a virtual
   // FPU stack, so we can just hopefully grab that.

   //   // Grab the floating point return value from the top of the floating point stack
   //   asm ("fstl fpuReturnValue");

   //   localFpuReturnVal = fpuReturnValue;

   localFpuReturnVal = VG_(get_FPU_stack_top)(currentTID);

   VG_(printf)("Exit function: %s - EAX: 0x%x fpuReturnValue: %x\n", fnname, EAX, localFpuReturnVal);

   // Check for longjmps (if the exit doesn't match the call on the top of
   // the stack, and the ESP doesn't look right -- need both, because
   // sometimes the names don't match (eg. __foo vs. foo) and sometimes the
   // ESPs don't match, I don't know why).
   //   while ( top(&topEntry) &&
   //	   !VG_STREQ(f, topEntry.name) &&
   //	   (ESP > (topEntry.EBP + 4)) ) { // ESP = EBP + 4
   //      unwinds++;
   //      pop_fn(0, 0, 0, 0, 0, 0);
   //   }

   pop_fn(fnname, EAX, EDX, localFpuReturnVal, EAXvalid, EDXvalid);
}

/*------------------------------------------------------------*/
/*--- Instrumentation                                      ---*/
/*------------------------------------------------------------*/

// DEPRECATED - We now only show functions which show up in DaikonFunctionInfoTable
/*
Requires:
Modifies:
Returns: whether the program should display a particular function (fn)
         with a particular filename (filename)
Effects:
*/
/* Bool want_to_show(Char* fn, Char* filename) */
/* { */
/*    UInt  i, j; */
/*    Char* dl_fns[] = { //"_dl_debug_initialize", */
/*                       //"_dl_runtime_resolve", */
/*                       "__i686.get_pc_thunk.bx", */
/*                       "__i686.get_pc_thunk.cx", */
/*                       //"_dl_lookup_versioned_symbol", */
/*                       //"do_lookup_versioned", */
/*                       //"do_lookup", */

/* 		      // from dl-runtime.c: */
/* 		      "fixup", */
/*                       NULL */
/*                     }; */

/*    // These were found empirically by observation of test runs: */
/*    Char* dl_files[] = { */
/*      // You need to manually pick out functions within dl-runtime.c: */
/*                         //"dl-runtime.c", */
/* 			"dl-minimal.c", */
/* 			"dl-version.c", */
/* 			"dl-deps.c", */
/* 			"dl-load.c", */
/* 			"dl-lookup.c", */
/* 			"vg_intercept.c", */
/* 			"rtld.c", */
/*                         "mac_replace_strmem.c", */
/*                         "vg_replace_malloc.c", */
/*                         "memcheck/mac_replace_strmem.c", */
/* 			NULL */
/*    }; */

/*    // If --show-all-funcs=yes, then always show */
/*    if (sp_clo_show_all_funcs) */
/*       return True; */

/*    // if starts with "_dl_", it is a dynamic linker function */
/*    if ( 0 == VG_(strncmp)(fn, "_dl_", 4) || */
/*         0 == VG_(strncmp)(fn, "__GI__dl_", 9)) */
/*       return False; */

/*    // If the filename starts with ../sysdeps, IGNORE IT */
/*    // This may be system dependent, so I dunno??!!?? */
/*    if ( 0 == VG_(strncmp)(filename, "../sysdeps", 10) ) */
/*      return False; */

/*    // If it's in dl_fns[], don't show */
/*    for (i = 0; NULL != dl_fns[i]; i++) { */
/*       if VG_STREQ(dl_fns[i], fn) */
/*          return False; */
/*    } */

/*    // If it's in dl_files[], don't show */
/*    for (j = 0; NULL != dl_files[j]; j++) { */
/*       if VG_STREQ(dl_files[j], filename) */
/*          return False; */
/*    } */

/*    return True; */
/* } */

/*
Requires:
Modifies: lots of global stuff
Returns:
Effects: All of the Kvasir initialization is performed right here;
         Memcheck mc_main.c calls this at the end of its own
         initialization and this must extract DWARF2 debugging
         information from the ELF executable, process the
         dwarf_entry_array, and create .decls and .dtrace files
*/

// Before processing command-line options
void kvasir_pre_clo_init()
{
   // Clear fn_stack
   VG_(memset)(fn_stack, 0, FN_STACK_SIZE * sizeof(*fn_stack));

   // Clear all global variables before processing command-line options:
   kvasir_decls_filename = 0;
   kvasir_dtrace_filename = 0;
   kvasir_print_debug_info = False;
   kvasir_ignore_globals = False;
   kvasir_ignore_static_vars = False;
   kvasir_dtrace_append = False;
   kvasir_dtrace_gzip = False;
   kvasir_output_fifo = False;

#ifdef KVASIR_DEVEL_BUILD
   kvasir_asserts_aborts_on = True;
#else
   kvasir_asserts_aborts_on = False;
#endif

   kvasir_decls_only = False;
   kvasir_limit_static_vars = False;
   kvasir_default_disambig = False;
   kvasir_dump_prog_pt_names_filename = 0;
   kvasir_dump_var_names_filename = 0;
   kvasir_trace_prog_pts_filename = 0;
   kvasir_trace_vars_filename = 0;
   kvasir_disambig_filename = 0;
   kvasir_program_stdout_filename = 0;
   kvasir_program_stderr_filename = 0;
}

// Initialize kvasir after processing command-line options
void kvasir_post_clo_init()
{
  // Assume that the filename is the FIRST string in
  // VG(client_argv) since that is the client argv array
  // after being parsed by the Valgrind core:
  char* filename = VG_(client_argv)[0];

  // Handle variables set by command-line options:
  char* DISAMBIG = ".disambig";
  int DISAMBIG_LEN = VG_(strlen)(DISAMBIG);

  DPRINTF("\nReading binary file \"%s\" [0x%x] (Assumes that filename is first argument in client_argv)\n\n",
	  filename, filename);
  DPRINTF("handleFunctionEntrance is at %p\n", handleFunctionEntrance);

  // --disambig results in the disambig filename being ${filename}.disambig
  // (overrides --disambig-file option)
  if (kvasir_default_disambig) {
    char* disambig_filename =
      VG_(calloc)(VG_(strlen)(filename) + DISAMBIG_LEN + 1,
	     sizeof(*disambig_filename));

    VG_(strcpy)(disambig_filename, filename);
    VG_(strcat)(disambig_filename, DISAMBIG);
    kvasir_disambig_filename = disambig_filename;
  }
  // --disambig-file=F results in the disambig filename being ${F}.disambig
  else if (kvasir_disambig_filename) {
    char* disambig_filename =
      VG_(calloc)(VG_(strlen)(kvasir_disambig_filename) + DISAMBIG_LEN + 1,
	     sizeof(*disambig_filename));

    VG_(strcpy)(disambig_filename, kvasir_disambig_filename);
    VG_(strcat)(disambig_filename, DISAMBIG);
    kvasir_disambig_filename = disambig_filename;
  }

  DPRINTF("\n%s\n\n", kvasir_disambig_filename);

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
  if (kvasir_decls_only || kvasir_decls_filename) {
    DPRINTF("\nSeparate .decls\n\n");
    actually_output_separate_decls_dtrace = True;
  }

  process_elf_binary_data(filename);
  daikon_preprocess_entry_array();
  createDeclsAndDtraceFiles(filename);
}

void kvasir_print_usage()
{
   VG_(printf)(
"    --debug             print Kvasir-internal debug messages [--no-debug]\n"
#ifdef KVASIR_DEVEL_BUILD
"    --asserts-aborts    turn on safety asserts and aborts (ON BY DEFAULT)\n"
"                        [--asserts-aborts]\n"
#else
"    --asserts-aborts    turn on safety asserts and aborts (OFF BY DEFAULT)\n"
"                        [--no-asserts-aborts]\n"
#endif
"    --ignore-globals     ignores all global variables [--no-ignore-globals]\n"
"    --ignore-static-vars ignores all static variables [--no-ignore-static-vars]\n"
"    --limit-static-vars  limits the output of static vars [--no-limit-static-vars]\n"
"    --bit-level-precision     Uses bit-level precision to produce more accurate\n"
"                              output at the expense of speed [--no-bit-level-precision]\n"
"    --nesting-depth=N   limits the maximum number of dereferences of any structure\n"
"                        to N [--nesting-depth=2]\n"
"                        (N must be an integer between 0 and 100)\n"
"    --struct-depth=N    limits the maximum number of dereferences of recursively\n"
"                        defined structures (i.e. linked lists) to N [--struct-depth=2]\n"
"                        (N must be an integer between 0 and 100)\n"
"    --dtrace-append     appends .dtrace data to the end of the existing file\n"
"                        [--no-dtrace-append]\n"
"    --output-fifo       create output files as named pipes [--no-output-fifo]\n"
"    --decls-only        exit after creating .decls file [--no-decls-only]\n"
"    --decls-file=<string>    the output .decls file location\n"
"                             [daikon-output/FILENAME.decls]\n"
"                             (forces generation of separate .decls file)\n"
"    --dtrace-file=<string>   the output .dtrace file location\n"
"                             [daikon-output/FILENAME.dtrace]\n"
"    --dtrace-gzip            compresses .dtrace data [--no-dtrace-gzip]\n"
"                             (Automatically ON if --dtrace-file string ends in '.gz')\n"
"    --dump-ppt-file=<string> outputs all program point names to a file\n"
"    --dump-var-file=<string> outputs all variable names to a file\n"
"    --ppt-list-file=<string> trace only the program points listed in this file\n"
"    --var-list-file=<string> trace only the variables listed in this file\n"
"    --disambig-file=<string> Reads in disambig file if exists; otherwise creates one\n"
"    --disambig               Uses <program name>.disambig as the disambig file\n"
"    --program-stdout=<file>  redirect instrumented program stdout to file\n"
"                             [Kvasir's stdout, or /dev/tty if --dtrace-file=-]\n"
"    --program-stderr=<file>  redirect instrumented program stderr to file\n"
   );
}

/* Like VG_BOOL_CLO, but of the form "--foo", "--no-foo" rather than
   "--foo=yes", "--foo=no". Note that qq_option should not have a
   leading "--". */

#define VG_YESNO_CLO(qq_option, qq_var) \
   if (VG_CLO_STREQ(arg, "--"qq_option)) { (qq_var) = True; } \
   else if (VG_CLO_STREQ(arg, "--no-"qq_option))  { (qq_var) = False; }


// Processes command-line options
Bool kvasir_process_cmd_line_option(Char* arg)
{
   VG_STR_CLO(arg, "--decls-file", kvasir_decls_filename)
   else VG_STR_CLO(arg, "--dtrace-file",    kvasir_dtrace_filename)
   else VG_BOOL_CLO(arg, "debug",          kvasir_print_debug_info)
   else VG_BOOL_CLO(arg, "ignore-globals", kvasir_ignore_globals)
   else VG_BOOL_CLO(arg, "ignore-static-vars", kvasir_ignore_static_vars)
   else VG_BOOL_CLO(arg, "dtrace-append",  kvasir_dtrace_append)
   else VG_BOOL_CLO(arg, "dtrace-gzip",    kvasir_dtrace_gzip)
   else VG_BOOL_CLO(arg, "output-fifo",    kvasir_output_fifo)
   else VG_BOOL_CLO(arg, "asserts-aborts", kvasir_asserts_aborts_on)
   else VG_BOOL_CLO(arg, "decls-only",     kvasir_decls_only)
   else VG_BOOL_CLO(arg, "limit-static-vars", kvasir_limit_static_vars)
   else VG_BOOL_CLO(arg, "bit-level-precision", kvasir_use_bit_level_precision)
   else VG_BNUM_CLO(arg, "--struct-depth",  MAX_STRUCT_INSTANCES, 0, 100) // [0 to 100]
   else VG_BNUM_CLO(arg, "--nesting-depth", MAX_NUM_STRUCTS_TO_DEREFERENCE, 0, 100) // [0 to 100]
   else VG_BNUM_CLO(arg, "--array-length-limit", kvasir_array_length_limit,
                    -1, 0x7fffffff)
   else VG_BOOL_CLO(arg, "disambig", kvasir_default_disambig)
   else VG_STR_CLO(arg, "--dump-ppt-file",  kvasir_dump_prog_pt_names_filename)
   else VG_STR_CLO(arg, "--dump-var-file",  kvasir_dump_var_names_filename)
   else VG_STR_CLO(arg, "--ppt-list-file",  kvasir_trace_prog_pts_filename)
   else VG_STR_CLO(arg, "--var-list-file",  kvasir_trace_vars_filename)
   else VG_STR_CLO(arg, "--disambig-file",  kvasir_disambig_filename)
   else VG_STR_CLO(arg, "--program-stdout", kvasir_program_stdout_filename)
   else VG_STR_CLO(arg, "--program-stderr", kvasir_program_stderr_filename)
   else
      return MAC_(process_common_cmd_line_option)(arg);

  return True;
}

/*------------------------------------------------------------*/
/*--- Init/fini                                            ---*/
/*------------------------------------------------------------*/

// This runs after Kvasir finishes
void kvasir_finish() {

  if (disambig_writing) {
    generateDisambigFile();
  }

  finishDtraceFile();
}

/*--------------------------------------------------------------------*/
/*--- end                                            kvasir_main.c ---*/
/*--------------------------------------------------------------------*/
