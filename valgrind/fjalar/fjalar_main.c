/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_main.c:

   This file contains most of the code to interact with the Valgrind
   core.  It is called from mc_main.c since mc_main.c is the
   launching-point for Fjalar.
*/

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <search.h>

#include "tool.h"
#include "generate_fjalar_entries.h"
#include "fjalar_main.h"
#include "fjalar_runtime.h"
#include "fjalar_tool.h"
#include "fjalar_select.h"
#include "disambig.h"
#include "mc_include.h"
#include "typedata.h"

// Global variables that are set by command-line options
Bool fjalar_debug = False;
Bool fjalar_ignore_globals = False;
Bool fjalar_ignore_static_vars = False;
Bool fjalar_limit_static_vars = False;
Bool fjalar_default_disambig = False;
Bool fjalar_smart_disambig = False;
Bool fjalar_use_bit_level_precision = False;
Bool fjalar_output_struct_vars = False;
Bool fjalar_flatten_arrays = False;
Bool fjalar_func_disambig_ptrs = False;
Bool fjalar_disambig_ptrs = False;
int  fjalar_array_length_limit = -1;

// adjustable via the --struct-depth=N option:
UInt MAX_VISIT_STRUCT_DEPTH = 4;
// adjustable via the --nesting-depth=N option:
UInt MAX_VISIT_NESTING_DEPTH = 2;

// These are used as both strings and boolean flags -
// They are initialized to 0 upon initiation so if they are
// never filled with values by the respective command-line
// options, then they can be treated as False
char* fjalar_dump_prog_pt_names_filename = 0;
char* fjalar_dump_var_names_filename = 0;
char* fjalar_trace_prog_pts_filename = 0;
char* fjalar_trace_vars_filename = 0;
char* fjalar_disambig_filename = 0;
char* fjalar_program_stdout_filename = 0;
char* fjalar_program_stderr_filename = 0;
char* fjalar_xml_output_filename = 0;

// The filename of the target executable:
char* executable_filename = 0;

static void handle_first_function_entrance();

// TODO: We cannot sub-class FunctionExecutionState unless we make
// this into an array of pointers:
FunctionExecutionState FunctionExecutionStateStack[FN_STACK_SIZE];
// The first free slot in FunctionExecutionStateStack
// right above the top element:
int fn_stack_first_free_index;
// The top element of the stack is:
//   FunctionExecutionStateStack[fn_stack_first_free_index]

// "Pushes" a new entry onto the stack by returning a pointer to it
// and incrementing fn_stack_first_free_index (Notice that this has
// slightly has different semantics than a normal stack push)
__inline__ FunctionExecutionState* fnStackPush() {
  tl_assert(fn_stack_first_free_index < FN_STACK_SIZE);
  fn_stack_first_free_index++;
  return &(FunctionExecutionStateStack[fn_stack_first_free_index - 1]);
}

// Returns the top element of the stack and pops it off
__inline__ FunctionExecutionState* fnStackPop() {
  tl_assert(fn_stack_first_free_index > 0);
  fn_stack_first_free_index--;
  return &(FunctionExecutionStateStack[fn_stack_first_free_index]);
}

// Returns the top element of the stack
__inline__ FunctionExecutionState* fnStackTop() {
  tl_assert(fn_stack_first_free_index >= 0);
  return &(FunctionExecutionStateStack[fn_stack_first_free_index - 1]);
}


void printFunctionExecutionStateStack()
{
  int i;
  for (i = fn_stack_first_free_index - 1; i >= 0; i--) {
    FunctionExecutionState* cur_fn = &FunctionExecutionStateStack[i];
    VG_(printf)("FunctionExecutionStateStack[%d] %s - EBP: 0x%x, lowestESP: 0x%x\n",
		i,
		cur_fn->func->fjalar_name,
		cur_fn->EBP,
		cur_fn->lowestESP);
  }
}

//extern char* prog_pts_tree; // from decls-output.c
static char atLeastOneFunctionHandled = 0;

// This gets updated whenever we encounter a Ist_IMark instruction.
// It is required to track function exits because the address does not
// come with the Ist_Exit IR instruction:
static Addr currentAddr = 0;

// This is called whenever we encounter an IMark statement.  From the
// IR documentation (Copyright (c) 2004-2005 OpenWorks LLP):
//
// IMark(literal guest address, length)
//
// Semantically a no-op.  However, indicates that the IR statements
// which follow it originally came from a guest instruction of the
// stated length at the stated guest address.  This information is
// needed by some kinds of profiling tools.

// We will utilize this information to pause the target program at
// function entrances.  This is called from mc_translate.c.
void handle_possible_entry(MCEnv* mce, Addr64 addr) {
  IRDirty  *di;
  FunctionEntry* curFuncPtr = 0;

  // Right now, for x86, we only care about 32-bit instructions

  // REMEMBER TO ALWAYS UPDATE THIS regardless of whether this is
  // truly a function entry so that handle_possible_exit() can work
  // properly:
  currentAddr = (Addr)(addr);

  // If this is truly a function entry and we are interested in
  // tracking this particular function ...  This ensures that we only
  // track functions which we have in FunctionTable!!!
  curFuncPtr = findFunctionEntryByStartAddr(currentAddr);

  if (curFuncPtr && !atLeastOneFunctionHandled) {
    handle_first_function_entrance();
  }

  if (curFuncPtr &&
      // Also, if fjalar_trace_prog_pts_filename is on (we are reading
      // in a ppt list file), then DO NOT generate IR code to call
      // helper functions for functions whose name is NOT located in
      // prog_pts_tree.  This will greatly speed up processing because
      // these functions are filtered out at translation-time, not at
      // run-time
      (!fjalar_trace_prog_pts_filename ||
       prog_pts_tree_entry_found(curFuncPtr))) {
    // The only argument to enter_function() is a pointer to the
    // FunctionEntry for the function that we are entering
    di = unsafeIRDirty_0_N(1/*regparms*/,
			   "enter_function",
			   &enter_function,
			   mkIRExprVec_1(IRExpr_Const(IRConst_U32((Addr)curFuncPtr))));

/*     di = unsafeIRDirty_0_N(2, */
/* 			   "enter_function", */
/* 			   &enter_function, */
/* 			   mkIRExprVec_2(IRExpr_Const(IRConst_U32((Addr)curFuncPtr)), */
/* 					 IRExpr_Const(IRConst_U32(currentAddr)))); */

    // For function entry, we are interested in observing the ESP so make
    // sure that it's updated by setting the proper annotations:
    di->nFxState = 1;
    di->fxState[0].fx     = Ifx_Read;
    di->fxState[0].offset = mce->layout->offset_SP;
    di->fxState[0].size   = mce->layout->sizeof_SP;

    stmt( mce->bb, IRStmt_Dirty(di) );
  }
}

// Handle a function exit statement, which contains a jump kind of
// 'Ret'.  It seems pretty accurate to cue off of currentAddr, a value
// that is updated every time an Ist_IMark statement is translated,
// which is quite often
void handle_possible_exit(MCEnv* mce, IRJumpKind jk) {
  if (Ijk_Ret == jk) {
    IRDirty  *di;

    FunctionEntry* curFuncPtr = findFunctionEntryByAddrSlow(currentAddr);

    if (curFuncPtr &&
	// Also, if fjalar_trace_prog_pts_filename is on (we are
	// reading in a ppt list file), then DO NOT generate IR code
	// to call helper functions for functions whose names are NOT
	// located in prog_pts_tree.  This will greatly speed up
	// processing because these functions are filtered out at
	// translation-time, not at run-time
	(!fjalar_trace_prog_pts_filename ||
	 prog_pts_tree_entry_found(curFuncPtr))) {

      // The only argument to exit_function() is a pointer to the
      // FunctionEntry for the function that we are exiting
      di = unsafeIRDirty_0_N(1/*regparms*/,
			     "exit_function",
			     &exit_function,
			     mkIRExprVec_1(IRExpr_Const(IRConst_U32((Addr)curFuncPtr))));

      // For function exit, we are interested in observing the ESP,
      // EAX, EDX, FPTOP, and FPREG[], so make sure that they are
      // updated by setting the proper annotations:
      di->nFxState = 4;
      di->fxState[0].fx     = Ifx_Read;
      di->fxState[0].offset = mce->layout->offset_SP;
      di->fxState[0].size   = mce->layout->sizeof_SP;

      // Now I'm totally hacking based upon the definition of
      // VexGuestX86State in vex/pub/libvex_guest_x86.h:
      // (This is TOTALLY x86 dependent right now, but oh well)
      di->fxState[1].fx     = Ifx_Read;
      di->fxState[1].offset = 0; // offset of EAX
      di->fxState[1].size   = sizeof(UInt); // 4 bytes

      di->fxState[2].fx     = Ifx_Read;
      di->fxState[2].offset = 8; // offset of EDX
      di->fxState[2].size   = sizeof(UInt); // 4 bytes

      di->fxState[3].fx     = Ifx_Read;
      di->fxState[3].offset = 60; // offset of FPTOP
      // Size of FPTOP + all 8 elements of FPREG
      di->fxState[3].size   = sizeof(UInt) + (8 * sizeof(ULong));

      stmt( mce->bb, IRStmt_Dirty(di) );
    }
  }
}


/*
This is the hook into Valgrind that is called whenever the target
program enters a function.  Pushes an entry onto the top of
FunctionExecutionStateStack and calls out to a handler function
implemented by the Fjalar tool.
*/
VGA_REGPARM(1)
void enter_function(FunctionEntry* f)
{
  FunctionExecutionState* newEntry = fnStackPush();

  Addr  ESP = VG_(get_SP)(VG_(get_running_tid)());
  // Assign %esp - 4 to %ebp - empirically tested to be
  // correct for calling conventions
  Addr  EBP = ESP - 4;

  FJALAR_DPRINTF("Enter function: %s - StartPC: %p\n",
	  f->fjalar_name, (void*)f->startPC);

  int formalParamStackByteSize =
    determineFormalParametersStackByteSize(f);

  newEntry->func = f;
  newEntry->EBP = EBP;
  newEntry->lowestESP = ESP;
  newEntry->EAX = 0;
  newEntry->EDX = 0;
  newEntry->FPU = 0;

  // Initialize virtual stack and copy parts of the Valgrind stack
  // into that virtual stack
  if (formalParamStackByteSize > 0) {
    // For some reason, VG_(calloc) doesn't work here:
    // This is the error msg. that it gives:
    //   the `impossible' happened:
    //   add_MAC_Chunk: shadow area is accessible
    newEntry->virtualStack = calloc(formalParamStackByteSize, sizeof(char));
    newEntry->virtualStackByteSize = formalParamStackByteSize;

    VG_(memcpy)(newEntry->virtualStack, (void*)EBP, (formalParamStackByteSize * sizeof(char)));
    // VERY IMPORTANT!!! Copy all the A & V bits over from EBP to virtualStack!!!
    // (As a consequence, this copies over the tags as well - look in mc_main.c)
    mc_copy_address_range_state(EBP, (Addr)(newEntry->virtualStack), formalParamStackByteSize);
  }
  else {
    // Watch out for null pointer segfaults here:
    newEntry->virtualStack = 0;
    newEntry->virtualStackByteSize = 0;
  }

  // Do this AFTER initializing virtual stack and lowestESP
  fjalar_tool_handle_function_entrance(newEntry);
}

/*
This is the hook into Valgrind that is called whenever the target
program exits a function.  Initializes the top entry of
FunctionExecutionStateStack with return values from EAX, EDX, and FPU,
then calls out to a handler function implemented by the Fjalar tool.
*/
VGA_REGPARM(1)
void exit_function(FunctionEntry* f)
{
  FunctionExecutionState* top = fnStackPop();
  int i;

  ThreadId currentTID = VG_(get_running_tid)();

  // Get the value at the simulated %EAX (integer and pointer return
  // values are stored here upon function exit)
  Addr EAX = VG_(get_EAX)(currentTID);

  // Get the value of the simulated %EDX (the high 32-bits of the long
  // long int return value is stored here upon function exit)
  Addr EDX = VG_(get_EDX)(currentTID);

  // Ok, in Valgrind 2.X, we needed to directly code some assembly to
  // grab the top of the floating-point stack, but Valgrind 3.0
  // provides a virtual FPU stack, so we can just grab that.  Plus, we
  // now have shadow V-bits for the FPU stack.
  double fpuReturnVal = VG_(get_FPU_stack_top)(currentTID);

  // 64 bits
  // Use SHADOW values of Valgrind simulated registers to get V-bits
  UInt EAXshadow = VG_(get_shadow_EAX)(currentTID);
  UInt EDXshadow = VG_(get_shadow_EDX)(currentTID);
  ULong FPUshadow = VG_(get_shadow_FPU_stack_top)(currentTID);

  // s is null if an "unwind" is popped off the stack (WHAT?)
  // Only do something if top->func matches func
  if (!(top->func->fjalar_name) || (top->func != f)) {
    VG_(printf)("MISMATCHED on exit_function! %s != f: %s\n",
		top->func->fjalar_name,
		f->fjalar_name);
    return;
  }

  top->EAX = EAX;
  top->EDX = EDX;
  top->FPU = fpuReturnVal;

  // Very important!  Set the A and V bits of the appropriate
  // FunctionExecutionState object and the tags from the (x86) guest
  // state as well:
  for (i = 0; i < 4; i++) {
    set_abit((Addr)(&(top->EAX)) + (Addr)i, VGM_BIT_VALID);
    set_abit((Addr)(&(top->EDX)) + (Addr)i, VGM_BIT_VALID);
    set_abit((Addr)(&(top->FPU)) + (Addr)i, VGM_BIT_VALID);

    set_vbyte((Addr)(&(top->EAX)) + (Addr)i, (UChar)((EAXshadow & 0xff) << (i * 8)));
    set_vbyte((Addr)(&(top->EDX)) + (Addr)i, (UChar)((EDXshadow & 0xff) << (i * 8)));
    set_vbyte((Addr)(&(top->FPU)) + (Addr)i, (UChar)((FPUshadow & 0xff) << (i * 8)));
  }

  for (i = 4; i < 8; i++) {
    set_abit((Addr)(&(top->FPU)) + (Addr)i, VGM_BIT_VALID);
    set_vbyte((Addr)(&(top->FPU)) + (Addr)i, (UChar)((FPUshadow & 0xff) << (i * 8)));
  }

  fjalar_tool_handle_function_exit(top);

  // Destroy the memory allocated by virtualStack
  // AFTER the tool has handled the exit
  if (top->virtualStack) {
    // For some reason, VG_(calloc) still doesn't work!!!
    // This is the error msg. that it gives:
    //   the `impossible' happened:
    //   add_MAC_Chunk: shadow area is accessible
    free(top->virtualStack);
  }
}

// This code is run when Valgrind stops execution at the first
// function entrance.  At this point, we have full access to
// Valgrind's name demangling mechanism so we can perform the rest of
// our initialization code that requires this functionality.
static void handle_first_function_entrance() {
  // Right before we handle the first function entrance, update all
  // the fjalar_name fields of all entries in FunctionTable:
  updateAllFunctionEntryNames();

  // Let the tool do its initialization:
  fjalar_tool_handle_first_function_entrance();
  atLeastOneFunctionHandled = 1;

  // If we want to dump program point, variable, or .disambig info to
  // output files, do it here, close the appropriate files, and then
  // exit (notice that this supports writing to more than 1 kind of
  // file before exiting):
  if (fjalar_dump_prog_pt_names_filename ||
      fjalar_dump_var_names_filename ||
      (fjalar_disambig_filename && disambig_writing)) {
    if (fjalar_dump_prog_pt_names_filename) {
      tl_assert(prog_pt_dump_fp);
      outputProgramPointsToFile();
      VG_(printf)("\nDone generating program point list (ppt-list) file %s\n",
                  fjalar_dump_prog_pt_names_filename);
      fclose(prog_pt_dump_fp);
      prog_pt_dump_fp = 0;
    }

    if (fjalar_dump_var_names_filename) {
      tl_assert(var_dump_fp);
      outputVariableNamesToFile();
      VG_(printf)("\nDone generating variable list (var-list) file %s\n",
                  fjalar_dump_var_names_filename);
      fclose(var_dump_fp);
      var_dump_fp = 0;
    }

    if (fjalar_disambig_filename && disambig_writing) {
      tl_assert(disambig_fp);
      // TODO: Write .disambig entries to file
      fclose(disambig_fp);
    }

    VG_(exit)(0);
  }
}


// Opens the appropriate files for reading or writing to handle
// selective program point tracing, selective variable tracing, and
// pointer type disambiguation, and make the proper calls to
// initialize those files if necessary
static void open_files_and_load_data() {

  if (fjalar_xml_output_filename) {
    xml_output_fp = fopen(fjalar_xml_output_filename, "w");
    outputAllXMLDeclarations();
    VG_(printf)("\nDone outputting XML file %s\n",
                fjalar_xml_output_filename);
  }
  else {
    xml_output_fp = 0;
  }

  if (fjalar_dump_prog_pt_names_filename) {
    prog_pt_dump_fp = fopen(fjalar_dump_prog_pt_names_filename, "w");
  }
  else {
    prog_pt_dump_fp = 0;
  }

  if (fjalar_dump_var_names_filename) {
    var_dump_fp = fopen(fjalar_dump_var_names_filename, "w");
  }
  else {
    var_dump_fp = 0;
  }

  if (fjalar_trace_prog_pts_filename) {
    if ((trace_prog_pts_input_fp =
	 fopen(fjalar_trace_prog_pts_filename, "r"))) {
      VG_(printf)( "\nBegin processing program point list file \"%s\" ...\n",
		   fjalar_trace_prog_pts_filename);
      initializeProgramPointsTree();
      VG_(printf)( "Done processing program point list file \"%s\"\n",
		   fjalar_trace_prog_pts_filename);
    }
    else {
      VG_(printf)( "\nError: \"%s\" is an invalid filename for the program point list file specified by the --ppt-list-file option.\n\nExiting.\n\n",
		   fjalar_trace_prog_pts_filename);

      VG_(exit)(1);
    }
  }

  if (fjalar_trace_vars_filename) {
    if ((trace_vars_input_fp
	 = fopen(fjalar_trace_vars_filename, "r"))) {
      VG_(printf)( "\nBegin processing variable list file \"%s\" ...\n",
		   fjalar_trace_vars_filename);
      initializeVarsTree();
      VG_(printf)( "Done processing variable list file \"%s\"\n",
		   fjalar_trace_vars_filename);
    }
    else {
      VG_(printf)( "\nError: \"%s\" is an invalid filename for the variable list file specified by the --var-list-file option.\n\nExiting.\n\n",
		   fjalar_trace_vars_filename);

      VG_(exit)(1);
    }
  }

  if (fjalar_disambig_filename) {
    // Try to open it for reading, but if it doesn't exist, create a
    // new file by writing to it
    if ((disambig_fp =
	 fopen(fjalar_disambig_filename, "r"))) {
      FJALAR_DPRINTF("\n\nREADING %s\n", fjalar_disambig_filename);
      disambig_writing = False;
    }
    else if ((disambig_fp =
	      fopen(fjalar_disambig_filename, "wx"))) {
      FJALAR_DPRINTF("\n\nWRITING %s\n", fjalar_disambig_filename);
      disambig_writing = True;

      // Hack for correctly observing struct pointer/array values
      // when using --smart-disambig.
      // If we are writing a .disambig file and using run time
      // observations of the struct behavior to determine whether
      // a struct pointer always pointed to one element or more than
      // one element, we must always process base struct variables
      // or else those observations will be missed.
      if (fjalar_smart_disambig) {
	fjalar_output_struct_vars = True;
      }
    }
  }
}


/*
Requires:
Modifies: lots of global stuff
Returns:
Effects: All of the Fjalar initialization is performed right here;
         Memcheck mc_main.c calls this at the end of its own
         initialization and this must extract DWARF2 debugging
         information from the ELF executable, process the
         dwarf_entry_array, and create .decls and .dtrace files
*/

// Before processing command-line options
void fjalar_pre_clo_init()
{
  // Clear FunctionExecutionStateStack
  VG_(memset)(FunctionExecutionStateStack, 0,
	      FN_STACK_SIZE * sizeof(*FunctionExecutionStateStack));

  // TODO: Do we need to clear all global variables before processing
  // command-line options?  We don't need to as long as this function
  // is only run once at the beginning of program execution

  // Make sure to execute this last!
  fjalar_tool_pre_clo_init();
}

// Initialize Fjalar after processing command-line options
void fjalar_post_clo_init()
{
  // Assume that the filename is the FIRST string in
  // VG(client_argv) since that is the client argv array
  // after being parsed by the Valgrind core:
  executable_filename = VG_(client_argv)[0];

  // Handle variables set by command-line options:
  char* DISAMBIG = ".disambig";
  int DISAMBIG_LEN = VG_(strlen)(DISAMBIG);

  FJALAR_DPRINTF("\nReading binary file \"%s\" [0x%x] (Assumes that filename is first argument in client_argv)\n\n",
	  executable_filename, executable_filename);

  // --disambig results in the disambig filename being ${executable_filename}.disambig
  // (overrides --disambig-file option)
  if (fjalar_default_disambig) {
    char* disambig_filename =
      VG_(calloc)(VG_(strlen)(executable_filename) + DISAMBIG_LEN + 1,
	     sizeof(*disambig_filename));

    VG_(strcpy)(disambig_filename, executable_filename);
    VG_(strcat)(disambig_filename, DISAMBIG);
    fjalar_disambig_filename = disambig_filename;
  }

  FJALAR_DPRINTF("\n%s\n\n", fjalar_disambig_filename);

  // Calls into typedata.c:
  initialize_typedata_structures();

  // Calls into readelf.c:
  process_elf_binary_data(executable_filename);

  // Calls into generate_fjalar_entries.c:
  initializeAllFjalarData();

  // Call this AFTER data has been initialized by
  // generate_fjalar_entries.c:
  open_files_and_load_data();

  // Make sure to execute this last!
  fjalar_tool_post_clo_init();
}


void fjalar_print_usage()
{
   VG_(printf)("\n  User options for Fjalar framework:\n");

   VG_(printf)(
"\n  Selective program tracing:\n"
"    --ppt-list-file=<string> Trace only the program points listed in this file\n"
"    --var-list-file=<string> Trace only the variables listed in this file\n"
"    --dump-ppt-file=<string> Outputs all program point names to a file\n"
"    --dump-var-file=<string> Outputs all variable names to a file\n"
"    --ignore-globals         Ignores all global variables [--no-ignore-globals]\n"
"    --ignore-static-vars     Ignores all static variables [--no-ignore-static-vars]\n"
"    --limit-static-vars      Limits the output of static vars [--no-limit-static-vars]\n"

"\n  Pointer type disambiguation:\n"
"    --disambig-file=<string> Reads in disambig file if exists; otherwise creates one\n"
"    --disambig               Uses <program name>.disambig as the disambig file\n"
"    --smart-disambig         Infers sensible values for each entry in .disambig file\n"
"                             generated using the --disambig or --disambig-file options\n"
"    --func-disambig-ptrs     Treats function parameter and return value pointer\n"
"                             variables as pointing to a single element\n"
"    --disambig-ptrs          Treats all pointer vars. as pointing to a single element\n"

"\n  Misc. options:\n"
"    --flatten-arrays         Force flattening of all statically-sized arrays\n"
"    --output-struct-vars     Outputs struct variables along with their contents\n"
"    --bit-level-precision    Uses bit-level precision to produce more accurate\n"
"                             output at the expense of speed [--no-bit-level-precision]\n"
"    --nesting-depth=N        Limits the maximum number of dereferences of any\n"
"                             structure to N (default is 2)\n"
"    --struct-depth=N         Limits the maximum number of dereferences of recursively\n"
"                             defined structures (i.e. linked lists) to N (default is 4)\n"
"                             (N must be an integer between 0 and 100)\n"
"    --fjalar-debug           Print internal Fjalar debug messages\n"
"    --program-stdout=<string>   The name of the file to use for stdout\n"
"    --program-stderr=<string>   The name of the file to use for stderr\n"
"    --xml-output-file=<string>  Output declarations in XML format to a file\n"
   );

   // Make sure to execute this last!
   fjalar_tool_print_usage();
}

/* Like VG_BOOL_CLO, but of the form "--foo", "--no-foo" rather than
   "--foo=yes", "--foo=no". Note that qq_option should not have a
   leading "--". */

#define VG_YESNO_CLO(qq_option, qq_var) \
   if (VG_CLO_STREQ(arg, "--"qq_option)) { (qq_var) = True; } \
   else if (VG_CLO_STREQ(arg, "--no-"qq_option))  { (qq_var) = False; }

// Processes command-line options
// (Called from MAC_(process_common_cmd_line_option)() in mac_needs.c)
Bool fjalar_process_cmd_line_option(Char* arg)
{
  VG_YESNO_CLO("fjalar-debug", fjalar_debug)
  else VG_YESNO_CLO("ignore-globals", fjalar_ignore_globals)
  else VG_YESNO_CLO("ignore-static-vars", fjalar_ignore_static_vars)
  else VG_YESNO_CLO("limit-static-vars", fjalar_limit_static_vars)
  else VG_YESNO_CLO("disambig", fjalar_default_disambig)
  else VG_YESNO_CLO("smart-disambig", fjalar_smart_disambig)
  else VG_YESNO_CLO("bit-level-precision", fjalar_use_bit_level_precision)
  else VG_YESNO_CLO("output-struct-vars", fjalar_output_struct_vars)
  else VG_YESNO_CLO("flatten-arrays", fjalar_flatten_arrays)
  else VG_YESNO_CLO("func-disambig-ptrs", fjalar_func_disambig_ptrs)
  else VG_YESNO_CLO("disambig-ptrs", fjalar_disambig_ptrs)
  else VG_BNUM_CLO(arg, "--array-length-limit", fjalar_array_length_limit,
		   -1, 0x7fffffff)

  else VG_BNUM_CLO(arg, "--struct-depth",  MAX_VISIT_STRUCT_DEPTH, 0, 100)  // [0 to 100]
  else VG_BNUM_CLO(arg, "--nesting-depth", MAX_VISIT_NESTING_DEPTH, 0, 100) // [0 to 100]

  else VG_STR_CLO(arg, "--dump-ppt-file",  fjalar_dump_prog_pt_names_filename)
  else VG_STR_CLO(arg, "--dump-var-file",  fjalar_dump_var_names_filename)
  else VG_STR_CLO(arg, "--ppt-list-file",  fjalar_trace_prog_pts_filename)
  else VG_STR_CLO(arg, "--var-list-file",  fjalar_trace_vars_filename)
  else VG_STR_CLO(arg, "--disambig-file",  fjalar_disambig_filename)
  else VG_STR_CLO(arg, "--program-stdout", fjalar_program_stdout_filename)
  else VG_STR_CLO(arg, "--program-stderr", fjalar_program_stderr_filename)
  else VG_STR_CLO(arg, "--xml-output-file", fjalar_xml_output_filename)
  else
    return fjalar_tool_process_cmd_line_option(arg);

  return True;
}


// This runs after the target program exits
void fjalar_finish() {

  // If fjalar_smart_disambig is on, then
  // we must create the .disambig file at the very end after
  // Fjalar has run though the entire program so that it can
  // determine whether each pointer variable has only referenced
  // one element or multiple elements throughout this particular execution
  if (disambig_writing && fjalar_smart_disambig) {
    generateDisambigFile();
  }

  // Make sure to execute this last!
  fjalar_tool_finish();
}
