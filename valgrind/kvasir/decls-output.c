/*
   This file is part of Kvasir, a Valgrind tool that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* decls-output.c:
   Functions for creating .decls and .dtrace files and outputting
   name and type information into a Daikon-compatible .decls file
*/

#include "mc_include.h"
#include "decls-output.h"
#include "dtrace-output.h"
#include "kvasir_main.h"
#include "kvasir_runtime.h"
#include "generate_daikon_data.h"
#include "dyncomp_runtime.h"
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/errno.h>
#include <assert.h>
#include <search.h>
#include <limits.h>

static int createFIFO(const char *filename);

// This increments every time outputDaikonVar is called and a full
// Daikon name is successfully generated.  It is used to index into
// the var_tags and new_tags arrays
int g_daikonVarIndex = 0;

FILE* decls_fp = 0; // File pointer for .decls file (this will point
                    // to the same thing as dtrace_fp by default since
                    // both .decls and .dtrace are outputted to .dtrace
                    // unless otherwise noted by the user)

FILE* dtrace_fp = 0; // File pointer for dtrace file (from dtrace-output.c)
static char *dtrace_filename; /* File name to open dtrace_fp on */

FILE* prog_pt_dump_fp = 0; // File pointer for dumping program points
FILE* var_dump_fp = 0; // File pointer for dumping variable names

FILE* trace_prog_pts_input_fp = 0; // File pointer for list of program points to trace
FILE* trace_vars_input_fp = 0; // File pointer for list of variables to trace

char* decls_folder = "daikon-output/";
static char* decls_ext = ".decls";
static char* dtrace_ext = ".dtrace";
static char* dereference = "[]";
static char* zeroth_elt = "[0]";
static char* dot = ".";
static char* arrow = "->";
static char* star = "*";

static char COMMENT_CHAR = '#';

const char* ENTRY_DELIMETER = "----SECTION----";
#define ENTRY_DELIMETER_LEN 21
const char* GLOBAL_STRING = "globals";
#define GLOBAL_STRING_LEN 7
const char* ENTER_PPT = ":::ENTER";
const char* EXIT_PPT = ":::EXIT0";

const char* MANGLED_TOKEN = "(mangled)";

extern char* kvasir_trace_prog_pts_filename;
extern char* kvasir_trace_vars_filename;

// GNU binary tree (built into search.h) (access using tsearch and
// tfind) which holds either the full Daikon name or the mangled name
// (for C++ only) of the program points which we are interested in
// tracing.  When we are trying to detect whether to instrument a
// particular DaikonFunctionInfo entry at translation-time within
// handle_possible_entry and handle_possible_exit, we know whether to
// look for the Daikon name or the mangled C++ name by simply querying
// whether the particular entry has a mangled C++ name.  If it has
// one, we should use it ... otherwise, use the Daikon name
char* prog_pts_tree = NULL;

// GNU binary tree which holds names of functions and trees of variables
// to trace within those functions (packed into a FunctionTree struct)
FunctionTree* vars_tree = NULL;

// Special entry for global variables
FunctionTree* globalFunctionTree = 0;

// TODO: Warning! We never free the memory used by prog_pts_tree and vars_tree
// but don't worry about it for now

// Maps tags to comparability numbers, which are assigned sequentially
// for every program point.  This is only used for DynComp.
// Key: tag (unsigned int)
// Value: comparability number (int) - notice that this is SIGNED because that
//                                     is what Daikon requires
struct genhashtable* g_compNumberMap = 0;

// This is the current sequential comparability number (only for
// DynComp).  It increments after it has been assigned as a value in
// g_compNumberMap, and it is reset back to 1 during every program
// point.
int g_curCompNumber = 1;

// adjustable via the --struct-depth=N option:
UInt MAX_VISIT_STRUCT_DEPTH = 4;
// adjustable via the --nesting-depth=N option:
UInt MAX_VISIT_NESTING_DEPTH = 2;

// This array can be indexed using the DaikonDeclaredType enum
static const char* DaikonDeclaredTypeString[] = {
  "no_declared_type", // Create padding
  "unsigned char", //D_UNSIGNED_CHAR,
  "char", //D_CHAR,
  "unsigned short", //D_UNSIGNED_SHORT,
  "short", //D_SHORT,
  "unsigned int", //D_UNSIGNED_INT,
  "int", //D_INT,
  "unsigned long long int", //D_UNSIGNED_LONG_LONG_INT,
  "long long int", //D_LONG_LONG_INT,
  "unsigned float", //D_UNSIGNED_FLOAT, // currently unused
  "float", //D_FLOAT,
  "unsigned double", //D_UNSIGNED_DOUBLE, // currently unused
  "double", //D_DOUBLE,
  "unsigned long double", //D_UNSIGNED_LONG_DOUBLE, // currently unused
  "long double", //D_LONG_DOUBLE,
  // This should NOT be used unless you created an unnamed struct/union!
  // Use DaikonVariable::collectionName instead
  "enumeration", //D_ENUMERATION
  "struct", //D_STRUCT
  "union", //D_UNION
  "function", //D_FUNCTION
  "void", //D_VOID
  "char", //D_CHAR_AS_STRING
  "bool", //D_BOOL
};

// This array can be indexed using the DaikonRepType enum
static const char* DaikonRepTypeString[] = {
  "no_rep_type", //R_NO_TYPE, // Create padding
  "int", //R_INT,
  "double", //R_DOUBLE,
  "hashcode", //R_HASHCODE,
  "java.lang.String" //R_STRING
};

// This stack represents the full name of the variable that we
// currently want to output (Only puts REFERENCES to strings in
// fullNameStack; does not do any allocations)
char* fullNameStack[MAX_STRING_STACK_SIZE];
int fullNameStackSize = 0;

void stringStackPush(char** stringStack, int* pStringStackSize, char* str)
{
  tl_assert(str && *pStringStackSize < MAX_STRING_STACK_SIZE);

  // Don't allow null strings at all:
  //  if (!str) {
  //    VG_(printf)( "Null string passed to push!\n");
  //    /* abort(); */
  //    str = "<null>";
  //  }

  stringStack[*pStringStackSize] = str;
  (*pStringStackSize)++;
}

char* stringStackPop(char** stringStack, int* pStringStackSize)
{
  char* temp;
  tl_assert(*pStringStackSize > 0);

  temp = stringStack[*pStringStackSize - 1];
  (*pStringStackSize)--;

  return temp;
}

char* stringStackTop(char** stringStack, int stringStackSize)
{
  return stringStack[stringStackSize - 1];
}

void stringStackClear(int* pStringStackSize)
{
  (*pStringStackSize) = 0;
}

// Returns: Total length of all strings on stringStack
int stringStackStrLen(char** stringStack, int stringStackSize)
{
  int i;
  int total = 0;
  for (i = stringStackSize - 1; i >=0; i--)
    {
      total+=VG_(strlen)(stringStack[i]);
    }
  return total;
}

void stringStackPrint(char** stringStack, int stringStackSize)
{
  int i;
  for (i = stringStackSize - 1; i >= 0; i--)
    {
      printf("stringStack[%d] = %s\n", i, stringStack[i]);
    }
}

// Takes all of the strings on stringStack, copies them into a newly
// calloc'ed string (in a queue-like FIFO order), and returns a
// pointer to that string.
char* stringStackStrdup(char** stringStack, int stringStackSize)
{
  // Extra 1 for trailing '\0'
  int totalStrLen = stringStackStrLen(stringStack, stringStackSize) + 1;
  char* fullName = (char*)VG_(calloc)(totalStrLen, sizeof(char));
  int i;

  for (i = 0; i < stringStackSize; i++) {
    VG_(strcat)(fullName, stringStack[i]);
  }
  return fullName;
}

// if (actually_output_separate_decls_dtrace):
//   Create a decls file with the name "daikon-output/x.decls"
//   where x is the application name (by default)
//   and initializes the file pointer decls_fp.
//   Also creates a corresponding .dtrace file, but doesn't open it yet.
// else: --- (DEFAULT)
//   Create a dtrace file and initialize both decls_fp and dtrace_fp
//   to point to it
char createDeclsAndDtraceFiles(char* appname)
{
  char* dirname = 0;
  char* filename = 0;
  char* newpath_decls = 0;
  char* newpath_dtrace;
  int success = 0;
  int ret;

  // Free VisitedStructsTable if it has been allocated
  if (VisitedStructsTable)
    {
      genfreehashtable(VisitedStructsTable);
    }
  VisitedStructsTable = 0;

  // Handle command-line options:
  if (kvasir_dump_prog_pt_names_filename)
    {
      prog_pt_dump_fp = fopen(kvasir_dump_prog_pt_names_filename, "w");
      // TODO: Hack! Generate no output when we dump program point or
      //       variable names - this is probably not as efficient as it
      //       could be since it still runs through all of the code
      //       but outputs to "/dev/null" instead of skipping the code altogether
      kvasir_decls_filename = "/dev/null";
      kvasir_dtrace_filename = "/dev/null";
    }
  else
    {
      prog_pt_dump_fp = 0;
    }

  if (kvasir_dump_var_names_filename)
    {
      var_dump_fp = fopen(kvasir_dump_var_names_filename, "w");
      // TODO: Hack! Generate no output when we dump variable names -
      //       this is probably not as efficient as it could be since
      //       it still runs through all of the code but outputs to
      //       "/dev/null" instead of skipping the code altogether
      kvasir_decls_filename = "/dev/null";
      kvasir_dtrace_filename = "/dev/null";
    }
  else
    {
      var_dump_fp = 0;
    }

  if (kvasir_trace_prog_pts_filename)
    {
      if ((trace_prog_pts_input_fp = fopen(kvasir_trace_prog_pts_filename, "r")))
	{
	  VG_(printf)( "\nBegin processing program point list file \"%s\" ...\n",
		  kvasir_trace_prog_pts_filename);
	  initializeProgramPointsTree();
	  VG_(printf)( "Done processing program point list file \"%s\"\n",
		  kvasir_trace_prog_pts_filename);
	}
      else
	{
	  VG_(printf)( "\nError: \"%s\" is an invalid filename for the program point list file specified by the --ppt-list-file option.\n\nExiting.\n\n",
		  kvasir_trace_prog_pts_filename);

          VG_(exit)(1);
	}
    }

  if (kvasir_trace_vars_filename)
    {
      if ((trace_vars_input_fp = fopen(kvasir_trace_vars_filename, "r")))
	{
	  VG_(printf)( "\nBegin processing variable list file \"%s\" ...\n",
		  kvasir_trace_vars_filename);
	  initializeVarsTree();
	  VG_(printf)( "Done processing variable list file \"%s\"\n",
		  kvasir_trace_vars_filename);
	}
      else
	{
	  VG_(printf)( "\nError: \"%s\" is an invalid filename for the variable list file specified by the --var-list-file option.\n\nExiting.\n\n",
		  kvasir_trace_vars_filename);

          VG_(exit)(1);
	}
    }

  if (kvasir_disambig_filename)
    {
      // Try to open it for reading, but if it doesn't exist,
      // create a new file by writing to it
      if ((disambig_fp = fopen(kvasir_disambig_filename, "r")))
	{
	  DPRINTF("\n\nREADING %s\n", kvasir_disambig_filename);
	  disambig_writing = False;
	}
      else if ((disambig_fp = fopen(kvasir_disambig_filename, "wx")))
	{
	  DPRINTF("\n\nWRITING %s\n", kvasir_disambig_filename);
	  disambig_writing = True;

          // Hack for correctly observing struct pointer/array values
          // when using --smart-disambig.
          // If we are writing a .disambig file and using run time
          // observations of the struct behavior to determine whether
          // a struct pointer always pointed to one element or more than
          // one element, we must always process base struct variables
          // or else those observations will be missed.
          if (kvasir_smart_disambig) {
            kvasir_output_struct_vars = True;
          }
	}
    }

  // Step 1: Make a path to .decls and .dtrace files
  //         relative to daikon-output/ folder

  if (!splitDirectoryAndFilename(appname, &dirname, &filename))
    {
      VG_(printf)( "Failed to parse path: %s\n", appname);
      return 0;
    }

  DPRINTF("**************\ndirname=%s, filename=%s\n***********\n",
	  dirname, filename);

  if (actually_output_separate_decls_dtrace) {
    if (kvasir_decls_filename) {
      newpath_decls = VG_(strdup)(kvasir_decls_filename);
    }
    else {
      newpath_decls = (char*)VG_(malloc)((VG_(strlen)(decls_folder) +
					  VG_(strlen)(filename) +
					  VG_(strlen)(decls_ext) + 1) *
					 sizeof(char));

      VG_(strcpy)(newpath_decls, decls_folder);
      VG_(strcat)(newpath_decls, filename);
      VG_(strcat)(newpath_decls, decls_ext);
    }

    if (kvasir_dtrace_filename) {
      newpath_dtrace = VG_(strdup)(kvasir_dtrace_filename);
    }
    else {
      newpath_dtrace = (char*)VG_(malloc)((VG_(strlen)(decls_folder) +
					   VG_(strlen)(filename) +
					   VG_(strlen)(dtrace_ext) + 1) *
					  sizeof(char));

      VG_(strcpy)(newpath_dtrace, decls_folder);
      VG_(strcat)(newpath_dtrace, filename);
      VG_(strcat)(newpath_dtrace, dtrace_ext);
    }
  }
  else { // DEFAULT - just .dtrace
    if (kvasir_dtrace_filename) {
      newpath_dtrace = VG_(strdup)(kvasir_dtrace_filename);
    }
    else {
      newpath_dtrace = (char*)VG_(malloc)((VG_(strlen)(decls_folder) +
					   VG_(strlen)(filename) +
					   VG_(strlen)(dtrace_ext) + 1) *
					  sizeof(char));

      VG_(strcpy)(newpath_dtrace, decls_folder);
      VG_(strcat)(newpath_dtrace, filename);
      VG_(strcat)(newpath_dtrace, dtrace_ext);
    }
  }

  DPRINTF("decls=%s, dtrace=%s\n", newpath_decls, newpath_dtrace);
  DPRINTF("Command-line options: decls_filename=%s "
	  "dtrace_filename=%s "
	  "print_debug_info=%d "
	  "no_globals=%d "
	  "limit_static_vars=%d "
	  "dtrace_append=%d "
	  "dtrace_gzip=%d "
	  "dump_prog_pt_names_filename=%s "
	  "dump_var_names_filename=%s "
	  "trace_prog_pts_filename=%s "
	  "trace_vars_filename=%s\n",

	  kvasir_decls_filename,
	  kvasir_dtrace_filename,
	  kvasir_print_debug_info,
	  kvasir_ignore_globals,
	  kvasir_limit_static_vars,
	  kvasir_dtrace_append,
	  kvasir_dtrace_gzip,
	  kvasir_dump_prog_pt_names_filename,
	  kvasir_dump_var_names_filename,
	  kvasir_trace_prog_pts_filename,
	  kvasir_trace_vars_filename);

  // Step 2: Make the daikon-output/ directory
  ret = mkdir(decls_folder, 0777); // more abbreviated UNIX form
  if (ret == -1 && errno != EEXIST)
    VG_(printf)( "Couldn't create %s: %s\n", decls_folder, strerror(errno));

  // ASSUME mkdir succeeded! (or that the directory already exists)

  // Step 3: Make the .decls and .dtrace FIFOs, if requested
  if (kvasir_output_fifo) {
    if (actually_output_separate_decls_dtrace) {
      if (!createFIFO(newpath_decls))
	VG_(printf)( "Trying as a regular file instead.\n");
      if (!createFIFO(newpath_dtrace))
	VG_(printf)( "Trying as a regular file instead.\n");
    }
    else {
      if (!createFIFO(newpath_dtrace))
	VG_(printf)( "Trying as a regular file instead.\n");
    }
  }

  dtrace_filename = VG_(strdup)(newpath_dtrace); /* But don't open it til later */

  // Step 4: Open the .decls file for writing
  if (actually_output_separate_decls_dtrace) {
    success = (decls_fp = fopen(newpath_decls, "w")) != 0;

    if (!success)
      VG_(printf)( "Failed to open %s for declarations: %s\n",
		   newpath_decls, strerror(errno));
  }
  else { // Default
    openTheDtraceFile();

    // decls_fp and dtrace_fp both point to the .dtrace file
    if (print_declarations) {
      decls_fp = dtrace_fp;
    }
    else {
      decls_fp = 0;
    }
  }

  VG_(free)(filename);
  VG_(free)(dirname);

  if (actually_output_separate_decls_dtrace) {
    if (!kvasir_decls_filename) {
      VG_(free)(newpath_decls);
    }
    if (!kvasir_dtrace_filename) {
      VG_(free)(newpath_dtrace);
    }
  }
  else {
    if (!kvasir_dtrace_filename) {
      VG_(free)(newpath_dtrace);
    }
  }

  return success;
}

void openTheDtraceFile(void) {
  openDtraceFile(dtrace_filename);
  VG_(free)(dtrace_filename);
  dtrace_filename = 0;
}

// Splits up the input string (passed as char* input)
// into two strings (dirname and filename) that are separated
// by the first '/' that is recognized parsing from right
// to left - this breaks up a full path into a filename
// and a directory:
// Before: input = "../tests/IntTest/IntTest"
// After:  *dirnamePtr = "../tests/IntTest/" *filenamePtr = "IntTest"
// Postcondition - *dirname and *filename are malloc'ed - must be FREE'd!!!
// Return 1 on success, 0 on failure
// TODO: This can be replaced with calls to the glibc dirname() and basename() functions
char splitDirectoryAndFilename(const char* input, char** dirnamePtr, char** filenamePtr)
{
  int len = VG_(strlen)(input);
  int i, j;

  // We need this to be static or else dirname and filename
  // will dereference to junk
  static char* filename = 0;
  static char* dirname = 0;

  if (len <= 0)
    return 0;

  for (i = len - 1; i >= 0; i--)
    {
      if ((input[i] == '/') && ((i + 1) < len))
        {
          //          printf("i=%d, len=%d\n", i, len);
          filename = VG_(malloc)((len - i) * sizeof(char));
          dirname = VG_(malloc)((i + 2) * sizeof(char));

          // I didn't get the regular strncpy to work properly ...
          //          strncpy(dirname, input, i + 1);
          //          strncpy(filename, input + i + 1, len - i - 1);

          // Make my own strncpy:
          for (j = 0; j <= i; j++)
            {
              dirname[j] = input[j];
              //              printf("dirname[%d]=%c\n", j, dirname[j]);
            }
          dirname[i + 1] = '\0';
          //          printf("dirname[%d]=%c\n", i + 1, dirname[i + 1]);
          for (j = i + 1; j < len; j++)
            {
              filename[j - i - 1] = input[j];
              //              printf("filename[%d]=%c\n", j - i - 1, filename[j - i - 1]);
            }
          filename[len - i - 1] = '\0';
          //          printf("filename[%d]=%c\n", len - i - 1, filename[len - i - 1]);


          *filenamePtr = filename;
          *dirnamePtr = dirname;

          return 1;
        }
    }
  // If we don't find a '/' anywhere, just set filename to equal input
  filename = VG_(strdup)(input);
  *filenamePtr = filename;
  return 1;
}

static int createFIFO(const char *filename) {
  int ret;
  ret = remove(filename);
  if (ret == -1 && errno != ENOENT) {
    VG_(printf)( "Couldn't replace old file %s: %s\n", filename,
	    strerror(errno));
    return 0;
  }
  ret = mkfifo(filename, 0666);
  if (ret == -1) {
    VG_(printf)( "Couldn't make %s as a FIFO: %s\n", filename,
	    strerror(errno));
    return 0;
  }
  return 1;
}

int compareStrings(const void *a, const void *b)
{
  return VG_(strcmp)((char*)a, (char*)b);
}

// Iterate through each line of the file trace_prog_pts_input_fp
// and VG_(strdup) each string into a new entry of prog_pts_tree
// Every line in a ppt program point file must be one of the following:
//
//  1.) A full Daikon name of the program point (as printed in
//  .decls/.dtrace) - This happens most of the time.
//
// e.g.:   FunctionNamesTest.c.staticFoo()
//
//  2.) The keyword '(mangled)' followed by the mangled program point
//  name then followed by the full Daikon name, all separated by
//  spaces.  This only happens for C++ function names that are
//  mangled.  The mangled name is what Kvasir actually uses and the
//  Daikon name is just there for human readability
//
// e.g.:   (mangled) _Z17firstFileFunctionv ..firstFileFunction()
//
//
// A list of addresses/program point names can be generated by running Kvasir
// with the --dump-ppt-file=<string> command-line option)
// Close the file when you're done with it
//
// (Comments are allowed - ignore all lines starting with COMMENT_CHAR)
//
// Here is an example of a program point list file with both regular
// and mangled names:
//
//     FunctionNamesTest.c.staticFoo()
//     (mangled) _Z17firstFileFunctioni ..firstFileFunction(int)
//     ..main()
//     second_file.c.staticFoo()
//     (mangled) _Z18secondFileFunctionv ..secondFileFunction()
//
void initializeProgramPointsTree()
{
  // TODO: This is crude and unsafe but works for now
  char line[200];

  while (fgets(line, 200, trace_prog_pts_input_fp))
    {
      char *newString;
      char *firstToken;
      int lineLen = VG_(strlen)(line);

      // Skip blank lines (those consisting of solely the newline character)
      // Also skip comment lines (those beginning with COMMENT_CHAR)
      if(('\n' == line[0]) ||
         (COMMENT_CHAR == line[0])) {
        //        VG_(printf)("skipping blank line ...\n");
        continue;
      }

      // Strip '\n' off the end of the line
      // NOTE: Only do this if the end of the line is a newline character.
      // If the very last line of a file is not followed by a newline character,
      // then blindly stripping off the last character will truncate the actual
      // string, which is undesirable.
      if (line[lineLen - 1] == '\n') {
        line[lineLen - 1] = '\0';
      }

      newString = VG_(strdup)(line);

      // Check out the first token
      firstToken = strtok(newString, " ");

      // If it matches MANGLED_TOKEN, then we are dealing with a mangled
      // C++ name so we just grab it as the second token
      if (0 == VG_(strcmp)(firstToken, MANGLED_TOKEN)) {
        char* secondToken = strtok(NULL, " ");
        //        VG_(printf)("mangled: %s\n", secondToken);
        tsearch((void*)VG_(strdup)(secondToken), (void**)&prog_pts_tree, compareStrings);
      }
      // Otherwise, that is the Daikon name of the function so grab it
      else {
        //        VG_(printf)("regular: %s\n", firstToken);
        tsearch((void*)VG_(strdup)(firstToken), (void**)&prog_pts_tree, compareStrings);
      }

      VG_(free)(newString);
    }

  fclose(trace_prog_pts_input_fp);
  trace_prog_pts_input_fp = 0;
}

int compareFunctionTrees(const void *a, const void *b)
{
  return VG_(strcmp)(((FunctionTree*) a)->function_daikon_name,
		     ((FunctionTree*) b)->function_daikon_name);
}

// Iterate through each line of the file trace_vars_input_fp
// and insert the line below ENTRY_DELIMETER into vars_tree as
// a new FunctionTree.  Then iterate through all variables within that function
// and add them to a tree of strings in FunctionTree.variable_tree
// Close the file when you're done
//
// (Comments are allowed - ignore all lines starting with COMMENT_CHAR)
//
/* This is an example of a variables output format:

----SECTION----
globals
StaticArraysTest_c/staticStrings
StaticArraysTest_c/staticStrings[]
StaticArraysTest_c/staticShorts
StaticArraysTest_c/staticShorts[]

----SECTION----
..f()
arg
strings
strings[]
return


----SECTION----
..b()
oneShort
manyShorts
manyShorts[]
return

----SECTION----
..main()
return

*/
void initializeVarsTree()
{
  // TODO: This is crude and unsafe but works for now
  char line[200];
  char nextLineIsFunction = 0;
  FunctionTree* currentFunctionTree = 0;
  while (fgets(line, 200, trace_vars_input_fp))
    {
      int lineLen = VG_(strlen)(line);

      // Skip blank lines (those consisting of solely the newline character)
      // Also skip comment lines (those beginning with COMMENT_CHAR)
      if(('\n' == line[0]) ||
         (COMMENT_CHAR == line[0])) {
        //        VG_(printf)("skipping blank line ...\n");
        continue;
      }

      // Strip '\n' off the end of the line
      // NOTE: Only do this if the end of the line is a newline character.
      // If the very last line of a file is not followed by a newline character,
      // then blindly stripping off the last character will truncate the actual
      // string, which is undesirable.
      if (line[lineLen - 1] == '\n') {
        line[lineLen - 1] = '\0';
      }

      // For some weird reason, it crashes when you don't use strncmp
      if (VG_(strncmp)(line, ENTRY_DELIMETER, ENTRY_DELIMETER_LEN) == 0)
	{
	  nextLineIsFunction = 1;
	}
      else
	{
	  // Create a new FunctionTree and insert it into vars_tree
	  if (nextLineIsFunction)
	    {
	      currentFunctionTree = VG_(malloc)(sizeof(*currentFunctionTree));
	      currentFunctionTree->function_daikon_name = VG_(strdup)(line);
	      currentFunctionTree->function_variables_tree = NULL; // Remember to initialize to null!

              //              VG_(printf)("Function: %s\n", currentFunctionTree->function_daikon_name);

	      tsearch((void*)currentFunctionTree, (void**)&vars_tree, compareFunctionTrees);

	      // Keep a special pointer for global variables to trace

              // For some weird reason, it crashes when you don't use strncmp
              if (VG_(strncmp)(line, GLOBAL_STRING, GLOBAL_STRING_LEN) == 0)
		{
		  globalFunctionTree = currentFunctionTree;
                  //                  VG_(printf)("globalFunctionTree: %p\n", globalFunctionTree);
		}
	    }
	  // Otherwise, create a new variable and stuff it into
	  // the function_variables_tree of the current function_tree
	  else
	    {
	      char* newString = VG_(strdup)(line);
	      tsearch((void*)newString, (void**)&(currentFunctionTree->function_variables_tree), compareStrings);
              //              VG_(printf)("variable: %s\n", newString);
	    }

	  nextLineIsFunction = 0;
	}
    }

  fclose(trace_vars_input_fp);
  trace_vars_input_fp = 0;
}

// This has different behavior depending on if faux_decls is on.  If
// faux_decls is on, then we do all the processing but don't actually
// output anything to the .decls file.
void outputDeclsFile(char faux_decls)
{
  // We need to update all DaikonFunctionInfo entries so that
  // they have the proper demangled names as obtained from Valgrind.
  // We must run this first before anything else happens or else
  // variable names will not be printed out correctly.
  updateAllDaikonFunctionInfoEntries();

  // Process .disambig at this time AFTER
  // updateAllDaikonFunctionInfoEntries() has been run
  if (disambig_fp && !disambig_writing) {
    VG_(printf)( "\nBegin processing disambiguation file \"%s\" ...\n",
		  kvasir_disambig_filename);

    processDisambigFile();

    VG_(printf)( "Done processing disambiguation file \"%s\"\n",
		  kvasir_disambig_filename);
  }

  if (print_declarations) {

    if (var_dump_fp)
      {
	fputs(ENTRY_DELIMETER, var_dump_fp);
	fputs("\n", var_dump_fp);
	fputs(GLOBAL_STRING, var_dump_fp);
	fputs("\n", var_dump_fp);
	printVariablesInVarList(0, 0, GLOBAL_VAR, 0, DECLS_FILE, 1,
				(globalFunctionTree ?
				 globalFunctionTree->function_variables_tree : 0), 0, 0);
	fputs("\n", var_dump_fp);
      }

    if (!faux_decls) {
      printDeclsHeader();
    }

    printAllFunctionDecls(faux_decls);

    // For DynComp, print this out at the end of execution
    if (!kvasir_with_dyncomp) {
      printAllObjectAndClassDecls();
    }

    // Clean-up:
    // Only close decls_fp if we are generating it separate of .dtrace
    if (prog_pt_dump_fp)
      {
        VG_(printf)("Done generating program point list (ppt-list) file %s\n",
                    kvasir_dump_prog_pt_names_filename);
        fclose(prog_pt_dump_fp);
        prog_pt_dump_fp = 0;
      }

    if (var_dump_fp)
      {
        VG_(printf)("Done generating variable list (var-list) file %s\n",
                    kvasir_dump_var_names_filename);
        fclose(var_dump_fp);
        var_dump_fp = 0;
      }

    // Punt everything if you're dumping program point or variable names
    // or if we only wanted the .decls file
    if (kvasir_dump_prog_pt_names_filename ||
        kvasir_dump_var_names_filename || kvasir_decls_only ||
        (disambig_writing && !kvasir_smart_disambig))
      {

        // If kvasir_smart_disambig is off, then write the .disambig now
        // and then punt so that we don't have to run the entire program
        if (disambig_writing && !kvasir_smart_disambig) {
          generateDisambigFile();
        }

        if (actually_output_separate_decls_dtrace) {
          fclose(decls_fp);
          decls_fp = 0;
        }
        else {
          finishDtraceFile();
        }
        VG_(exit)(0);
      }

    if (!faux_decls) {

      if (actually_output_separate_decls_dtrace) {
        fclose(decls_fp);
        decls_fp = 0;
      }
    }
  }
}

// Print .decls at the end of program execution and then close it
// (Only used when DynComp is on)
void DC_outputDeclsAtEnd() {
  printAllFunctionDecls(0);

  printAllObjectAndClassDecls();

  fclose(decls_fp);
  decls_fp = 0;
}

// Print out the Daikon .decls header depending on whether DynComp is
// activated or not
void printDeclsHeader()
{
  if (kvasir_with_dyncomp) {
    // VarComparability implicit is the DEFAULT so we don't need to
    // write anything here:
    //    fputs("VarComparability\nimplicit\n\n", decls_fp);
  }
  else {
    fputs("VarComparability\nnone\n\n", decls_fp);
  }
}

// Print out one individual function declaration
// Example:
/*
DECLARE
printHelloWorld():::ENTER
routebaga
double # isParam=true
double
1
turnip
char # isParam=true
int
2
*/
// char isEnter = 1 for function ENTER, 0 for EXIT
// faux_decls = True if we are making the FIRST pass with DynComp to count up
// how many Daikon variables exist at a program point so that we can initialize
// the proper data structures (no .decls output is made during this dry run)
// and faux_decls = False if we are really outputting .decls, which is in the
// beginning of execution without DynComp and at the END of execution with DynComp
void printOneFunctionDecl(DaikonFunctionInfo* funcPtr, char isEnter, char faux_decls)
{
  // This is a GLOBAL so be careful :)
  // Reset it before doing any traversals with outputDaikonVar
  g_daikonVarIndex = 0;

  // Only dump the function's Daikon name once during function EXIT
  // because we want to get return values for the var list file
  if (!isEnter) {
    if (prog_pt_dump_fp) {
      // If the mangled name exists, then print out the following:
      // (mangled) MANGLED_NAME DAIKON_NAME

      // Otherwise, just print out DAIKON_NAME

      if (funcPtr->mangled_name) {
        fprintf(prog_pt_dump_fp, "%s %s ", MANGLED_TOKEN, funcPtr->mangled_name);
      }

      fputs(funcPtr->daikon_name, prog_pt_dump_fp);
      fputs("\n", prog_pt_dump_fp);
    }

    if (var_dump_fp) {
      fputs(ENTRY_DELIMETER, var_dump_fp);
      fputs("\n", var_dump_fp);
      fputs(funcPtr->daikon_name, var_dump_fp);
      fputs("\n", var_dump_fp);
    }
  }

  // Optimization: If we are only dumping program point names
  // and NOT variable names, then we can simply quit at this point
  // because we are done (we don't need to print out anything
  // about the function's formal parameters)
  if (prog_pt_dump_fp && !var_dump_fp) {
    return;
  }

  if (!faux_decls) {
    fputs("DECLARE\n", decls_fp);
    fputs(funcPtr->daikon_name, decls_fp);

    if (isEnter)
      {
        fputs(ENTER_PPT, decls_fp);
        fputs("\n", decls_fp);
      }
    else
      {
        fputs(EXIT_PPT, decls_fp);
        fputs("\n", decls_fp);
      }

    // For outputting real .decls when running with DynComp,
    // initialize a global hashtable which associates tags with
    // sequentially-assigned comparability numbers
    if (kvasir_with_dyncomp) {
      // This is a GLOBAL so be careful :)
      g_compNumberMap = genallocatehashtable(NULL, // no hash function needed for u_int keys
                                             (int (*)(void *,void *)) &equivalentIDs);

      g_curCompNumber = 1;
    }
  }

  // Print out globals
  if (!kvasir_ignore_globals)
    {
      printVariablesInVarList(funcPtr, isEnter, GLOBAL_VAR, 0,
                              (faux_decls ? FAUX_DECLS_FILE : DECLS_FILE), 0,
			      (globalFunctionTree ?
			       globalFunctionTree->function_variables_tree : 0), 0, 0);
    }

  // Now print out one entry for every formal parameter (actual and derived)
  printVariablesInVarList(funcPtr, isEnter,
			  (isEnter ?
			   FUNCTION_ENTER_FORMAL_PARAM :
			   FUNCTION_EXIT_FORMAL_PARAM),
			  0, (faux_decls ? FAUX_DECLS_FILE : DECLS_FILE), !isEnter,
			  funcPtr->trace_vars_tree, 0, 0);

  // If EXIT, print out return value
  if (!isEnter)
    {
      printVariablesInVarList(funcPtr, isEnter, FUNCTION_RETURN_VAR, 0,
                              (faux_decls ? FAUX_DECLS_FILE : DECLS_FILE), !isEnter,
			      funcPtr->trace_vars_tree, 0 ,0);
    }

  if (var_dump_fp)
    {
      fputs("\n", var_dump_fp);
    }

  if (!faux_decls) {
    fputs("\n", decls_fp);
  }


  if (kvasir_with_dyncomp) {
    if (faux_decls) {
      // Allocate program point data structures if we are using DynComp:
      // (This should only be run once for every ppt)
      // This must be run at the end because its results depend on
      // g_daikonVarIndex being properly incremented
      allocate_ppt_structures(funcPtr, isEnter, g_daikonVarIndex);
    }
    else {
      genfreehashtable(g_compNumberMap);
    }
  }
}

// Returns 1 if the proper function name of cur_entry is found in
// prog_pts_tree and 0 otherwise.  If cur_entry->mangled_name exists,
// that is what we look for; otherwise, we look for
// cur_entry->daikon_name.
char prog_pts_tree_entry_found(DaikonFunctionInfo* cur_entry) {
  //  VG_(printf)("prog_pts_tree_entry_found() - mangled: %s | daikon: %s ",
  //              cur_entry->mangled_name,
  //              cur_entry->daikon_name);

  char* nameToFind = (cur_entry->mangled_name ?
                      cur_entry->mangled_name : cur_entry->daikon_name);

  if (tfind((void*)nameToFind,
            (void**)&prog_pts_tree,
            compareStrings)) {
    return 1;
  }
  else {
    return 0;
  }
}

// Print out all function declarations in Daikon .decls format
void printAllFunctionDecls(char faux_decls)
{
  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);

  while(!it->finished) {
    DaikonFunctionInfo* cur_entry = (DaikonFunctionInfo*)
         gengettable(DaikonFunctionInfoTable, gennext(it));

    if (!cur_entry)
         continue;

    // If kvasir_trace_prog_pts_filename is OFF, then ALWAYS
    // print out all program point .decls
    if (!kvasir_trace_prog_pts_filename ||
        // If kvasir_trace_prog_pts_filename is on (we are reading in
        // a ppt list file), then DO NOT OUTPUT .decls entries for
        // program points that we are not interested in tracing.  This
        // decreases the clutter of the .decls file and speeds up
        // processing time
        prog_pts_tree_entry_found(cur_entry)) {
      printOneFunctionDecl(cur_entry, 1, faux_decls);
      printOneFunctionDecl(cur_entry, 0, faux_decls);
    }
  }

  genfreeiterator(it);
}


// For C++ only: Print out an :::OBJECT program point.
// The object program point should consist of class_name:::OBJECT
// and all information from 'this'

// For C++ only: Print out a :::CLASS program point.
// The class program point should consist of class_name:::CLASS
// and all information about only STATIC variables belonging to this class

// DynComp: Right now, do NOT try to print out comparability
// information for OBJECT and CLASS program points.  We may support
// this in the future if necessary.
void printAllObjectAndClassDecls() {

  struct geniterator* it = gengetiterator(DaikonTypesTable);

  // Hashtable which contains the names of classes which have already printed
  // OBJECT and CLASS program points.  This is so that we can allow duplicate
  // entries in DaikonTypesTable but only print out ONE OBJECT/CLASS .decls program
  // point for each entry with a particular name
  // Key: Class name, Value: Doesn't matter - we only check if the table
  // "contains the entry"
  struct genhashtable* ClassNamesAlreadyPrinted =
    genallocatehashtable((unsigned int (*)(void *)) & hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  Bool hacked_dyncomp_switch = False;

  // HACK ALERT: We need to temporarily pretend that we are not using
  // kvasir_with_dyncomp in order to print out the OBJECT and CLASS
  // program points normally.  We need to set this back at the end of
  // the function:
  if (kvasir_with_dyncomp) {
    kvasir_with_dyncomp = False;
    hacked_dyncomp_switch = True;
  }

  while(!it->finished) {
    DaikonType* cur_type = (DaikonType*)
         gengettable(DaikonTypesTable, gennext(it));

    if (!cur_type)
         continue;

    // Only print out .decls for :::OBJECT and :::CLASS program points
    // if num_member_funcs > 0 - otherwise we have no member functions
    // so these program points will never be reached :)
    // Also, only print them out if their name is NOT contained in
    // ClassNamesAlreadyPrinted - otherwise there is a duplicate so don't
    // print it out!
    if ((cur_type->num_member_funcs > 0) &&
        (cur_type->collectionName) && // Do NOT try to print out unnamed anonymous classes
                                      // because we will have a naming ambiguity
        !gencontains(ClassNamesAlreadyPrinted, cur_type->collectionName)) {
         // Make up a fake DaikonFunctionInfo entry and populate the parentClass field
         DaikonFunctionInfo fakeFuncInfo;

         // Make up a fake DaikonVariable named 'this' and set its type to cur_type
         DaikonVariable fakeThisVar;

         memset(&fakeFuncInfo, 0, sizeof(fakeFuncInfo));
         fakeFuncInfo.parentClass = cur_type;

         memset(&fakeThisVar, 0, sizeof(fakeThisVar));
         fakeThisVar.name = "this";
         fakeThisVar.varType = cur_type;
         fakeThisVar.repPtrLevels = 1;
         fakeThisVar.declaredPtrLevels = 1;
         // Remember the .disambig for "this" so that it prints
         // out as ONE element and not an array
         fakeThisVar.disambig = 'P';

         fputs("DECLARE\n", decls_fp);
         fputs(cur_type->collectionName, decls_fp);
         fputs(":::OBJECT\n", decls_fp);

         stringStackPush(fullNameStack, &fullNameStackSize, "this");

         visitVariable(&fakeThisVar,
                       0,
                       0,
                       FUNCTION_ENTER_FORMAL_PARAM,
                       DECLS_FILE,
                       0,
                       0,
                       0,
                       0);

         stringStackPop(fullNameStack, &fullNameStackSize);


         fputs("\n", decls_fp);

         fputs("DECLARE\n", decls_fp);
         fputs(cur_type->collectionName, decls_fp);
         fputs(":::CLASS\n", decls_fp);

         printVariablesInVarList(&fakeFuncInfo, 1, // set 'isEnter' to 1 here (arbitrary choice)
                                 GLOBAL_VAR,
                                 0,
                                 DECLS_FILE,
                                 0,
                                 0,
                                 1,
                                 0);

         fputs("\n", decls_fp);

         genputtable(ClassNamesAlreadyPrinted, cur_type->collectionName, 0);
    }
  }

  genfreeiterator(it);
  genfreehashtable(ClassNamesAlreadyPrinted);

  // HACK ALERT! Remember to restore original state
  if (hacked_dyncomp_switch) {
    kvasir_with_dyncomp = True;
  }
}




// Print all variables contained in varListPtr
void printVariablesInVarList(DaikonFunctionInfo* funcPtr, // 0 for unspecified function,
                             char isEnter,
			     // which means --limit-static-vars has no effect
			     // and varOrigin must = GLOBAL_VAR
			     VariableOrigin varOrigin,
			     char* stackBaseAddr,
			     OutputFileType outputType,
			     char allowVarDumpToFile,
			     char* trace_vars_tree,

                             // 1 if we want to print out all static variables
                             // (in globalVars) corresponding to the class which
                             // funcPtr belongs to (This is for the C++ :::CLASS invariants)
                             // Must be called with varOrigin == GLOBAL_VAR and
                             // funcPtr->parentClass non-null
                             char printClassProgramPoint,
                             // 1 if we want to stop printing after the first
                             // variable in the list - MUST BE USED WITH
                             // varOrigin == {FUNCTION_ (ENTER or EXIT)_FORMAL_PARAM
                             // to print out ONLY the contents of the first
                             // param "this"
                             char stopAfterFirstVar)
{
  VarNode* i = 0;

  VarList* varListPtr = 0;
  int numIters = 0;

  if (!funcPtr && (varOrigin != GLOBAL_VAR)) {
    VG_(printf)( "Error with null funcPtr and (varOrigin != GLOBAL_VAR in printVariablesInVarList()\n");
    abort();
  }

  switch (varOrigin) {
  case GLOBAL_VAR:
    varListPtr = &globalVars;
    break;
  case FUNCTION_ENTER_FORMAL_PARAM:
  case FUNCTION_EXIT_FORMAL_PARAM:
    varListPtr = &(funcPtr->formalParameters);
    break;
  case FUNCTION_RETURN_VAR:
    varListPtr = &(funcPtr->returnValue);
    break;
  default:
    // Let varListPtr remain at 0
    break;
  }

  stringStackClear(&fullNameStackSize);

  if(!varListPtr)
    {
      VG_(printf)( "Error with varListPtr in printVariablesInVarList()\n");
      abort();
    }

  for (i = varListPtr->first; i != 0; i = i->next)
    {
      DaikonVariable* var;
      void* basePtrValue = 0;

      var = &(i->var);

      numIters++;

      if (stopAfterFirstVar && (numIters > 1)) {
           break;
      }

      if (!var->name) {
	VG_(printf)( "Weird null variable name!\n");
	continue;
      }

      if ((varOrigin == FUNCTION_ENTER_FORMAL_PARAM) ||
	  (varOrigin == FUNCTION_EXIT_FORMAL_PARAM))
	{
	  basePtrValue = (void*)((int)stackBaseAddr + var->byteOffset);
	}
      else if (varOrigin == GLOBAL_VAR)
	{
	  basePtrValue = (void*)(var->globalLocation);

          // If "--limit-static-vars" option was selected, then:
          // * Only print file-static variables at program points
          //   in the file in which the variables were declared
          // * Only print static variables declared within functions
          //   at program points of that particular function
	  if (!var->isExternal && kvasir_limit_static_vars && funcPtr) {
            // Declared within a function
            if (var->functionStartPC) {
              if (funcPtr->startPC != var->functionStartPC) {
                continue;
              }
            }
            // Declared globally
            else if (!VG_STREQ(funcPtr->filename, var->fileName)) {
              continue;
            }
          }

          if (printClassProgramPoint) {
               // With printClassProgramPoint on, THE ONLY VARIABLES YOU SHOULD PRINT
               // OUT ARE C++ static member variables
               // with the same class as the function we are printing
               if (funcPtr &&
                   (var->structParentType != funcPtr->parentClass)) {
                    continue;
               }
          }
          else {
               // Under normal circumstances, DON'T PRINT OUT C++ static member variables
               // UNLESS it belongs to the SAME CLASS as the function we are printing
               // Print out all regular globals normally (hence the check for
               // var->structParentType)
               if (var->structParentType && funcPtr &&
                   (var->structParentType != funcPtr->parentClass)){
                    continue;
               }
          }
	}

      // For .disambig, we only want to output selected
      // types of variables.  If the variable does not
      // meet the requirements, we will skip it
      if ((DISAMBIG_FILE == outputType) &&
	  !shouldOutputVarToDisambig(var)) {
	continue;
      }

      stringStackPush(fullNameStack, &fullNameStackSize, var->name);

      visitVariable(var,
                    basePtrValue,
                    0,
                    varOrigin,
                    outputType,
                    allowVarDumpToFile,
                    trace_vars_tree,
                    funcPtr,
                    isEnter);

      stringStackPop(fullNameStack, &fullNameStackSize);
    }
}


// Checks whether we are interested in tracing this variable, and if
// so, prints out the variable name to out_file, and if requested,
// also prints the variable name to the var-list-file specified by
// var_fump_fp.
// Pre: varName is allocated and freed by the caller
static void printVariableName(char* varName,
                              char allowVarDumpToFile,
                              FILE* out_file) {
  if (out_file) {
    fputs(varName, out_file);
    fputs("\n", out_file);
  }

  if (var_dump_fp && allowVarDumpToFile) {
    fputs(varName, var_dump_fp);
    fputs("\n", var_dump_fp);
  }
}


// Print a .decls entry for a particular variable
// Pre: varName is allocated and freed by caller
// This consists of 4 lines:
// var. name, declared type, rep. type, comparability number
// e.g.,
// /foo                 <-- variable name
// char*                <-- declared type
// java.lang.String     <-- rep. type
// 22                   <-- comparability number
static void printDeclsEntry(DaikonVariable* var,
                            char* varName,
                            VariableOrigin varOrigin,
                            char allowVarDumpToFile,
                            int layersBeforeBase,
                            char printAsSequence,
                            DisambigOverride disambigOverride,
                            DaikonFunctionInfo* varFuncInfo,
                            char isEnter) {
  DaikonDeclaredType dType = var->varType->declaredType;
  DaikonDeclaredType rType = var->varType->repType;
  int layers;
  char printingFirstAnnotation = 1;
  char alreadyPutDerefOnLine3;

  // Line 1: Variable name
  printVariableName(varName, allowVarDumpToFile, decls_fp);

  // Line 2: Declared type

  if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
    fputs(DaikonRepTypeString[R_INT], decls_fp);
    fputs(dereference, decls_fp);
  }
  else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
    fputs(DaikonRepTypeString[R_INT], decls_fp);
  }
  // named struct/union or enumeration
  else if (((dType == D_ENUMERATION) || (dType == D_STRUCT) || (dType == D_UNION)) &&
           var->varType->collectionName) {
    fputs(var->varType->collectionName, decls_fp);

    // For the repair tool, concatenate all of the field names
    // after the 'unnamed' struct name (after an underscore)
    if (kvasir_repair_format &&
        VG_STREQ(var->varType->collectionName, "unnamed")) {
      VarList* memberVars = var->varType->memberListPtr;
      VarNode* i = 0;
      DaikonVariable* curVar = 0;

      fputs("_", decls_fp);

      for (i = memberVars->first; i != 0; i = i->next) {
        curVar = &(i->var);
        if (curVar->name) {
          fputs(curVar->name, decls_fp);
        }
      }
    }
  }
  else {
    // Normal type (or unnamed struct/union)
    fputs(DaikonDeclaredTypeString[dType], decls_fp);
    // If we have a string, print it as char*
    // because the dType of string is "char"
    // so we need to append a "*" to it
    if (var->isString) {
      fputs(star, decls_fp);
    }
  }

  // For the declared type, print out one level of '*' for every
  // layer above base to denote pointer types
  for (layers = 0; layers < layersBeforeBase; layers++) {
    fputs(star, decls_fp);
    // TODO: Determine later whether this special case is worth it:
    // Special case for static array types: use a '[]' to
    // replace the LAST '*'
    //        if ((var->isStaticArray) &&
    //            (layers == (layersBeforeBase - 1))) {
    //          fputs(dereference, decls_fp);
    //        }
    //        else {
    //          fputs(star, decls_fp);
    //        }
  }

  // If we print this as a sequence, then we must append '[]'
  if (printAsSequence) {
    fputs(dereference, decls_fp);
  }

  // Add annotations as comments in .decls file
  // (The first one is preceded by ' # ' and all subsequent ones are
  // preceded by ',')

  // Original vars in function parameter lists have "isParam=true"

  if ((varOrigin == FUNCTION_ENTER_FORMAL_PARAM) ||
      (varOrigin == FUNCTION_EXIT_FORMAL_PARAM)) {
    if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
    else {fputs(",", decls_fp);}

    fputs("isParam=true", decls_fp);
  }

  // Struct variables are annotated with "isStruct=true"
  // in order to notify Daikon that the hashcode values printed
  // out for that variable have no semantic meaning
  if (kvasir_output_struct_vars &&
      (layersBeforeBase == 0) &&
      (var->varType->isStructUnionType)) {
    if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
    else {fputs(",", decls_fp);}

    fputs("isStruct=true", decls_fp);
  }

  // Hashcode variables that can never be null has "hasNull=false".
  // (e.g., statically-allocated arrays)
  if (var->isStaticArray && (layersBeforeBase == 1)) {
    if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
    else {fputs(",", decls_fp);}

    fputs("hasNull=false", decls_fp);
  }

  fputs("\n", decls_fp);


  // Line 3: Rep. type
  alreadyPutDerefOnLine3 = 0;

  // Print out rep. type as hashcode when you are not done dereferencing
  // pointer layers:
  if (layersBeforeBase > 0) {
    fputs(DaikonRepTypeString[R_HASHCODE], decls_fp);
  }
  else {
    // Special handling for strings and 'C' chars in .disambig
    if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
      fputs(DaikonRepTypeString[R_INT], decls_fp);
      fputs(dereference, decls_fp);
      alreadyPutDerefOnLine3 = 1;
    }
    else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
      fputs(DaikonRepTypeString[R_INT], decls_fp);
    }
    else if ((var->isString) ||
             (OVERRIDE_CHAR_AS_STRING == disambigOverride)) {
      fputs(DaikonRepTypeString[R_STRING], decls_fp);
    }
    else {
      tl_assert(rType != 0);
      fputs(DaikonRepTypeString[rType], decls_fp);
    }
  }

  // Append "[]" onto the end of the rep. type if necessary
  if (!alreadyPutDerefOnLine3 &&
      printAsSequence) {
    fputs(dereference, decls_fp);
  }

  fputs("\n", decls_fp);


  // Line 4: Comparability number

  // If we are outputting a REAL .decls with DynComp, that means
  // that the program has already finished execution so that all
  // of the comparability information would be already updated:
  if (kvasir_with_dyncomp) {
    // Remember that comp_number is a SIGNED INTEGER but the
    // tags are UNSIGNED INTEGERS so be careful of overflows
    // which result in negative numbers, which are useless
    // since Daikon ignores them.
    int comp_number = DC_get_comp_number_for_var(varFuncInfo,
                                                 isEnter,
                                                 g_daikonVarIndex);
    fprintf(decls_fp, "%d", comp_number);
    fputs("\n", decls_fp);
  }
  else {
    // Otherwise, print out unknown comparability type "22"
    fputs("22", decls_fp);
    fputs("\n", decls_fp);
  }
}


static void printDtraceEntry(DaikonVariable* var,
                             UInt numDereferences,
                             char* varName,
                             void* pValue,
                             VariableOrigin varOrigin,
                             char isHashcode,
                             char overrideIsInit,
                             DisambigOverride disambigOverride,
                             char isSequence,
                             // pValueArray and numElts only valid if
                             // isSequence non-null
                             void** pValueArray,
                             UInt numElts,
                             DaikonFunctionInfo* varFuncInfo,
                             char isEnter) {
  char variableHasBeenObserved = 0;
  int layersBeforeBase = var->repPtrLevels - numDereferences;
  void* firstInitElt = 0;

  tl_assert(layersBeforeBase >= 0);

  // Line 1: Variable name
  printVariableName(varName, 0, dtrace_fp);

/*   VG_(printf)("%s - isSequence: %u (overrideInit: %u)\n", varName, isSequence, overrideIsInit); */
/*   if (pValueArray) { */
/*     UInt i; */
/*     VG_(printf)("[ "); */
/*     for (i = 0; i < numElts; i++) { */
/*       VG_(printf)("%u ", pValueArray[i]); */
/*     } */
/*     VG_(printf)("]\n"); */
/*   } */

  // Lines 2 & 3: Value and modbit
  if (isSequence) {
    variableHasBeenObserved =
      printDtraceSequence(var,
                          pValueArray,
                          numElts,
                          varOrigin,
                          isHashcode,
                          disambigOverride,
                          &firstInitElt);
  }
  else {
    variableHasBeenObserved =
      printDtraceSingleVar(var,
                           pValue,
                           varOrigin,
                           isHashcode,
                           overrideIsInit,
                           disambigOverride);
  }

  // DynComp post-processing after observing a variable:
  if (kvasir_with_dyncomp && variableHasBeenObserved) {
    Addr a = 0;
    void* ptrInQuestion = 0;
    char ptrAllocAndInit = 0;

    // Pick the first initialized element from the sequence
    if (isSequence) {
      ptrInQuestion = firstInitElt;
    }
    else {
      ptrInQuestion = pValue;
    }

    // Special handling for static arrays: Currently, in the
    // .dtrace, for a static arrays 'int foo[]', we print out
    // 'foo' as the address of foo and 'foo[]' as the contents of
    // 'foo'.  However, for comparability, there is no place in
    // memory where the address of 'foo' is maintained; thus,
    // there is no tag for it anywhere, so we must not
    // post-process it and simply allow it to keep a tag of 0.
    // This implies that all static array hashcode values are
    // unique and not comparable to one another, which is the
    // intended behavior.  (Notice that if one wants to assign a
    // pointer to 'foo', then the address of 'foo' resides
    // somewhere in memory - where that pointer is located - and
    // thus gets a fresh tag.  One can then have that pointer
    // interact with other pointers and have THEM be comparable,
    // but 'foo' itself still has no tag and is not comparable to
    // anything else.)

    // Don't do anything if it's a base static array variable
    // (layersBeforeBase > 0) is okay since var->isStaticArray implies
    // that there is only one level of pointer indirection, and for a
    // static string (static array of 'char'), layersBeforeBase == 0
    // right away so we still process it
    if (!(var->isStaticArray &&
          (layersBeforeBase > 0))) {

      // Special handling for strings.  We are not interested in the
      // comparability of the 'char*' pointer variable, but rather
      // we are interested in the comparability of the CONTENTS of
      // the string.  (Be careful about statically-declared strings,
      // in which case the address of the first element is the address
      // of the pointer variable)
      if (var->isString &&
          (0 == layersBeforeBase)) {
        if (ptrInQuestion) {
          ptrAllocAndInit =
            (addressIsAllocated((Addr)ptrInQuestion, sizeof(void*)) &&
             addressIsInitialized((Addr)ptrInQuestion, sizeof(void*)));
        }

        if (ptrAllocAndInit) {
          // Depends on whether the variable is a static array or not:
          a = var->isStaticArray ?
            (Addr)ptrInQuestion :
            *((Addr*)(ptrInQuestion));
        }
      }
      else {
        a = (Addr)ptrInQuestion;
      }

      if (a) {
        DC_post_process_for_variable(varFuncInfo,
                                     isEnter,
                                     g_daikonVarIndex,
                                     a);
      }
    }
  }


  // While observing the runtime values,
  // set var->disambigMultipleElts and
  // var->pointerHasEverBeenObserved depending on whether
  // upperBound == 0 (1 element) or not and whether
  // variableHasBeenObserved:
  // We do this only when numDereferences == 1 because
  // we want to see if the target of a particular pointer
  // has been observed and whether it refers to 1 or multiple elements
  if ((1 == numDereferences) && variableHasBeenObserved) {
    if (isSequence && (numElts > 1)) {
      var->disambigMultipleElts = 1;
    }

    // If pointerHasEverBeenObserved is not set, then set it
    if (!var->pointerHasEverBeenObserved) {
      var->pointerHasEverBeenObserved = 1;
    }
  }
}


// Prints a .disambig file entry for a Daikon variable
// This consists of 2 lines:
//   variable name, disambig type
// e.g.,
// /foo       <-- variable name
// S          <-- disambig type
static void printDisambigEntry(DaikonVariable* var, char* varName) {

  // Line 1: Variable name
  printVariableName(varName, 0, disambig_fp);

  // Line 2: Disambig type
  // (specified in the "Daikon User Manual" and also due to decisions
  // made by the Kvasir developers)

  /* Default values:
     Base type "char" and "unsigned char": 'I' for integer
     Pointer to "char": 'S' for string
     Pointer to all other types:
       - 'A' for array if var->disambigMultipleElts,
             which means that we've observed array
             behavior during program's execution
         or if !var->pointerHasEverBeenObserved,
            which means that the pointer has never
            been observed so a conservative guess
            of 'A' should be the default
         or if var->isStructUnionMember - don't try
            to be smart about member variables
            within structs/unions - just default to "A"
       - 'P' for pointer if (var->pointerHasEverBeenObserved &&
             !var->disambigMultipleElts)
  */

  if (0 == var->declaredPtrLevels) {
    if ((D_CHAR == var->varType->declaredType) ||
        (D_UNSIGNED_CHAR == var->varType->declaredType)) {
      fputs("I", disambig_fp);
    }
  }

  // Normal string, not pointer to string
  else if (var->isString && (0 == var->repPtrLevels)) {
    fputs("S", disambig_fp);
  }
  else if (var->repPtrLevels > 0) {
    if (var->isStructUnionMember) {
      fputs("A", disambig_fp);
    }
    else {
      if (var->pointerHasEverBeenObserved) {
        if (var->disambigMultipleElts) {
          fputs("A", disambig_fp);
        }
        else {
          fputs("P", disambig_fp);
        }
      }
      // default behavior for variable that was
      // never observed during the execution
      else {
        fputs("A", disambig_fp);
      }
    }
  }

  fputs("\n", disambig_fp);
}

static void handleDynCompExtraProp(DaikonVariable* var,
                                   int layersBeforeBase,
                                   DaikonFunctionInfo* varFuncInfo,
                                   char isEnter) {
  // Special handling for static arrays: Currently, in the
  // .dtrace, for a static arrays 'int foo[]', we print out
  // 'foo' as the address of foo and 'foo[]' as the contents of
  // 'foo'.  However, for comparability, there is no place in
  // memory where the address of 'foo' is maintained; thus,
  // there is no tag for it anywhere, so we must not
  // post-process it and simply allow it to keep a tag of 0.
  // This implies that all static array hashcode values are
  // unique and not comparable to one another, which is the
  // intended behavior.  (Notice that if one wants to assign a
  // pointer to 'foo', then the address of 'foo' resides
  // somewhere in memory - where that pointer is located - and
  // thus gets a fresh tag.  One can then have that pointer
  // interact with other pointers and have THEM be comparable,
  // but 'foo' itself still has no tag and is not comparable to
  // anything else.)

  // Don't do anything if this condition holds:
  // (layersBeforeBase > 0) is okay since var->isStaticArray implies
  // that there is only one level of pointer indirection, and for a
  // static string (static array of 'char'), layersBeforeBase == 0
  // right away so we still process it
  if (!(var->isStaticArray &&
        (layersBeforeBase > 0))) {
    DC_extra_propagation_post_process(varFuncInfo,
                                      isEnter,
                                      g_daikonVarIndex);
  }
}


/* Functions for visiting variables at every program point */

// Returns 1 if we are interested in visiting this variable and its
// children, 0 otherwise.  No children of this variable will get
// visited if this variable is not visited.  For example, if 'foo' is
// an array, then if the hashcode value of 'foo' is not visited, then
// the actual array value of 'foo[]' won't be visited either.
// This performs string matching in trace_vars_tree based on fullDaikonName
static char interestedInVar(char* fullDaikonName, char* trace_vars_tree) {
  if (kvasir_trace_vars_filename) {
    if (trace_vars_tree) {
      if (!tfind((void*)fullDaikonName, (void**)&trace_vars_tree, compareStrings)) {
        return 0;
      }
    }
    // If trace_vars_tree is kept at 0 on purpose but
    // kvasir_trace_vars_filename is valid, then still punt because we
    // are only supposed to print out variables listed in
    // kvasir_trace_vars_filename and obviously there aren't any
    // relevant variables to print
    else {
      return 0;
    }
  }

  return 1;
}

static void visitSingleVar(DaikonVariable* var,
                           UInt numDereferences,
                           void* pValue,
                           char overrideIsInit,
                           VariableOrigin varOrigin,
                           OutputFileType outputType,
                           char allowVarDumpToFile,
                           char* trace_vars_tree,
                           DisambigOverride disambigOverride,
                           UInt numStructsDereferenced,
                           DaikonFunctionInfo* varFuncInfo,
                           char isEnter);

static void visitSequence(DaikonVariable* var,
                          UInt numDereferences,
                          void** pValueArray,
                          UInt numElts,
                          VariableOrigin varOrigin,
                          OutputFileType outputType,
                          char allowVarDumpToFile,
                          char* trace_vars_tree,
                          DisambigOverride disambigOverride,
                          UInt numStructsDereferenced,
                          DaikonFunctionInfo* varFuncInfo,
                          char isEnter);


// This is the only function that should be called from the outside.
// It visits a variable by delegating to visitSingleVar()
// Pre: varOrigin != DERIVED_VAR, varOrigin != DERIVED_FLATTENED_ARRAY_VAR
// Pre: The name of the variable is initialized in fullNameStack
void visitVariable(DaikonVariable* var,
                   void* pValue,
                   // We only use overrideIsInit when we pass in
                   // things (e.g. return values) that cannot be
                   // checked by the Memcheck A and V bits. Never have
                   // overrideIsInit when you derive variables (make
                   // recursive calls) because their addresses are
                   // different from the original's
                   char overrideIsInit,
                   VariableOrigin varOrigin,
                   OutputFileType outputType,
                   char allowVarDumpToFile,
                   char* trace_vars_tree, // Binary tree within FunctionTree struct
                   // These uniquely identify which program point we
                   // are at (only relevant for DynComp)
                   DaikonFunctionInfo* varFuncInfo,
                   char isEnter) {
  tl_assert(varOrigin != DERIVED_VAR);
  tl_assert(varOrigin != DERIVED_FLATTENED_ARRAY_VAR);

  // In preparation for a new round of variable visits, initialize a
  // new VisitedStructsTable, freeing an old one if necessary
  if (VisitedStructsTable) {
    genfreehashtable(VisitedStructsTable);
    VisitedStructsTable = 0;
  }
  VisitedStructsTable = genallocatehashtable((unsigned int (*)(void *)) & hashID,
                                             (int (*)(void *,void *)) &equivalentIDs);

  // Delegate:
  visitSingleVar(var,
                 0,
                 pValue,
                 overrideIsInit,
                 varOrigin,
                 outputType,
                 allowVarDumpToFile,
                 trace_vars_tree,
                 OVERRIDE_NONE,
                 0,
                 varFuncInfo,
                 isEnter);
}


// Visit a single variable uniquely identified by var and
// numDereferences and then derive additional variables either by
// dereferencing pointers or by visiting struct members
// This function calls visitSingleVar() or visitSequence()
static
void visitSingleVar(DaikonVariable* var,
                    UInt numDereferences,
                    // Pointer to the variable's current value
                    void* pValue,
                    // We only use overrideIsInit when we pass in
                    // things (e.g. return values) that cannot be
                    // checked by the Memcheck A and V bits. Never have
                    // overrideIsInit when you derive variables (make
                    // recursive calls) because their addresses are
                    // different from the original's
                    char overrideIsInit,
                    VariableOrigin varOrigin,
                    OutputFileType outputType,
                    char allowVarDumpToFile,
                    char* trace_vars_tree, // Binary tree within FunctionTree struct
                    DisambigOverride disambigOverride,
                    // The number of structs we have dereferenced for
                    // a particular call of visitVariable(); Starts at
                    // 0 and increments every time we hit a variable
                    // which is a base struct type
                    // Range: [0, MAX_VISIT_NESTING_DEPTH]
                    UInt numStructsDereferenced,
                    // These uniquely identify which program point we
                    // are at (only relevant for DynComp)
                    DaikonFunctionInfo* varFuncInfo,
                    char isEnter) {
  char* fullDaikonName = 0;
  int layersBeforeBase;

  // Initialize these in a group later
  char disambigOverrideArrayAsPointer = 0;
  char derefSingleElement = 0;

  tl_assert(var);
  layersBeforeBase = var->repPtrLevels - numDereferences;
  tl_assert(layersBeforeBase >= 0);

  // Special handling for overriding in the presence of .disambig:
  // Only check this for original (numDereferences == 0) variables
  // to ensure that it's only checked once per variable
  if (0 == numDereferences) {
    disambigOverride = returnDisambigOverride(var);
  }

  if (kvasir_disambig_ptrs) {
    disambigOverride = OVERRIDE_ARRAY_AS_POINTER;
  }

  disambigOverrideArrayAsPointer =
    (OVERRIDE_ARRAY_AS_POINTER == disambigOverride);

  derefSingleElement = disambigOverrideArrayAsPointer;


  // Unless kvasir_output_struct_vars is on,
  // don't print out an entry for base (non-pointer) struct/union
  // variables since they have no substantive meaning for C programs.
  // They are merely represented as hashcode values, and that's kind
  // of deceiving because they aren't really pointer variables either.

  // This means that anywhere inside of this 'if' statement, we should
  // be very careful about mutating state because different state may
  // be mutated based on whether kvasir_output_struct_vars is on,
  // which may lead to different-looking results.
  if (kvasir_output_struct_vars ||
      (!((layersBeforeBase == 0) &&
         (var->varType->isStructUnionType)))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStackSize > 0);
    fullDaikonName = stringStackStrdup(fullNameStack, fullNameStackSize);
    // If we are not interested in visiting this variable or its
    // children, then PUNT:
    if (!interestedInVar(fullDaikonName, trace_vars_tree)) {
      VG_(free)(fullDaikonName);
      return;
    }

    // Perform the actual output depending on outputType:
    switch (outputType) {
    case DECLS_FILE:
      printDeclsEntry(var, fullDaikonName, varOrigin, allowVarDumpToFile,
                      layersBeforeBase, 0, disambigOverride,
                      varFuncInfo, isEnter);
      break;
    case DTRACE_FILE:
      printDtraceEntry(var,
                       numDereferences,
                       fullDaikonName,
                       pValue,
                       varOrigin,
                       (layersBeforeBase > 0),
                       overrideIsInit,
                       disambigOverride,
                       0, // NOT isSequence
                       0,
                       0,
                       varFuncInfo,
                       isEnter);
      break;
    case DISAMBIG_FILE:
      printDisambigEntry(var, fullDaikonName);
      // DO NOT DERIVE VARIABLES for .disambig.  We are only interested
      // in printing out the variables which are immediately visible
      // to the user.  Thus, we should RETURN out of the function
      // altogether instead of simply breaking out of the switch
      return;
    case DYNCOMP_EXTRA_PROP:
      handleDynCompExtraProp(var, layersBeforeBase, varFuncInfo, isEnter);
      break;
    case FAUX_DECLS_FILE:
      // Chill and do nothing here because we're making a dry run :)
      break;
    default:
      VG_(printf)( "Error! Invalid outputType in visitSingleVar()\n");
      abort();
      break;
    }
  }

  // We don't need the name anymore since we're done printing
  // everything about this variable by now
  VG_(free)(fullDaikonName);

  // Be very careful about where you increment this!  We want to
  // increment this once per call of either visitSingleVar() or
  // visitSequence():
  g_daikonVarIndex++;


  // Now comes the fun part of deriving variables!

  // Dereference and keep on printing out derived variables until we
  // hit the base type:
  if (layersBeforeBase > 0) {

    // 1.) Initialize pValue properly and call visitSingleVar() again
    // because we are dereferencing a single element:
    if (derefSingleElement) {
      char derivedIsAllocated = 0;
      char derivedIsInitialized = 0;

      void* pNewValue = 0;

      // Initialize pNewValue if possible, otherwise leave at 0:
      if ((DTRACE_FILE == outputType) && pValue) {
        derivedIsAllocated = (overrideIsInit ? 1 :
                              addressIsAllocated((Addr)pValue, sizeof(void*)));
        if (derivedIsAllocated) {
          derivedIsInitialized = (overrideIsInit ? 1 :
                                  addressIsInitialized((Addr)pValue, sizeof(void*)));
          // Make a single dereference unless the variable is a static
          // array, in which case we shouldn't make a dereference at
          // all:
          pNewValue = var->isStaticArray ? pValue : *((void **)pValue);
        }
      }

      // Push 1 symbol on stack to represent single elt. dereference:
      if (kvasir_repair_format) {
        stringStackPush(fullNameStack, &fullNameStackSize, star);
      }
      else {
        stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt);
      }

      visitSingleVar(var,
                     numDereferences + 1,
                     pNewValue,
                     overrideIsInit,
                     (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                     outputType,
                     allowVarDumpToFile,
                     trace_vars_tree,
                     disambigOverride,
                     numStructsDereferenced,
                     varFuncInfo,
                     isEnter);

      // Pop 1 symbol off
      stringStackPop(fullNameStack, &fullNameStackSize);
    }
    // 2.) Sequence dereference (can either be static or dynamic
    // array).  We need to initialize pValueArray and numElts
    // appropriately and call visitSequence()
    else {
      void** pValueArray = 0;
      UInt numElts = 0;
      UInt bytesBetweenElts = getBytesBetweenElts(var);
      UInt i;

      // We only need to set pValueArray and numElts for .dtrace output:
      if ((DTRACE_FILE == outputType) && pValue) {
        // Static array:
        if (VAR_IS_STATIC_ARRAY(var)) {
          // Flatten multi-dimensional arrays by treating them as one
          // giant single-dimensional array.  Take the products of the
          // sizes of all dimensions (remember to add 1 to each to get
          // from upper bound to size):
          UInt dim;

          // Notice the +1 to convert from upper bound to numElts
          numElts = 1 + var->upperBounds[0];

          // Additional dimensions:
          for (dim = 1; dim < var->numDimensions; dim++) {
            numElts *= (1 + var->upperBounds[dim]);
          }

          pValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

          //          VG_(printf)("Static array - dims: %u, numElts: %u\n",
          //                      var->numDimensions, numElts);

          // Build up pValueArray with pointers to the elements of the
          // static array starting at pValue
          for (i = 0; i < numElts; i++) {
            pValueArray[i] = pValue + (i * bytesBetweenElts);
          }
        }
        // Dynamic array:
        else {
          char derivedIsAllocated = 0;
          char derivedIsInitialized = 0;
          void* pNewStartValue = 0;

          derivedIsAllocated = (overrideIsInit ? 1 :
                                addressIsAllocated((Addr)pValue, sizeof(void*)));
          if (derivedIsAllocated) {
            derivedIsInitialized = (overrideIsInit ? 1 :
                                    addressIsInitialized((Addr)pValue, sizeof(void*)));
            // Make a single dereference to get to the start of the array
            pNewStartValue = *((void **)pValue);
          }

          // We should only initialize pValueArray and numElts if the
          // pointer to the start of the array is valid:
          if (pNewStartValue) {
            // Notice the +1 to convert from upper bound to numElts
            numElts = 1 + returnArrayUpperBoundFromPtr(var, (Addr)pNewStartValue);
            pValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

            // Build up pValueArray with pointers starting at pNewStartValue
            for (i = 0; i < numElts; i++) {
              pValueArray[i] = pNewStartValue + (i * bytesBetweenElts);
            }
          }
        }
      }

      // Push 1 symbol on stack to represent sequence dereference:
      stringStackPush(fullNameStack, &fullNameStackSize, dereference);

      visitSequence(var,
                    numDereferences + 1,
                    pValueArray,
                    numElts,
                    (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                    outputType,
                    allowVarDumpToFile,
                    trace_vars_tree,
                    disambigOverride,
                    numStructsDereferenced,
                    varFuncInfo,
                    isEnter);

      // Pop 1 symbol off
      stringStackPop(fullNameStack, &fullNameStackSize);

      // Only free if necessary
      if (pValueArray) {
        VG_(free)(pValueArray);
        pValueArray = 0;
      }
    }
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (var->varType->isStructUnionType) {
    tl_assert(0 == layersBeforeBase);

    VarList* memberVars;
    VarNode* i;
    DaikonVariable* curVar;

    // Check to see if the VisitedStructsTable contains more than
    // MAX_VISIT_STRUCT_DEPTH of the current struct type
    if (gencontains(VisitedStructsTable, (void*)(var->varType))) {
      UInt count = (UInt)(gengettable(VisitedStructsTable, (void*)(var->varType)));

      if (count <= MAX_VISIT_STRUCT_DEPTH) {
        count++;
        genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
      }
      // PUNT because this struct has appeared more than
      // MAX_VISIT_STRUCT_DEPTH times during one call to visitVariable()
      else {
        return;
      }
    }
    // If not found in the table, initialize this entry with 1
    else {
      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)1);
    }

    // If we have dereferenced more than
    // MAX_VISIT_NESTING_DEPTH structs, then simply PUNT and
    // stop deriving variables from it.
    if (numStructsDereferenced > MAX_VISIT_NESTING_DEPTH) {
      return;
    }


    // Walk down the member variables list and visit each one with the
    // current struct variable name as the prefix:
    memberVars = var->varType->memberListPtr;
    i = 0;
    curVar = 0;

    // No member variables
    if(!memberVars || !(memberVars->first))
      return;

    for (i = memberVars->first; i != 0; i = i->next) {
      char* top;
      char numEltsPushedOnStack = 0;
      // Pointer to the value of the current member variable
      void* pCurVarValue = 0;
      curVar = &(i->var);
      assert(curVar);

      // Only flatten static arrays when the --flatten-arrays option
      // is used.  Normally we do not have to flatten static arrays at
      // this point because we can simply visit them as an entire
      // sequence.
      if (VAR_IS_STATIC_ARRAY(curVar) &&
          kvasir_flatten_arrays &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(curVar->isString && (curVar->declaredPtrLevels == 1))) {
        // Only look at the first dimension:
        UInt arrayIndex;
        for (arrayIndex = 0; arrayIndex <= curVar->upperBounds[0]; arrayIndex++) {
          char indexStr[5];
          top = stringStackTop(fullNameStack, fullNameStackSize);

          sprintf(indexStr, "%d", arrayIndex);

          // TODO: Subtract and add is a HACK!  Subtract one from the
          // type of curVar just because we are looping through and
          // expanding the array
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count--;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          if (DTRACE_FILE == outputType) {
            // The starting address for the member variable is the
            // struct's starting address plus the location of the
            // variable within the struct
            pCurVarValue = pValue + curVar->data_member_location;

            // Very important! Add offset within the flattened array:
            pCurVarValue += (arrayIndex * getBytesBetweenElts(curVar));
          }

          // If the top element is '*', then instead of pushing a
          // '.' to make '*.', erase that element and instead push
          // '->'.  If last element is '->', then we're fine and
          // don't do anything else.  Otherwise, push a '.'
          if (top[0] == '*') {
            stringStackPop(fullNameStack, &fullNameStackSize);
            stringStackPush(fullNameStack, &fullNameStackSize, arrow);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, arrow)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(fullNameStack, &fullNameStackSize, dot);
            numEltsPushedOnStack = 1;
          }

          stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
          stringStackPush(fullNameStack, &fullNameStackSize, "[");
          stringStackPush(fullNameStack, &fullNameStackSize, indexStr);
          stringStackPush(fullNameStack, &fullNameStackSize, "]");

          numEltsPushedOnStack += 4;


          visitSingleVar(curVar,
                         0,
                         pCurVarValue,
                         0,
                         DERIVED_FLATTENED_ARRAY_VAR,
                         outputType,
                         allowVarDumpToFile,
                         trace_vars_tree,
                         OVERRIDE_NONE, // Start over again and read new .disambig entry
                         numStructsDereferenced + 1, // Notice the +1 here
                         varFuncInfo,
                         isEnter);

          // POP all the stuff we pushed on there before
          while ((numEltsPushedOnStack--) > 0) {
            stringStackPop(fullNameStack, &fullNameStackSize);
          }

          // HACK: Add the count back on at the end
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count++;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }
        }
      }
      // Regular member variable (without array flattening):
      else {
        if ((DTRACE_FILE == outputType) && pValue) {
          // The starting address for the member variable is the
          // struct's starting address plus the location of the variable
          // within the struct TODO: Are we sure that arithmetic on
          // void* basePtrValue adds by 1?  Otherwise, we'd have
          // mis-alignment issues.  (I tried it in gdb and it seems to
          // work, though.)
          pCurVarValue = pValue + curVar->data_member_location;

          // Override for D_DOUBLE types: For some reason, the DWARF2
          // info.  botches the locations of double variables within
          // structs, setting their data_member_location fields to give
          // them only 4 bytes of padding instead of 8 against the next
          // member variable.  If curVar is a double and there exists a
          // next member variable such that the difference in
          // data_member_location of this double and the next member
          // variable is exactly 4, then decrement the double's location
          // by 4 in order to give it a padding of 8:
          if ((D_DOUBLE == curVar->varType->declaredType) &&
              (i->next) &&
              ((i->next->var.data_member_location -
                curVar->data_member_location) == 4)) {
            pCurVarValue -= 4;
          }
        }

        top = stringStackTop(fullNameStack, fullNameStackSize);

        // If the top element is '*' or '[0]', then instead of pushing a
        // '.' to make '*.' or '[0].', erase that element and instead push
        // '->'.  If last element is '->', then we're fine and
        // don't do anything else.  Otherwise, push a '.'
        if ((top[0] == '*') || (VG_STREQ(top, zeroth_elt))) {
          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPush(fullNameStack, &fullNameStackSize, arrow);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, arrow)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, dot);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
        numEltsPushedOnStack++;

        visitSingleVar(curVar,
                       0,
                       pCurVarValue,
                       0,
                       (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                       outputType,
                       allowVarDumpToFile,
                       trace_vars_tree,
                       OVERRIDE_NONE, // Start over again and read new .disambig entry
                       numStructsDereferenced + 1, // Notice the +1 here
                       varFuncInfo,
                       isEnter);

        // POP everything we've just pushed on
        while ((numEltsPushedOnStack--) > 0) {
          stringStackPop(fullNameStack, &fullNameStackSize);
        }
      }
    }
  }
}


// Visit a variable sequence uniquely identified by var and
// numDereferences whose values are referred to by pointers within
// pValueArray (of size numElts), and then derive additional variables
// either by dereferencing pointers or by visiting struct members.
// This function only calls visitSequence() with the same value of
// numElts because Daikon only supports one level of sequences.
// Pre: varOrigin == {DERIVED_VAR, DERIVED_FLATTENED_ARRAY_VAR}
static
void visitSequence(DaikonVariable* var,
                   UInt numDereferences,
                   // Array of pointers to the current variable's values
                   void** pValueArray,
                   UInt numElts, // Size of pValueArray
                   VariableOrigin varOrigin,
                   OutputFileType outputType,
                   char allowVarDumpToFile,
                   char* trace_vars_tree, // Binary tree within FunctionTree struct
                   DisambigOverride disambigOverride,
                   // The number of structs we have dereferenced for
                   // a particular call of visitVariable(); Starts at
                   // 0 and increments every time we hit a variable
                   // which is a base struct type
                   // Range: [0, MAX_VISIT_NESTING_DEPTH]
                   UInt numStructsDereferenced,
                   // These uniquely identify which program point we
                   // are at (only relevant for DynComp)
                   DaikonFunctionInfo* varFuncInfo,
                   char isEnter) {

  char* fullDaikonName = 0;
  int layersBeforeBase;

  tl_assert(var);
  layersBeforeBase = var->repPtrLevels - numDereferences;
  tl_assert(layersBeforeBase >= 0);
  tl_assert((DERIVED_VAR == varOrigin) ||
            (DERIVED_FLATTENED_ARRAY_VAR == varOrigin));

  // Special handling for overriding in the presence of .disambig:
  // Only check this for original (numDereferences == 0) variables
  // to ensure that it's only checked once per variable
  if (0 == numDereferences) {
    disambigOverride = returnDisambigOverride(var);
  }

  // Unless kvasir_output_struct_vars is on,
  // don't print out an entry for base (non-pointer) struct/union
  // variables since they have no substantive meaning for C programs.
  // They are merely represented as hashcode values, and that's kind
  // of deceiving because they aren't really pointer variables either.

  // This means that anywhere inside of this 'if' statement, we should
  // be very careful about mutating state because different state may
  // be mutated based on whether kvasir_output_struct_vars is on,
  // which may lead to different-looking results.
  if (kvasir_output_struct_vars ||
      (!((layersBeforeBase == 0) &&
         (var->varType->isStructUnionType)))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStackSize > 0);
    fullDaikonName = stringStackStrdup(fullNameStack, fullNameStackSize);

    // If we are not interested in visiting this variable or its
    // children, then PUNT:
    if (!interestedInVar(fullDaikonName, trace_vars_tree)) {
      VG_(free)(fullDaikonName);
      return;
    }

    // Perform the actual output depending on outputType:
    switch (outputType) {
    case DECLS_FILE:
      printDeclsEntry(var, fullDaikonName, varOrigin, allowVarDumpToFile,
                      layersBeforeBase, 1, disambigOverride,
                      varFuncInfo, isEnter);
      break;
    case DTRACE_FILE:
      printDtraceEntry(var,
                       numDereferences,
                       fullDaikonName,
                       0,
                       varOrigin,
                       (layersBeforeBase > 0),
                       0,
                       disambigOverride,
                       1, // YES isSequence
                       pValueArray,
                       numElts,
                       varFuncInfo,
                       isEnter);
      break;
    case DISAMBIG_FILE:
      printDisambigEntry(var, fullDaikonName);
      // DO NOT DERIVE VARIABLES for .disambig.  We are only interested
      // in printing out the variables which are immediately visible
      // to the user.  Thus, we should RETURN out of the function
      // altogether instead of simply breaking out of the switch
      return;
    case DYNCOMP_EXTRA_PROP:
      handleDynCompExtraProp(var, layersBeforeBase, varFuncInfo, isEnter);
      break;
    case FAUX_DECLS_FILE:
      // Chill and do nothing here because we're making a dry run :)
      break;
    default:
      VG_(printf)( "Error! Invalid outputType in outputDaikonVar()\n");
      abort();
      break;
    }
  }

  // We don't need the name anymore since we're done printing
  // everything about this variable by now
  VG_(free)(fullDaikonName);

  // Be very careful about where you increment this!  We want to
  // increment this once per call of either visitSingleVar() or
  // visitSequence():
  g_daikonVarIndex++;


  // Now comes the fun part of deriving variables!

  // Dereference and keep on printing out derived variables until we
  // hit the base type.  We want to override the old pointer values
  // within pValueArray with new pointer values ascertained from
  // dereferencing each element of the array.  If a particular element
  // is un-allocated or un-initialized, then mark it with a 0.
  if (layersBeforeBase > 0) {
    // TODO: Implement static array flattening

    // We only need to set pValueArray and numElts for .dtrace output:
    // (If this variable is a static array, then there is no need to
    //  dereference pointers - very important but subtle point!)
    if ((DTRACE_FILE == outputType) &&
        !VAR_IS_STATIC_ARRAY(var)) {
      // Iterate through pValueArray and dereference each pointer
      // value if possible, then override the entries in pValueArray
      // with the dereferenced pointers (use a value of 0 for
      // unallocated or uninit)
      UInt i;
      for (i = 0; i < numElts; i++) {
        char derivedIsAllocated = 0;
        char derivedIsInitialized = 0;
        void** pValueArrayEntry = &pValueArray[i];

        // If this entry is already 0, then skip it
        if (0 == *pValueArrayEntry) {
          continue;
        }

        derivedIsAllocated = addressIsAllocated((Addr)(*pValueArrayEntry), sizeof(void*));
        if (derivedIsAllocated) {
          derivedIsInitialized = addressIsInitialized((Addr)(*pValueArrayEntry), sizeof(void*));
          if (derivedIsInitialized) {
            // Make a single dereference and override pValueArray
            // entry with the dereferenced value:
            *pValueArrayEntry = *((void **)(*pValueArrayEntry));
          }
          else {
            // TODO: We need to somehow mark this entry as 'uninit'
            *pValueArrayEntry = 0;
          }
        }
        else {
          // TODO: We need to somehow mark this entry as 'unallocated'
          *pValueArrayEntry = 0;
        }
      }
    }

    // Push 1 symbol on stack to represent single elt. dereference:
    if (kvasir_repair_format) {
      stringStackPush(fullNameStack, &fullNameStackSize, star);
    }
    else {
      stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt);
    }

    visitSequence(var,
                  numDereferences + 1,
                  pValueArray,
                  numElts,
                  (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                  outputType,
                  allowVarDumpToFile,
                  trace_vars_tree,
                  disambigOverride,
                  numStructsDereferenced,
                  varFuncInfo,
                  isEnter);

    // Pop 1 symbol off
    stringStackPop(fullNameStack, &fullNameStackSize);
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (var->varType->isStructUnionType) {
    tl_assert(0 == layersBeforeBase);

    VarList* memberVars;
    VarNode* i;
    DaikonVariable* curVar;

    // Check to see if the VisitedStructsTable contains more than
    // MAX_VISIT_STRUCT_DEPTH of the current struct type
    if (gencontains(VisitedStructsTable, (void*)(var->varType))) {
      UInt count = (UInt)(gengettable(VisitedStructsTable, (void*)(var->varType)));

      if (count <= MAX_VISIT_STRUCT_DEPTH) {
        count++;
        genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
      }
      // PUNT because this struct has appeared more than
      // MAX_VISIT_STRUCT_DEPTH times during one call to visitVariable()
      else {
        return;
      }
    }
    // If not found in the table, initialize this entry with 1
    else {
      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)1);
    }

    // If we have dereferenced more than
    // MAX_VISIT_NESTING_DEPTH structs, then simply PUNT and
    // stop deriving variables from it.
    if (numStructsDereferenced > MAX_VISIT_NESTING_DEPTH) {
      return;
    }


    // Walk down the member variables list and visit each one with the
    // current struct variable name as the prefix:
    memberVars = var->varType->memberListPtr;
    i = 0;
    curVar = 0;

    // No member variables
    if(!memberVars || !(memberVars->first))
      return;

    for (i = memberVars->first; i != 0; i = i->next) {
      UInt ind;
      void** pCurVarValueArray = 0;
      char* top;
      char numEltsPushedOnStack = 0;
      curVar = &(i->var);
      assert(curVar);

      // If a member variable is a statically-sized array which is
      // smaller than MAXIMUM_ARRAY_SIZE_TO_EXPAND and we have not
      // already performed array flattening, then we must expand the
      // member array and print it out in its flattened form with one
      // set of derived variable for every element in the array:
      if (VAR_IS_STATIC_ARRAY(curVar) &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(curVar->isString && (curVar->declaredPtrLevels == 1))) {
        // Only look at the first dimension:
        UInt arrayIndex;
        for (arrayIndex = 0; arrayIndex <= curVar->upperBounds[0]; arrayIndex++) {
          char indexStr[5];
          top = stringStackTop(fullNameStack, fullNameStackSize);

          sprintf(indexStr, "%d", arrayIndex);

          // TODO: Subtract and add is a HACK!  Subtract one from the
          // type of curVar just because we are looping through and
          // expanding the array
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count--;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          if (DTRACE_FILE == outputType) {
            // Create pCurVarValueArray to be the same size as pValueArray:
            pCurVarValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

            // Iterate though pValueArray and fill up
            // pCurVarValueArray with pointer values offset by the
            // location of the member variable within the struct plus
            // the offset given by the array index of the flattened array:
            for (ind = 0; ind < numElts; ind++) {
              // The starting address for the member variable is the
              // struct's starting address plus the location of the
              // variable within the struct
              if (pValueArray[ind]) {
                void* pCurVarValue = pValueArray[ind] + curVar->data_member_location;

                // Override for D_DOUBLE types: For some reason, the DWARF2
                // info.  botches the locations of double variables within
                // structs, setting their data_member_location fields to give
                // them only 4 bytes of padding instead of 8 against the next
                // member variable.  If curVar is a double and there exists a
                // next member variable such that the difference in
                // data_member_location of this double and the next member
                // variable is exactly 4, then decrement the double's location
                // by 4 in order to give it a padding of 8:
                if ((D_DOUBLE == curVar->varType->declaredType) &&
                    (i->next) &&
                    ((i->next->var.data_member_location -
                      curVar->data_member_location) == 4)) {
                  pCurVarValue -= 4;
                }

                // Very important!  Add the offset within the
                // flattened array:
                pCurVarValue += (arrayIndex * getBytesBetweenElts(curVar));

                // Now assign that value into pCurVarValueArray:
                pCurVarValueArray[ind] = pCurVarValue;
              }
              // If the original entry was 0, then simply copy 0, which
              // propagates uninit/unallocated status from structs to
              // members.
              else {
                pCurVarValueArray[ind] = 0;
              }
            }
          }

          // If the top element is '*', then instead of pushing a
          // '.' to make '*.', erase that element and instead push
          // '->'.  If last element is '->', then we're fine and
          // don't do anything else.  Otherwise, push a '.'
          if (top[0] == '*') {
            stringStackPop(fullNameStack, &fullNameStackSize);
            stringStackPush(fullNameStack, &fullNameStackSize, arrow);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, arrow)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(fullNameStack, &fullNameStackSize, dot);
            numEltsPushedOnStack = 1;
          }

          stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
          stringStackPush(fullNameStack, &fullNameStackSize, "[");
          stringStackPush(fullNameStack, &fullNameStackSize, indexStr);
          stringStackPush(fullNameStack, &fullNameStackSize, "]");

          numEltsPushedOnStack += 4;

          visitSequence(curVar,
                        0,
                        pCurVarValueArray,
                        numElts,
                        DERIVED_FLATTENED_ARRAY_VAR,
                        outputType,
                        allowVarDumpToFile,
                        trace_vars_tree,
                        OVERRIDE_NONE,
                        numStructsDereferenced + 1, // Notice the +1 here
                        varFuncInfo,
                        isEnter);

          // POP all the stuff we pushed on there before
          while ((numEltsPushedOnStack--) > 0) {
            stringStackPop(fullNameStack, &fullNameStackSize);
          }

          // HACK: Add the count back on at the end
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count++;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          // Only free if necessary
          if (pCurVarValueArray) {
            VG_(free)(pCurVarValueArray);
            pCurVarValueArray = 0;
          }
        }
      }
      // Regular member variable (without array flattening):
      else {

        if (DTRACE_FILE == outputType) {
          // Create pCurVarValueArray to be the same size as pValueArray:
          pCurVarValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

          // Iterate though pValueArray and fill up pCurVarValueArray
          // with pointer values offset by the location of the member
          // variable within the struct:
          for (ind = 0; ind < numElts; ind++) {
            // The starting address for the member variable is the
            // struct's starting address plus the location of the
            // variable within the struct TODO: Are we sure that
            // arithmetic on void* basePtrValue adds by 1?  Otherwise,
            // we'd have mis-alignment issues.  (I tried it in gdb and
            // it seems to work, though.)
            if (pValueArray[ind]) {
              void* pCurVarValue = pValueArray[ind] + curVar->data_member_location;

              // Override for D_DOUBLE types: For some reason, the DWARF2
              // info.  botches the locations of double variables within
              // structs, setting their data_member_location fields to give
              // them only 4 bytes of padding instead of 8 against the next
              // member variable.  If curVar is a double and there exists a
              // next member variable such that the difference in
              // data_member_location of this double and the next member
              // variable is exactly 4, then decrement the double's location
              // by 4 in order to give it a padding of 8:
              if ((D_DOUBLE == curVar->varType->declaredType) &&
                  (i->next) &&
                  ((i->next->var.data_member_location -
                    curVar->data_member_location) == 4)) {
                pCurVarValue -= 4;
              }

              // Now assign that value into pCurVarValueArray:
              pCurVarValueArray[ind] = pCurVarValue;
            }
            // If the original entry was 0, then simply copy 0, which
            // propagates uninit/unallocated status from structs to
            // members.
            else {
              pCurVarValueArray[ind] = 0;
            }
          }
        }

        top = stringStackTop(fullNameStack, fullNameStackSize);

        // If the top element is '*' or '[0]', then instead of pushing a
        // '.' to make '*.' or '[0].', erase that element and instead push
        // '->'.  If last element is '->', then we're fine and
        // don't do anything else.  Otherwise, push a '.'
        if ((top[0] == '*') || (VG_STREQ(top, zeroth_elt))) {
          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPush(fullNameStack, &fullNameStackSize, arrow);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, arrow)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, dot);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
        numEltsPushedOnStack++;

        visitSequence(curVar,
                      0,
                      pCurVarValueArray,
                      numElts,
                      (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                      outputType,
                      allowVarDumpToFile,
                      trace_vars_tree,
                      OVERRIDE_NONE,
                      numStructsDereferenced + 1, // Notice the +1 here
                      varFuncInfo,
                      isEnter);

        // POP everything we've just pushed on
        while ((numEltsPushedOnStack--) > 0) {
          stringStackPop(fullNameStack, &fullNameStackSize);
        }

        // Only free if necessary
        if (pCurVarValueArray) {
          VG_(free)(pCurVarValueArray);
          pCurVarValueArray = 0;
        }
      }
    }
  }
}
