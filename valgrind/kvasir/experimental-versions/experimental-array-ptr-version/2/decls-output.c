/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

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

// This increments every time outputDaikonVar is called and a full
// Daikon name is successfully generated.  It is used to index into
// the var_tags and new_tags arrays
int g_daikonVarIndex = 0;

FILE* decls_fp = 0; // File pointer for .decls file (this will point
                    // to the same thing as dtrace_fp by default since
                    // both .decls and .dtrace are outputted to .dtrace
                    // unless otherwise noted by the user)

static FILE* dev_null_fp; // initialized to "/dev/null"

// Only true if we are doing dtrace append and (!actually_output_separate_decls_dtrace)
char do_not_print_out_decls = 0;

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

// denotes the maximum number of structs (any kind of struct) to expand
// when dereferencing a Daikon variable (as opposed to MAX_STRUCT_INSTANCES,
// which limits the number of the SAME TYPE of struct - a la linked lists -
// to dereference in one Daikon variable)
int MAX_NUM_STRUCTS_TO_DEREFERENCE = 2;

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

// This array can be indexed using the DaikonDeclaredType enum
const char* DaikonDeclaredTypeString[] = {
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
const char* DaikonRepTypeString[] = {
  "no_rep_type", //R_NO_TYPE, // Create padding
  "int", //R_INT,
  "double", //R_DOUBLE,
  "hashcode", //R_HASHCODE,
  "java.lang.String" //R_STRING
};

// Useful stack of strings for printing out names
// Only puts REFERENCES to strings, does not do any allocating

// Yes, this is very dirty because it's a global variable ... ahhh!
// The stack which represents the full name of the variable
// that we currently want to print out
char* fullNameStack[MAX_STRING_STACK_SIZE];
int fullNameStackSize = 0;

static int createFIFO(const char *filename);

void stringStackPush(char** stringStack, int* stringStackSizePtr, char* str)
{
  if (!str) {
    VG_(printf)( "Null string passed to push!\n");
    /* abort(); */
    str = "<null>";
  }
  if (*stringStackSizePtr < MAX_STRING_STACK_SIZE)
    {
      stringStack[*stringStackSizePtr] = str;
      (*stringStackSizePtr)++;
    }
  // Don't push on stack overflow
}

char* stringStackPop(char** stringStack, int* stringStackSizePtr)
{
  if (*stringStackSizePtr > 0)
    {
      char* temp = stringStack[*stringStackSizePtr - 1];
      (*stringStackSizePtr)--;
      return temp;
    }
  else
    {
      return 0;
    }
}

char* stringStackTop(char** stringStack, int stringStackSize)
{
  return stringStack[stringStackSize - 1];
}

void stringStackClear(int* stringStackSizePtr)
{
  (*stringStackSizePtr) = 0;
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
// calloc'ed string (in proper order), and returns a pointer to that
char* strdupFullNameString(char** stringStack, int stringStackSize)
{
  int totalStrLen = stringStackStrLen(stringStack, stringStackSize) + 1; // 1 for trailing '\0'
  char* fullName = VG_(calloc)(totalStrLen, sizeof(char));
  int i;

  // REMEMBER TO GO BACKWARDS!!!
  for (i = stringStackSize - 1; i >=0; i--)
    {
      fullName = VG_(strcat)(fullName, stringStack[i]);
    }
  return fullName;
}

// Takes all of the strings on stringStack, copies them into a newly
// calloc'ed string (in proper order), and returns a pointer to that
// THIS GOES IN REVERSE ORDER so it actually acts like a queue
char* strdupFullNameStringReverse(char** stringStack, int stringStackSize)
{
  int totalStrLen = stringStackStrLen(stringStack, stringStackSize) + 1; // 1 for trailing '\0'
  char* fullName = VG_(calloc)(totalStrLen, sizeof(char));
  int i;

  for (i = 0; i < stringStackSize; i++)
    {
      fullName = VG_(strcat)(fullName, stringStack[i]);
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

  // TODO: This is opened but never closed ... does that even matter?
  dev_null_fp = fopen("/dev/null", "w");

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
    if (do_not_print_out_decls) {
      decls_fp = 0;
    }
    else {
      decls_fp = dtrace_fp;
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

// Remember to get the ordering right:
// -1 if *a < *b
//  0 if *a == *b
//  1 if *a > *b
/* int compareUInts(const void *a, const void *b) */
/* { */
/*   if ((*(UInt*)a) < (*(UInt*)b)) { */
/*     return -1; */
/*   } */
/*   else if ((*(UInt*)a) > (*(UInt*)b)) { */
/*     return 1; */
/*   } */
/*   else { */
/*     return 0; */
/*   } */
/* } */


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

  if (!do_not_print_out_decls) {

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

        if (!actually_output_separate_decls_dtrace) {
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
         fakeThisVar.ppt_enter_disambig = 'P';
         fakeThisVar.ppt_exit_disambig = 'P';

         fputs("DECLARE\n", decls_fp);
         fputs(cur_type->collectionName, decls_fp);
         fputs(":::OBJECT\n", decls_fp);

         stringStackPush(fullNameStack, &fullNameStackSize, "this");

         outputDaikonVar(&fakeThisVar,
                         FUNCTION_ENTER_FORMAL_PARAM,
                         0,0,0,0,0,0,
                         DECLS_FILE,
                         0,0,0,0,0,0,0,0,0,0);

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

      outputDaikonVar(var,
		      varOrigin,
		      0,
		      0,
		      0,
		      0,
		      allowVarDumpToFile,
		      trace_vars_tree,
		      outputType,
		      0,
		      basePtrValue,
		      0, //(varOrigin == GLOBAL_VAR), //overrideIsInitialized if global var // No, scratch that!
		      0,
		      0,
		      0,
		      0,
                      0,
                      funcPtr, isEnter);

      stringStackPop(fullNameStack, &fullNameStackSize);
    }
}


// Creates suffixes for variables by pushing elements onto
// fullNameStack.  If isArray is 1, then we should only push "[0]" to
// denote single pointer dereferences, but if isArray is 0, then we
// can push at most one "[]" to denote an array sequence and
// subsequent "[0]" to denote pointer dereferences:
/* static void pushNameSuffixes(int numDereferences, char isArray) { */
/*   if (numDereferences > 0) { */
/*     int ind; */

/*     if (isArray) { */
/*       for (ind = 0; ind < numDereferences; ind++) { */
/*         stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt); */
/*       } */
/*     } */
/*     else { */
/*       stringStackPush(fullNameStack, &fullNameStackSize, dereference); */

/*       for (ind = 1; ind < numDereferences; ind++) { */
/*         // Special suffix '*' output for repair tool */
/*         if (kvasir_repair_format) { */
/*           stringStackPush(fullNameStack, &fullNameStackSize, star); */
/*         } */
/*         else { */
/*           stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt); */
/*         } */
/*       } */
/*     } */
/*   } */
/* } */

// Pops the same number of elements regardless of the value of isArray
// Make sure this matches pushNameSuffixes or else our stack will be
// in trouble!
/* static void popNameSuffixes (int numDereferences) { */
/*   if (numDereferences > 0) { */
/*     int ind; */
/*     for (ind = 0; ind < numDereferences; ind++) { */
/*       stringStackPop(fullNameStack, &fullNameStackSize); */
/*     } */
/*   } */
/* } */

// THIS IS THE MAIN DECLS AND DTRACE OUTPUT FUNCTION!!!
// Prints one DaikonVariable variable and all of its derived
// variables to decls_fp if outputType == DECLS_FILE,
// prints the runtime value of one DaikonVariable variable and all of
// its derived variables to dtrace_fp if outputType == DTRACE_FILE,
// prints the multiplicity (pointer/array) of one DaikonVariable
// variable if outputType == DISAMBIG_FILE.
// Precondition: The full variable name that you want to print out
//               is located in fullNameStack
// MUST BE PRECEDED BY A stringStackPush() call and
// SUCCEEDED BY A stringStackPop() call because it expects names
// to be on the string stack
// TODO: We REALLY NEED to clean up this function and make it smaller.
// Perhaps take in function pointer parameters and delegate to separate
// handler functions for .decls, .dtrace, .disambig, and DynComp
void outputDaikonVar(DaikonVariable* var,
		     VariableOrigin varOrigin,
		     int numDereferences,
                     // True if we have already exhausted the one
                     // level of sequences that Daikon allows so that
                     // all further dereferences are single pointer
                     // dereferences (denoted by blah[0]):
		     char isAlreadyDaikonSequence,
		     char stopExpandingArrays,
		     char stopDerivingMemberVars,
		     char allowVarDumpToFile,
		     char* trace_vars_tree, // Binary tree within FunctionTree struct
		     OutputFileType outputType,
		     DisambigOverride disambigOverride, // Only relevant for .disambig
		     // The variables below are only valid if outputType == DTRACE_FILE:
		     void* basePtrValue, // the pointer to the first element to print to .dtrace
		     char overrideIsInitialized, // don't check init. bit - assume it's initialized
		     // We only use overrideIsInitialized when we pass in things (e.g. return values)
		     // that cannot be checked by the Memcheck A and V bits
		     // Never have overrideIsInitialized when you derive variables (make recursive calls)
		     // because their addresses are different from the original's
		     char isDummy, // don't actually print any values because the address is NONSENSICAL
		     unsigned long upperBound, // upper bound of the array to print
		     unsigned long bytesBetweenElts, // number of bytes between each element of array (TODO: Deprecate this - we don't want to use it anymore!)
		     char structParentAlreadySetArrayInfo,
                     // The number of structs we have dereferenced for this particular Daikon variable;
                     // Starts at 0 and increments every time we hit a variable which is a base struct type
                     // Range: [0, MAX_NUM_STRUCTS_TO_DEREFERENCE)
                     int numStructsDereferenced,
                     DaikonFunctionInfo* varFuncInfo, char isEnter) // These uniquely identify which program point we are printing (only relevant for DynComp purposes)
{
  DaikonDeclaredType dType = var->varType->declaredType;
  DaikonRepType rType = var->varType->repType;

  char* fullDaikonName = 0;

  int layersBeforeBase = (var->repPtrLevels - numDereferences);
  //  char isBaseArrayVar = (isAlreadyDaikonSequence && (var->repPtrLevels == 0));

  // Initialize these in a group later
  char printAsSequence = 0;
  char disambigOverrideArrayAsPointer = 0;
  char derefSingleElement = 0;

  FILE* out_file = 0;

  if (!var) {
    VG_(printf)( "Error! var is null in outputDaikonVar()\n");
    abort();
  }

  switch (outputType) {
  case DECLS_FILE: out_file = decls_fp; break;
  case DTRACE_FILE: out_file = dtrace_fp; break;
  case DISAMBIG_FILE: out_file = disambig_fp; break;
  case DYNCOMP_EXTRA_PROP: out_file = 0; break;
  case FAUX_DECLS_FILE: out_file = dev_null_fp; break;
  }

  // If it is an original variable (and not a Daikon-derived one),
  // then initialize a new VisitedStructsTable
  if ((varOrigin != DERIVED_VAR) &&
      (varOrigin != DERIVED_FLATTENED_ARRAY_VAR))
    {
      // Free VisitedStructsTable if necessary
      if (VisitedStructsTable)
	{
	  genfreehashtable(VisitedStructsTable);
	  VisitedStructsTable = 0;
	}
      VisitedStructsTable = genallocatehashtable((unsigned int (*)(void *)) & hashID,
						 (int (*)(void *,void *)) &equivalentIDs);
    }

  // Special handling for overriding in the presence of .disambig:
  // Only check this for non-derived (numDereferences == 0) variables
  // to ensure that it's only checked once per variable
  if ((0 == numDereferences) &&
      ((kvasir_disambig_filename && !disambig_writing) ||
       VG_STREQ("this", var->name))) { // either using .disambig or special C++ 'this'
    char disambig_letter = 0;

    char found = 1;

    // TODO: Don't the ENTER and EXIT .disambig values for a
    // particular variable have to be the same because Daikon expects
    // the same names and content format for both ENTER and EXIT ppts?
    switch (varOrigin) {
    case FUNCTION_ENTER_FORMAL_PARAM:
    case GLOBAL_VAR: // It doesn't matter (both should be identical)
    case DERIVED_VAR:
    case DERIVED_FLATTENED_ARRAY_VAR:
      disambig_letter = var->ppt_enter_disambig;
      break;
    case FUNCTION_EXIT_FORMAL_PARAM:
    case FUNCTION_RETURN_VAR:
      disambig_letter = var->ppt_exit_disambig;
      break;
    default:
      found = 0;
      break;
    }

    if (found) {
      if (var->repPtrLevels == 0) {
	// 'C' denotes to print out as a one-character string
	if (var->isString) { // pointer to "char" or "unsigned char"
	  if ('C' == disambig_letter) {
	    DPRINTF("String C - %s\n\n", var->name);
	    disambigOverride = OVERRIDE_STRING_AS_ONE_CHAR_STRING;
	  }
	  else if ('A' == disambig_letter) {
	    DPRINTF("String A - %s\n\n", var->name);
	    disambigOverride = OVERRIDE_STRING_AS_INT_ARRAY;
	  }
	  else if ('P' == disambig_letter) {
	    DPRINTF("String P - %s\n\n", var->name);
	    disambigOverride = OVERRIDE_STRING_AS_ONE_INT;
	  }
	}
	else if ((D_CHAR == var->varType->declaredType) ||  // "char" or "unsigned char" (or string of chars)
		 (D_UNSIGNED_CHAR == var->varType->declaredType)) { // "char" or "unsigned char"
	  if ('C' == disambig_letter) {
	    DPRINTF("Char C - %s\n\n", var->name);
	    disambigOverride = OVERRIDE_CHAR_AS_STRING;
	  }
	}
      }
      // Ordinary pointer
      else if ('P' == disambig_letter) {
	disambigOverride = OVERRIDE_ARRAY_AS_POINTER;
      }
    }
  }

  disambigOverrideArrayAsPointer =
    (kvasir_disambig_ptrs ||
     (OVERRIDE_ARRAY_AS_POINTER == disambigOverride));

  // This clause is very important in controlling the correct output
  // format (scalar or sequence).  If we are already printing as a
  // sequence, then .disambig for this variable has no effect.
  // However, if we are not yet printing as a sequence, then the
  // .disambig does have an effect.
  printAsSequence = (isAlreadyDaikonSequence ||
                     (!disambigOverrideArrayAsPointer && (numDereferences > 0)));


  // If we are already a sequence or (if we are not) we choose to
  // disambiguate arrays as pointers, then we are dereferencing to
  // print out a single element instead of trying to print out an
  // array of elements:
  derefSingleElement = (isAlreadyDaikonSequence ||
                        disambigOverrideArrayAsPointer);


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

  // .decls, .dtrace, and .disambig files -
  //  Line 1: Print out name
  if (fullNameStackSize > 0)
    {
      // We are really popping stuff off of the stack in reverse and
      // treating it like a queue :)
      fullDaikonName = strdupFullNameStringReverse(fullNameStack, fullNameStackSize);

      // Now we must check whether we are interested in printing out
      // this variable - if we are not, then punt everything!  This
      // means that no 'children' of this variable will get printed
      // out if this variable is not printed out.  For example, if
      // 'foo' is an array, then if the hashcode value of 'foo' is not
      // printed out, then the actual array value of 'foo[]' won't be
      // printed out either.
      if (kvasir_trace_vars_filename)
	{
	  if (trace_vars_tree)
	    {
	      if (!tfind((void*)fullDaikonName, (void**)&trace_vars_tree, compareStrings))
		{
		  DPRINTF("%s NOT FOUND!!!\n", fullDaikonName);
		  // PUNT EVERYTHING!!!
		  VG_(free)(fullDaikonName);
		  return;
		}
	    }
	  // If trace_vars_tree is kept at 0 on purpose
	  // but kvasir_trace_vars_filename is valid, then still punt
	  // because we are only supposed to print out variables listed
	  // in kvasir_trace_vars_filename and obviously there aren't
	  // any relevant variables to print
	  else
	    {
	      VG_(free)(fullDaikonName);
	      return;
	    }
	}

      if (var_dump_fp && allowVarDumpToFile)
	{
          fputs(fullDaikonName, var_dump_fp);
	}

      if (out_file) {
        fputs(fullDaikonName, out_file);
      }

      // .dtrace and DynComp will need this for keeping track of
      // run-time info, so don't free the name for those runs:
      if ((DTRACE_FILE != outputType) &&
          (DYNCOMP_EXTRA_PROP != outputType)) {
        VG_(free)(fullDaikonName);
      }

      VG_(printf)("%s\n", fullDaikonName);
    }
  else
    {
      VG_(printf)( "Error! fullNameStack is empty in outputDaikonVar() - no name to print\n");
      abort();
    }

  if (var_dump_fp && allowVarDumpToFile)
    {
      fputs("\n", var_dump_fp);
    }

  if (out_file) {
    fputs("\n", out_file);
  }

  // .dtrace
  if (DTRACE_FILE == outputType)
    {
      char variableHasBeenObserved = 0;
      DPRINTF("printOneDaikonVar: %s %d %d %d %d %d %d %p %d %d %u %u\n",
	      var->name,
	      varOrigin,
	      numDereferences,
	      isAlreadyDaikonSequence,
	      stopExpandingArrays,
	      stopDerivingMemberVars,
	      (int)outputType,
	      basePtrValue,
	      overrideIsInitialized,
	      isDummy,
	      upperBound,
	      bytesBetweenElts);

      variableHasBeenObserved =
	outputDtraceValue(var,
			  basePtrValue,
			  varOrigin,
			  (layersBeforeBase > 0), // isHashcode
			  overrideIsInitialized,
			  isDummy,
			  printAsSequence,
			  upperBound,
			  bytesBetweenElts,
			  // override float as double when printing
			  // out function return variables because
			  // return variables stored in %EAX are always doubles
			  (varOrigin == FUNCTION_RETURN_VAR),
			  disambigOverride);

      // DynComp post-processing:
      if (kvasir_with_dyncomp && variableHasBeenObserved) {
        Addr a;

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

          // Special handling for strings.  We are not interested in the
          // comparability of the 'char*' pointer variable, but rather
          // we are interested in the comparability of the CONTENTS of
          // the string.  (Be careful about statically-declared strings,
          // in which case the address of the first element is the address
          // of the pointer variable)
          if (var->isString &&
              (0 == layersBeforeBase)) {
            // Depends on whether the variable is a static array or not:
            a = var->isStaticArray ?
              (Addr)basePtrValue :
              *((Addr*)(basePtrValue));
          }
          else {
            a = (Addr)basePtrValue;
          }

          DYNCOMP_DPRINTF("%s (%d) ", fullDaikonName, g_daikonVarIndex);
          DC_post_process_for_variable(varFuncInfo,
                                       isEnter,
                                       g_daikonVarIndex,
                                       a);
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
	if (printAsSequence && (upperBound > 0)) {
          //	if (!disambigOverrideArrayAsPointer && (upperBound > 0)) {
	  var->disambigMultipleElts = 1;
	}

	// If pointerHasEverBeenObserved is not set, then set it
	if (!var->pointerHasEverBeenObserved) {
	  var->pointerHasEverBeenObserved = 1;
	}
      }

      VG_(free)(fullDaikonName);
    }
  // .decls
  else if ((DECLS_FILE == outputType) || (FAUX_DECLS_FILE == outputType))
    {
      char alreadyPutDerefOnLine3;
      int layers;
      // .decls Line 2: Print out declared type

      if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
	fputs(DaikonRepTypeString[R_INT], out_file);
	fputs(dereference, out_file);
      }
      else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
	fputs(DaikonRepTypeString[R_INT], out_file);
      }
      // named struct/union or enumeration
      else if (((dType == D_ENUMERATION) || (dType == D_STRUCT) || (dType == D_UNION)) &&
	       var->varType->collectionName)
	{
	  fputs(var->varType->collectionName, out_file);
	}
      else
	{
	  // Normal type (or unnamed struct/union)
	  fputs(DaikonDeclaredTypeString[dType], out_file);
	  // If we have a string, print it as char*
	  // because the dType of string is "char"
	  // so we need to append a "*" to it
	  if (var->isString)
	    {
	      fputs(star, out_file);
	    }
	}

      // For the declared type, print out one level of '*' for every
      // layer above base to denote pointer types
      for (layers = 0; layers < layersBeforeBase; layers++) {
        fputs(star, out_file);
        // TODO: Determine later whether this special case is worth it:
        // Special case for static array types: use a '[]' to
        // replace the LAST '*'
        //        if ((var->isStaticArray) &&
        //            (layers == (layersBeforeBase - 1))) {
        //          fputs(dereference, out_file);
        //        }
        //        else {
        //          fputs(star, out_file);
        //        }
      }

      // If we print this as a sequence, then we must append '[]'
      if (printAsSequence) {
        fputs(dereference, out_file);
      }

      // Original variables in function parameter lists
      // have "# isParam = true"
      if ((varOrigin == FUNCTION_ENTER_FORMAL_PARAM) ||
	  (varOrigin == FUNCTION_EXIT_FORMAL_PARAM))
	{
	  fputs(" # isParam=true", out_file);
	}
      fputs("\n", out_file);


      // .decls Line 3: Print out rep. type
      alreadyPutDerefOnLine3 = 0;

      // Print out rep. type as hashcode when you are not done dereferencing
      // pointer layers:
      if (layersBeforeBase > 0)
	{
	  fputs(DaikonRepTypeString[R_HASHCODE], out_file);
	}
      else
	{
	  // Special handling for strings and 'C' chars in .disambig
	  if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
	      fputs(DaikonRepTypeString[R_INT], out_file);
	      fputs(dereference, out_file);
	      alreadyPutDerefOnLine3 = 1;
	  }
	  else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
	      fputs(DaikonRepTypeString[R_INT], out_file);
	  }
	  else if ((var->isString) ||
		   (OVERRIDE_CHAR_AS_STRING == disambigOverride)) {
	    fputs(DaikonRepTypeString[R_STRING], out_file);
	  }
	  else {
            tl_assert(rType != 0);
	    fputs(DaikonRepTypeString[rType], out_file);
	  }
	}

      // Append "[]" onto the end of the rep. type if necessary
      if (!alreadyPutDerefOnLine3 &&
          printAsSequence) {
        fputs(dereference, out_file);
      }

      fputs("\n", out_file);

      // .decls Line 4: Comparability number

      // If we are outputting a REAL .decls with DynComp, that means
      // that the program has already finished execution so that all
      // of the comparability information would be already updated:
      if (kvasir_with_dyncomp &&
          (DECLS_FILE == outputType)) {
        // Remember that comp_number is a SIGNED INTEGER but the
        // tags are UNSIGNED INTEGERS so be careful of overflows
        // which result in negative numbers, which are useless
        // since Daikon ignores them.
        int comp_number = DC_get_comp_number_for_var(varFuncInfo,
                                                     isEnter,
                                                     g_daikonVarIndex);
        fprintf(out_file, "%d", comp_number);
        fputs("\n", out_file);
      }
      else {
        // Print out unknown comparability type "22"
        fputs("22", out_file);
        fputs("\n", out_file);
      }
    }
  // DynComp - extra propagation at the end of the program's execution
  else if (DYNCOMP_EXTRA_PROP == outputType) {
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
      DYNCOMP_DPRINTF("%s (%d) ", fullDaikonName, g_daikonVarIndex);

      DC_extra_propagation_post_process(varFuncInfo,
                                        isEnter,
                                        g_daikonVarIndex);
    }
    VG_(free)(fullDaikonName);
  }
  // .disambig
  else if (DISAMBIG_FILE == outputType)
    {
      // Line 2: Print out .disambig code for each type
      // as specified in the "Daikon User Manual" and
      // also decisions made by the Kvasir developers

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
	  fputs("I", out_file);
	}
      }
      // Normal string, not pointer to string
      else if (var->isString && (0 == var->repPtrLevels)) {
	fputs("S", out_file);
      }
      else if (var->repPtrLevels > 0) {
	if (var->isStructUnionMember) {
	  fputs("A", out_file);
	}
	else {
	  if (var->pointerHasEverBeenObserved) {
	    if (var->disambigMultipleElts) {
	      fputs("A", out_file);
	    }
	    else {
	      fputs("P", out_file);
	    }
	  }
	  // default behavior for variable that was
	  // never observed during the execution
	  else {
	    fputs("A", out_file);
	  }
	}
      }

      fputs("\n", out_file);
      // DO NOT DERIVE VARIABLES for .disambig
      // We are only interested in printing out
      // the variables which are immediately
      // visible to the user
      return;
    }
  else
    {
      VG_(printf)( "Error! Invalid outputType in outputDaikonVar()\n");
      abort();
    }


  } // end if (!((layersBeforeBase == 0) && (var->varType->isStructUnionType)))



  // Be very careful about where you increment this!
  g_daikonVarIndex++;

  // Dereference and keep on printing out derived variables until we hit the base type:
  if (layersBeforeBase > 0)
    {
      void* ptrParam = 0;

      DPRINTF("layersBeforeBase is %d\n", layersBeforeBase);

      DPRINTF("isDummy=%d\n", isDummy);

      // If we are printing .dtrace, set ptrParam, upperBound, and bytesBetweenElts
      // for the derived variable that we want to print out:
      if ((DTRACE_FILE == outputType) && !isDummy)
	{
	  // Set isDummy appropriately depending on whether the derived variable
	  // is allocated and initialized:
	  char derivedIsAllocated = 0;
	  char derivedIsInitialized = 0;

	  DPRINTF("In array bounding branch\n");

	  // Recursively dereference this variable to print out another one,
	  // which should either be another pointer or a final
	  // struct/union/base/enumeration type -
	  // Pass the DEREFERENCED pointer value as the basePtrValue argument
	  // unless it's a statically-declared array, in which case, simply pass
	  // the value of the pointer as the argument:
	  if (var->isStaticArray)
	    {
	      ptrParam = basePtrValue;
	      // TODO: Investigate this more carefully, but it seems to work for now:
	      derivedIsAllocated = 1;
	      derivedIsInitialized = 1;
	    }
	  else
	    {
	      derivedIsAllocated = (overrideIsInitialized ? 1 :
				    addressIsAllocated((Addr)basePtrValue, sizeof(void*)));
	      if (derivedIsAllocated)
		{
		  derivedIsInitialized = (overrideIsInitialized ? 1 :
					  addressIsInitialized((Addr)basePtrValue, sizeof(void*)));
		  ptrParam = *((void **)basePtrValue);
		}
	    }

	  // If the derived variable is either unallocated or uninitialized,
	  // then it should print out as NONSENSICAL so isDummy should be "true"
	  isDummy |= !derivedIsAllocated;
	  isDummy |= !derivedIsInitialized;

	  // Special case for multi-dimensional arrays (numDereferences >= 1):
	  // Just print out the first dimension.  You would rather maintain
	  // the integrity and lose info about the rest of the dimensions than
	  // print out random garbage values like we previously did
	  if (((numDereferences >= 1) || // multi-dimensional arrays - always recalculate bounds
	       (!structParentAlreadySetArrayInfo)) &&
	      // If at ANY time, this next condition holds, we don't
	      // want to trigger structParentAlreadySetArrayInfo
	      (disambigOverride != OVERRIDE_ARRAY_AS_POINTER))
	    {
	      if (!var->isStaticArray && ptrParam)
		{
		  DPRINTF("In dynamic array bounding branch\n");

		  upperBound = returnArrayUpperBoundFromPtr(var, (Addr)ptrParam);

		  DPRINTF("upperBound for %s(%p) = %u\n",
			  var->name, ptrParam, upperBound);
		}
	      else if VAR_IS_STATIC_ARRAY(var)
		{
		  // TODO: Add multi-dimensional array support -
		  // Right now we only look at the first dimension
		  upperBound = var->upperBounds[0];

		  DPRINTF("upperBound for %s = %u\n",
			  var->name, upperBound);
		}

	      bytesBetweenElts = getBytesBetweenElts(var);
	      structParentAlreadySetArrayInfo = 1;
	    }
	}

      // Push one symbol onto stack to represent the dereference:
      if (derefSingleElement) {
        if (kvasir_repair_format) {
          stringStackPush(fullNameStack, &fullNameStackSize, star);
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt);
        }
      }
      else {
        stringStackPush(fullNameStack, &fullNameStackSize, dereference);
      }

      outputDaikonVar(var,
		      ((varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ?
		       DERIVED_FLATTENED_ARRAY_VAR :
		       DERIVED_VAR),
		      numDereferences + 1,
                      // If we are dereferencing a single element,
                      // keep the existing value of is
                      // AlreadyDaikonSequence; otherwise, definitely
                      // set it to 1:
		      (derefSingleElement ? isAlreadyDaikonSequence : 1),
		      stopExpandingArrays,
		      stopDerivingMemberVars,
		      allowVarDumpToFile,
		      trace_vars_tree,
		      outputType,
		      disambigOverride,
		      (isDummy ? 0 : ptrParam),
		      0,
		      isDummy,
		      (isDummy ? 0 : upperBound),
		      (isDummy ? 0 : bytesBetweenElts),
		      structParentAlreadySetArrayInfo,
                      numStructsDereferenced,
                      varFuncInfo, isEnter);

      // Pop one symbol off
      stringStackPop(fullNameStack, &fullNameStackSize);
    }
  // If this is the base type of a struct/union variable, then print out all
  // derived member variables:
  else if ((!stopDerivingMemberVars) &&
	   (var->varType->isStructUnionType))
    {
      VarList* memberVars;
      VarNode* i;
      DaikonVariable* curVar;
      // Check to see if the VisitedStructsTable contains
      // more than MAX_STRUCT_INSTANCES of the current struct type -
      // (later we will bail out if it contains more than this amount in order
      //  to prevent infinite loops for recursively-defined structs)
      if (gencontains(VisitedStructsTable, (void*)(var->varType)))
	{
	  int count = (int)(gengettable(VisitedStructsTable, (void*)(var->varType)));
	  if (count <= MAX_STRUCT_INSTANCES)
	    {
	      count++;
	      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
	    }
	}
      // If not found in the table, initialize this entry with 1
      else
	{
	  genputtable(VisitedStructsTable, (void*)(var->varType), (void*)1);
	}

      // Walk down the member variables list and
      // print each one out with the current struct variable
      // name as the prefix:
      memberVars = var->varType->memberListPtr;
      i = 0;
      curVar = 0;

      if(!memberVars || !(memberVars->first))
	return;

      for (i = memberVars->first; i != 0; i = i->next)
	{
	  int tempStopDerivingMemberVars = 0;
	  void* curVarBasePtr;
	  curVar = &(i->var);

	  assert(curVar);

	  // The starting address for the member variable is the struct's
	  // starting address plus the location of the variable within the struct
	  // TODO: Are we sure that arithmetic on void* basePtrValue
	  // adds by 1?  Otherwise, we'd have mis-alignment issues.
	  // (I tried it in gdb and it seems to work, though.)
	  curVarBasePtr = basePtrValue + curVar->data_member_location;

	  // Override for D_DOUBLE types: For some reason, the DWARF2 info.
	  // botches the locations of double variables within structs, setting
	  // their data_member_location fields to give them only 4 bytes of
	  // padding instead of 8 against the next member variable.
	  // If curVar is a double and there exists a next member variable
	  // such that the difference in data_member_location of this double
	  // and the next member variable is exactly 4, then decrement the
	  // double's location by 4 in order to give it a padding of 8:
	  if ((D_DOUBLE == curVar->varType->declaredType) &&
	      (i->next) &&
	      ((i->next->var.data_member_location -
		curVar->data_member_location) == 4)) {
	    curVarBasePtr -= 4;
	  }

	  // If a struct type has appeared more than MAX_STRUCT_INSTANCES
	  // times or if (numStructsDereferenced >= MAX_NUM_STRUCTS_TO_DEREFERENCE),
          // then stop deriving variables from it:
	  if ((numStructsDereferenced >= MAX_NUM_STRUCTS_TO_DEREFERENCE) ||
              (gencontains(VisitedStructsTable, (void*)(curVar->varType)) &&
	      ((int)(gengettable(VisitedStructsTable, (void*)(curVar->varType))) >
	       MAX_STRUCT_INSTANCES)))
	    {
	      tempStopDerivingMemberVars = 1;
	    }

	  // If a member variable is a statically-sized array
	  // and the current variable is already an array,
	  // then we must expand the member array and print it
	  // out in its flattened form with one set of derived
	  // variable for every element in the array:
	  if (printAsSequence &&
	      VAR_IS_STATIC_ARRAY(curVar) &&
	      !stopExpandingArrays &&
	      (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
	      // Ignore arrays of characters (strings) inside of the struct:
	      !(curVar->isString && (curVar->declaredPtrLevels == 1)))
	    {
	      // Only look at the first dimension:
	      int arrayIndex = 0;
	      for (arrayIndex = 0; arrayIndex <= curVar->upperBounds[0]; arrayIndex++)
		{
                  char* top = stringStackTop(fullNameStack, fullNameStackSize);
                  char numEltsPushedOnStack = 0;

		  char indexStr[5];
		  sprintf(indexStr, "%d", arrayIndex);

		  // TODO: Subtract and add is a HACK!
		  // Subtract one from the type of curVar just because
		  // we are looping through and expanding the array
		  if (gencontains(VisitedStructsTable, (void*)(var->varType)))
		    {
		      int count = (int)(gengettable(VisitedStructsTable, (void*)(var->varType)));
		      count--;
		      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
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

		  // Set bytesBetweenElts to the size of the largest enclosing struct
		  // that is also an array
		  // e.g. struct A takes up 100 bytes and contains an array of 3 struct B's, each
		  // of which take up 10 bytes.  Each B contains a struct C, which takes up 8 bytes.
		  // Each C contains a 4-byte int x, which we want to print out.  Here is the layout:
		  /*

		  [              A               ][              A               ][               A              ]


		  [ {   B   }{   B   }{   B   }  ][ {   B   }{   B   }{   B   }  ][ {   B   }{   B   }{   B   }  ]


		  [ { (  C )}{ (  C )}{ (  C )}  ][ { (  C )}{ (  C )}{ (  C )}  ][ { (  C )}{ (  C )}{ (  C )}  ]


		  [ { (  x )}{ (  x )}{ (  x )}  ][ { (  x )}{ (  x )}{ (  x )}  ][ { (  x )}{ (  x )}{ (  x )}  ]


		  In order to properly print out x, we need a spacing in between x's that is equal
		  to the size of struct B, NOT struct C, since B itself is an array but C isn't an array.

		  Also, the upperBound should be set to the upper bound of that struct array as well.
		  */

                  //                  VG_(printf)("   %s[%s] isAlreadyDaikonSequence: %d, numDereferences: %d\n",
                  //                              curVar->name, indexStr, isAlreadyDaikonSequence, numDereferences);

		  outputDaikonVar(curVar,
				  DERIVED_FLATTENED_ARRAY_VAR,
				  0,
                                  // Only change isAlreadyDaikonSequence from 0 to 1
                                  // if we have dereferenced to get
                                  // here:
                                  isAlreadyDaikonSequence,
                                  !isAlreadyDaikonSequence,
				  tempStopDerivingMemberVars,
				  allowVarDumpToFile,
				  trace_vars_tree,
				  outputType,
				  0,
				  (isDummy ? 0 :
				   // Need to add an additional offset:
				   curVarBasePtr + (arrayIndex *
						    getBytesBetweenElts(curVar))), //curVar->varType->byteSize)),
				  0,
				  isDummy,
				  (isDummy ? 0 :
				   upperBound),
				  // Use var's byteSize, not curVar's byte size
				  // in order to determine the number of bytes
				  // between each element of curVar:
				  (isDummy ? 0 :
				   getBytesBetweenElts(var)), // var->varType->byteSize),
				  structParentAlreadySetArrayInfo,
                                  (numStructsDereferenced + 1),
                                  varFuncInfo, isEnter);

		  // POP all the stuff we pushed on there before
                  while ((numEltsPushedOnStack--) > 0) {
                    stringStackPop(fullNameStack, &fullNameStackSize);
                  }

		  // HACK: Add the count back on at the end
		  if (gencontains(VisitedStructsTable, (void*)(var->varType)))
		    {
		      int count = (int)(gengettable(VisitedStructsTable, (void*)(var->varType)));
		      count++;
		      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
		    }
		}
	    }
	  // Print out a regular member variable without array flattening
	  else
	    {
              char* top = stringStackTop(fullNameStack, fullNameStackSize);
              char numEltsPushedOnStack = 0;

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

	      DPRINTF("-- %s -- override %d repPtrLevels %d isString %d... %c %c\n",
		      curVar->name, disambigOverride, curVar->repPtrLevels, curVar->isString,
		      curVar->ppt_enter_disambig, curVar->ppt_exit_disambig);

	      outputDaikonVar(curVar,
			      DERIVED_VAR,
			      0,
                              isAlreadyDaikonSequence,
                              // TODO: This still looks shady
                              (isAlreadyDaikonSequence ? 0 : stopExpandingArrays),
			      // Complex conditional:
			      // Do not derive any more member variables
			      // once we have said to stop expanding arrays
			      ((!curVar->isStaticArray ||
				(!stopExpandingArrays && curVar->isStaticArray)) ?
			       tempStopDerivingMemberVars : 1),
			      allowVarDumpToFile,
			      trace_vars_tree,
			      outputType,
			      0,
			      (isDummy ? 0 :
			       curVarBasePtr),
			      0,
			      isDummy,
			      (isDummy ? 0 :
			       upperBound),
			      (isDummy ? 0 :
			       bytesBetweenElts),
			      structParentAlreadySetArrayInfo,
                              (numStructsDereferenced + 1),
                              varFuncInfo, isEnter);

	      // POP everything we've just pushed on
              while ((numEltsPushedOnStack--) > 0) {
                stringStackPop(fullNameStack, &fullNameStackSize);
              }
	    }
	}
    }
}
