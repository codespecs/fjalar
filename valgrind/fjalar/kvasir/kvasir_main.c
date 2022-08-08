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

/* kvasir_main.c:
   Initialization code, command-line option handling, and file handling
*/

#define _FILE_OFFSET_BITS 64
#define _LARGEFILE64_SOURCE /* FOR O_LARGEFILE */

#include "../my_libc.h"

#include "../fjalar_tool.h"
#include "../fjalar_include.h"

#include "pub_tool_libcfile.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_debuginfo.h"

#include "kvasir_main.h"
#include "decls-output.h"
#include "dtrace-output.h"

#include "dyncomp_main.h"
#include "dyncomp_runtime.h"

extern void setNOBUF(FILE *stream);

// Global variables that are set by command-line options
const HChar* kvasir_decls_filename = 0;
const HChar* kvasir_dtrace_filename = 0;
const HChar* kvasir_program_stdout_filename = 0;
const HChar* kvasir_program_stderr_filename = 0;
Bool kvasir_dtrace_append = False;
Bool kvasir_dtrace_no_decls = False;
Bool kvasir_dtrace_gzip = False;
Bool kvasir_output_fifo = False;
Bool kvasir_decls_only = False;
Bool kvasir_print_debug_info = False;
Bool actually_output_separate_decls_dtrace = 0;
Bool print_declarations = 1;

Bool kvasir_with_dyncomp = True;
Bool dyncomp_no_gc = False;
Bool dyncomp_approximate_literals = False;
Bool dyncomp_detailed_mode = False;
int  dyncomp_gc_after_n_tags = 10000000;
Bool dyncomp_without_dtrace = False;
Bool dyncomp_print_debug_info = False;
Bool dyncomp_print_trace_info = False;
Bool dyncomp_print_trace_all = False;
Bool dyncomp_print_incremental = False;
Bool dyncomp_separate_entry_exit = False;
Bool dyncomp_trace_startup = False;
Bool dyncomp_delayed_print_IR = True;
Bool dyncomp_delayed_trace = True;

// Special modes for DynComp
// Changes the definition of what constitutes an interaction
Bool dyncomp_units_mode = False;                // Tries to be consistent with units
Bool dyncomp_dataflow_only_mode = False;        // Nothing is an interaction
Bool dyncomp_dataflow_comparisons_mode = False; // Only comparisons are interactions


FILE* decls_fp = 0; // File pointer for .decls file (this will point
                    // to the same thing as dtrace_fp by default since
                    // both .decls and .dtrace are outputted to .dtrace
                    // unless otherwise noted by the user)

FILE* dtrace_fp = 0; // File pointer for dtrace file (from dtrace-output.c)
static const char *dtrace_filename; /* File name to open dtrace_fp on */

const char* decls_folder = "daikon-output/";
static const char* decls_ext = ".decls";
static const char* dtrace_ext = ".dtrace";

static int createFIFO(const char *filename);
static int openDtraceFile(const char *fname);
static char splitDirectoryAndFilename(const char* input, char** dirnamePtr, char** filenamePtr);

// Lots of boring file-handling stuff:

static void openTheDtraceFile(void) {
  openDtraceFile(dtrace_filename);
  VG_(free)((void*)dtrace_filename);
  dtrace_filename = 0;
}

// if (actually_output_separate_decls_dtrace):
//   Create a decls file with the name "daikon-output/x.decls"
//   where x is the application name (by default)
//   and initializes the file pointer decls_fp.
//   Also creates a corresponding .dtrace file, but doesn't open it yet.
// else: --- (DEFAULT)
//   Create a dtrace file and initialize both decls_fp and dtrace_fp
//   to point to it
static void createDeclsAndDtraceFiles(const HChar* appname)
{
  char* dirname = 0;
  char* filename = 0;
  char* newpath_decls = 0;
  char* newpath_dtrace;
  SysRes res;

  // Free VisitedStructsTable if it has been allocated
  if (VisitedStructsTable)
    {
      genfreehashtable(VisitedStructsTable);
    }
  VisitedStructsTable = 0;

  // Step 1: Make a path to .decls and .dtrace files
  //         relative to daikon-output/ folder

  if (!splitDirectoryAndFilename(appname, &dirname, &filename))
    {
      printf( "Failed to parse path: %s\n", appname);
    }

  DPRINTF("**************\ndirname=%s, filename=%s\n***********\n",
	  dirname, filename);

  if (actually_output_separate_decls_dtrace) {
    if (kvasir_decls_filename) {
      newpath_decls = VG_(strdup)("kvasir_main.c: createDecls.1", kvasir_decls_filename);
    }
    else {
      newpath_decls = (char*)VG_(malloc)("kvasir_main.c: createDecls.2", (VG_(strlen)(decls_folder) +
					  VG_(strlen)(filename) +
					  VG_(strlen)(decls_ext) + 1) *
					 sizeof(char));

      VG_(strcpy)(newpath_decls, decls_folder);
      VG_(strcat)(newpath_decls, filename);
      VG_(strcat)(newpath_decls, decls_ext);
    }

    if (kvasir_dtrace_filename) {
      newpath_dtrace = VG_(strdup)("kvasir_main.c: createDecls.3", kvasir_dtrace_filename);
    }
    else {
      newpath_dtrace = (char*)VG_(malloc)("kvasir_main.c: createDecls.4", (VG_(strlen)(decls_folder) +
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
      newpath_dtrace = VG_(strdup)("kvasir_main.c: createDecls.5", kvasir_dtrace_filename);
    }
    else {
      newpath_dtrace = (char*)VG_(malloc)("kvasir_main.c: createDecls.6", (VG_(strlen)(decls_folder) +
					   VG_(strlen)(filename) +
					   VG_(strlen)(dtrace_ext) + 1) *
					  sizeof(char));

      VG_(strcpy)(newpath_dtrace, decls_folder);
      VG_(strcat)(newpath_dtrace, filename);
      VG_(strcat)(newpath_dtrace, dtrace_ext);
    }
  }

  // Step 2: Make the daikon-output/ directory
  res = VG_(mkdir)(decls_folder, 0777); // more abbreviated UNIX form
  if (sr_isError(res) && sr_Err(res) != VKI_EEXIST)
    printf( "Couldn't create %s: %s\n", decls_folder,
		 my_strerror(sr_Err(res)));

  // ASSUME mkdir succeeded! (or that the directory already exists)

  // Step 3: Make the .decls and .dtrace FIFOs, if requested
  if (kvasir_output_fifo) {
    if (actually_output_separate_decls_dtrace) {
      if (!createFIFO(newpath_decls))
	printf( "Trying as a regular file instead.\n");
      if (!createFIFO(newpath_dtrace))
	printf( "Trying as a regular file instead.\n");
    }
    else {
      if (!createFIFO(newpath_dtrace))
	printf( "Trying as a regular file instead.\n");
    }
  }

  dtrace_filename = VG_(strdup)("kvasir_main.c: createDecls.7", newpath_dtrace); /* But don't open it til later */

  // Step 4: Open the .decls file for writing
  if (actually_output_separate_decls_dtrace) {
    // add support for decls file output to stdout  (markro)  
    if VG_STREQ(newpath_decls, "-") {
      SysRes sr = VG_(dup)(1);
      int decls_fd = sr_Res(sr);
      /* Check sr.isError? */
      decls_fp = fdopen(decls_fd, "w");
      if (decls_fp) {
        // If we're debugging, turn off buffering to get commingled output. 
        if (kvasir_print_debug_info) {
          setNOBUF(decls_fp);
        }    
      }
    } else {
      decls_fp = fopen(newpath_decls, "w");
    }

    if (!decls_fp)
      printf("Failed to open %s for declarations: %s\n",
             newpath_decls, my_strerror(errno));
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
// (comment added 2005)  
// TODO: This can be replaced with calls to the glibc dirname() and basename() functions
static char splitDirectoryAndFilename(const char* input, char** dirnamePtr, char** filenamePtr)
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
          filename = VG_(malloc)("kvasir_main.c: splitDir.1", (len - i) * sizeof(char));
          dirname = VG_(malloc)("kvasir_main.c: splitDir.2", (i + 2) * sizeof(char));

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
  filename = VG_(strdup)("kvasir_main.c: splitDir.3", input);
  *filenamePtr = filename;
  return 1;
}

static int createFIFO(const char *filename) {
  int ret;
  ret = VG_(unlink)((char *)filename);
  if (ret == -1) {
    printf( "Couldn't replace old file %s: %s\n", filename,
		 my_strerror(ret));
    return 0;
  }
  ret = mkfifo(filename, 0666);
  if (ret == -1) {
    printf( "Couldn't make %s as a FIFO: %s\n", filename,
		 my_strerror(errno));
    return 0;
  }
  return 1;
}


/* Return a file descriptor for a stream with similar semantics to
   what you'd get in a Unix shell by saying ">fname". Prints an error
   and returns -1 if something goes wrong. */
static int openRedirectFile(const char *fname) {
  int new_fd;
  SysRes sr;
  if (fname[0] == '&') {
    sr = VG_(dup)(atoi(fname + 1));
    if (sr_isError(sr)) {
      printf( "Couldn't duplicate FD `%s': %s\n",
		   fname+1, my_strerror(sr_Err(sr)));
      return -1;
    }
    new_fd = sr_Res(sr);
  } else {
    sr = VG_(open)(fname, VKI_O_WRONLY|VKI_O_CREAT|VKI_O_LARGEFILE|VKI_O_TRUNC,
		  0666);
    if (sr_isError(sr)) {
      printf( "Couldn't open %s for writing: %s\n",
		   fname, my_strerror(sr_Err(sr)));
      return -1;
    }
    new_fd = sr_Res(sr);
  }
  return new_fd;
}

static int gzip_pid = 0;

static int openDtraceFile(const char *fname) {
  const char *mode_str;
  const char *stdout_redir = kvasir_program_stdout_filename;
  const char *stderr_redir = kvasir_program_stderr_filename;

  char *env_val = VG_(getenv)("DTRACEAPPEND");
  if (env_val || kvasir_dtrace_append) {
    // I've commented this out because multiple decls permits Daikon to
    // check them for consistency (avoid errors with inconsistent appending),
    // and because one might set the environment variable before the first
    // Kvasir run that creates the file.  A user can suppress the duplicate
    // decls by specifying /dev/null as the .decls file.  -MDE
    // if (!actually_output_separate_decls_dtrace) {
    //   // We are appending and not printing out separate decls and dtrace files.
    //   // Do NOT print out decls again since we assume that our existing
    //   // dtrace file already has the decls info in it, and we don't want
    //   // to bloat the file size by repeating this information.
    //   print_declarations = 0;
    // }
    mode_str = "a";
  }
  else {
    mode_str = "w";
  }

  // If we're sending trace data to stdout, we definitely don't want the
  // program's output going to the same place.
  if (VG_STREQ(fname, "-") && !stdout_redir) {
      // But if we're debugging - we probably do.  (markro)
      if (!kvasir_print_debug_info) {
          stdout_redir = "/dev/tty";
      }    
  }

  if (kvasir_dtrace_gzip || VG_(getenv)("DTRACEGZIP")) {
    int fds[2]; /* fds[0] for reading (child), fds[1] for writing (parent) */
    vki_pid_t pid;
    int fd;
    int mode;
    char *new_fname = VG_(malloc)("kvasir_main.c: openDtrace.1", VG_(strlen)(fname) + 4);
    VG_(strcpy)(new_fname, fname);
    VG_(strcat)(new_fname, ".gz");

    if (VG_(pipe)(fds) < 0)
      return 0;

    if (!(dtrace_fp = fdopen(fds[1], "w")) || (pid = VG_(fork)()) < 0) {
      VG_(close)(fds[0]);
      VG_(close)(fds[1]);
      return 0;
    }

    if (!pid) {
      /* In child */
      const HChar *const argv[] = {"gzip", "-c", 0};
      VG_(close)(fds[1]);

      /* Redirect stdin from the pipe */
      VG_(close)(0);
      VG_(dup2)(fds[0], 0);
      VG_(close)(fds[0]);

      if (!VG_STREQ(fname, "-")) {
	SysRes sr;
	/* Redirect stdout to the dtrace.gz file */
	mode = VKI_O_CREAT | VKI_O_LARGEFILE | VKI_O_TRUNC |
	  (*mode_str == 'a' ? VKI_O_APPEND : VKI_O_WRONLY);
	sr = VG_(open)(new_fname, mode, 0666);
	if (sr_isError(sr)) {
	  printf( "Couldn't open %s for writing\n", fname);
	}
	fd = sr_Res(sr);
	VG_(close)(1);
	VG_(dup2)(fd, 1);
	VG_(close)(fd);
      }

      VG_(execv)("/bin/gzip", (void *)argv);
      VG_(exit)(127);
    }

    VG_(close)(fds[0]);
    VG_(fcntl)(fds[1], VKI_F_SETFD, VKI_FD_CLOEXEC);
    gzip_pid = pid;
  } else if VG_STREQ(fname, "-") {
    SysRes sr = VG_(dup)(1);
    int dtrace_fd = sr_Res(sr);
    /* Check sr.isError? */
    dtrace_fp = fdopen(dtrace_fd, mode_str);
    if (!dtrace_fp) {
      return 0;
    }
    // If we're debugging, turn off buffering to get coimmingled output.  (markro)
    if (kvasir_print_debug_info) {
      setNOBUF(dtrace_fp);
    }    
  } else {
    dtrace_fp = fopen(fname, mode_str);
    if (!dtrace_fp) {
      return 0;
    }
  }

  if (stdout_redir) {
    int new_stdout = openRedirectFile(stdout_redir);
    if (new_stdout == -1)
      return 0;
    VG_(close)(1);
    VG_(dup2)(new_stdout, 1);
    if (stderr_redir && VG_STREQ(stdout_redir, stderr_redir)) {
      /* If the same name was supplied for stdout and stderr, do the
	 equivalent of the shell's 2>&1, rather than having them overwrite
	 each other */
      VG_(close)(2);
      VG_(dup2)(new_stdout, 2);
      stderr_redir = 0;
    }
    VG_(close)(new_stdout);
  }

  if (stderr_redir) {
    int new_stderr = openRedirectFile(stderr_redir);
    if (new_stderr == -1)
      return 0;
    VG_(close)(2);
    VG_(dup2)(new_stderr, 2);
    VG_(close)(new_stderr);
  }

  return 1;
}

// Close the stream and finish writing the .dtrace file
// as well as all other open file streams
static void finishDtraceFile(void)
{
  if (dtrace_fp) /* If something goes wrong, we can be called with this null */
    fclose(dtrace_fp);
  if (gzip_pid) {
    int status;
    VG_(waitpid)(gzip_pid, &status, 0);
    /* Perhaps check return value? */
    gzip_pid = 0;
  }
}



void fjalar_tool_pre_clo_init(void)
{
  // Nothing to do here
}

// Initialize kvasir after processing command-line options
void fjalar_tool_post_clo_init(void)
{

  if (dyncomp_gc_after_n_tags == 0) {
      dyncomp_no_gc = True;
  }

  // If we're printing all trace info, we want
  // all debugging info also.
  if (dyncomp_print_trace_all) {
      dyncomp_print_debug_info = True;
      dyncomp_print_trace_info = True;
  }

  if (dyncomp_trace_startup) {
      dyncomp_delayed_trace = False;
      dyncomp_delayed_print_IR = False;
  }

  if (dyncomp_delayed_trace) {
      if (dyncomp_print_trace_info) {
          dyncomp_print_trace_info = False;
      } else {
          dyncomp_delayed_trace = False;
      }    
  }

  if (dyncomp_delayed_print_IR) {
      if (fjalar_print_IR) {
          fjalar_print_IR = False;
      } else {
          dyncomp_delayed_print_IR = False;
      }    
  }

  // Special-case .dtrace handling if kvasir_dtrace_filename ends in ".gz"
  if (kvasir_dtrace_filename) {
    int filename_len = VG_(strlen)(kvasir_dtrace_filename);
    if VG_STREQ(kvasir_dtrace_filename + filename_len - 3, ".gz") {
      DPRINTF("\nFilename ends in .gz\n");
      // Chop off '.gz' from the end of the filename
      ((HChar *)kvasir_dtrace_filename)[filename_len - 3] = '\0';
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

  // If we are only printing .dtrace and have --dtrace-no-decls,
  // then do not print out declarations
  if (!actually_output_separate_decls_dtrace && kvasir_dtrace_no_decls) {
     print_declarations = 0;
  }

  // Set fjalar_output_struct_vars to True for new .decls
  // format so that we can derive all possible variables.
  fjalar_output_struct_vars = True;

  createDeclsAndDtraceFiles(executable_filename);

  // Remember to not actually output the .decls right now when we're
  // running DynComp.  We need to wait until the end to actually
  // output .decls, but we need to make a fake run in order to set up
  // the proper data structures
  outputDeclsFile(kvasir_with_dyncomp);

  // if --decls-only PUNT now!
  if (kvasir_decls_only) {
    if (decls_fp) {
      fclose(decls_fp);
    }
    VG_(exit)(0);
  }

  // (comment added 2005)  
  // TODO: Re-factor this
  if (actually_output_separate_decls_dtrace && !dyncomp_without_dtrace) {
    openTheDtraceFile();
  }

  // RUDD TEMP - There's currently an issue with separate dtrace and
  // decls files if the decls file is 2.0. Jeff is working on a fix
  // for this but it can be circumvented temporarily by putting the
  // 2.0 decls header at the top of the dtrace.
  // Is this still an issue?  markro 08/10/16

  if (dtrace_fp && !kvasir_dtrace_append) {

      fputs("input-language C/C++\n", dtrace_fp);

      //Decls version
      fputs("decl-version 2.0\n", dtrace_fp);

      if (kvasir_with_dyncomp) {
        fputs("var-comparability implicit\n", dtrace_fp);
      }
      else {
        fputs("var-comparability none\n", dtrace_fp);
      }
      fputs("\n", dtrace_fp);
  }

}

void fjalar_tool_print_usage()
{
   printf("\n  User options for Kvasir and DynComp:\n");

   printf(
"\n  Output file format:\n"
"    --decls-file=<string>    The output .decls file location\n"
"                             (forces generation of separate .decls file)\n"
"    --decls-only             Exit after creating .decls file [--no-decls-only]\n"
"    --dtrace-file=<string>   The output .dtrace file location\n"
"                             [daikon-output/PROGRAM_NAME.dtrace]\n"
"    --dtrace-no-decls        Do not include declarations in .dtrace file\n"
"                             [--no-dtrace-no-decls]\n"
"    --dtrace-append          Appends .dtrace data to the end of an existing .dtrace file\n"
"                             [--no-dtrace-append]\n"
"    --dtrace-gzip            Compresses .dtrace data [--no-dtrace-gzip]\n"
"                             (Automatically ON if --dtrace-file string ends in '.gz')\n"
"    --object-ppts            Enables printing of object program points for structs and classes\n"
"    --output-fifo            Create output files as named pipes [--no-output-fifo]\n"
"    --program-stdout=<file>  Redirect instrumented program stdout to file\n"
"                             [Kvasir's stdout, or /dev/tty if --dtrace-file=-]\n"
"    --program-stderr=<file>  Redirect instrumented program stderr to file\n"

"\n  DynComp dynamic comparability analysis\n"
"    --dyncomp                Enables DynComp comparability analysis\n"
"                             [default on; turn off with --no-dyncomp]\n"
"    --dyncomp-gc-num-tags=<number>  The number of tags that get assigned between successive runs\n"
"                             of the garbage collector (between 0 and INT_MAX)\n"
"                             (The default is to garbage collect every 10,000,000 tags created)\n"
"                             0 is a special case that turns off the garbage collector.\n"
"                             (Faster but may run out of memory for long-running programs)\n"
"    --dyncomp-approximate-literals  Approximates the handling of literals for comparability.\n"
"                                    (Loses some precision but faster and takes less memory)\n"
"    --dyncomp-detailed-mode  Uses an O(n^2) space/time algorithm for determining\n"
"                             variable comparability, which is potentially more precise\n"
"                             but takes up more resources than the O(n) default algorithm\n"
"    --dyncomp-separate-entry-exit  Allows variables to have distinct comparability\n"
"                                   numbers at function entrance/exit when run with\n"
"                                   DynComp.  This provides more accuracy, but may\n"
"                                   sometimes lead to output that Daikon cannot accept.\n"
"    --dyncomp-interactions=all          Counts all binary operations as interactions (default)\n"
"    --dyncomp-interactions=units        Only counts interactions that are consistent with units\n"
"    --dyncomp-interactions=comparisons  Only counts comparison operations as interactions\n"
"    --dyncomp-interactions=none         Tracks no interactions, just dataflow\n"
"\n  Debugging:\n"
"    --kvasir-debug           Print Kvasir-internal debug messages [--no-debug]\n"
"    --dyncomp-debug          Print DynComp debug messages (--dyncomp must also be on)\n"
"                             [--no-dyncomp-debug]\n"
"    --dyncomp-trace-merge    Similar, but more detailed\n"
"                             [--no-dyncomp-trace-merge]\n"
"    --dyncomp-trace          Similar, but very detailed\n"
"                             [--no-dyncomp-trace]\n"
"    --dyncomp-trace-startup  Trace all executed code\n"
"                             [default is don't start trace until 'main']\n"
"    --dyncomp-print-inc      Print DynComp comp. numbers at the execution of every program\n"
"                             point - requires separate dtrace file (for debug only)\n"
"\n"
   );
}

// Processes command-line options
Bool fjalar_tool_process_cmd_line_option(const HChar* arg)
{
  if VG_STR_CLO(arg, "--decls-file", kvasir_decls_filename) {}
  else if VG_STR_CLO(arg, "--dtrace-file", kvasir_dtrace_filename) {}
  else if VG_YESNO_CLO(arg, "dtrace-append",    kvasir_dtrace_append) {}
  else if VG_YESNO_CLO(arg, "object-ppts",      kvasir_object_ppts) {}
  else if VG_YESNO_CLO(arg, "dtrace-no-decls",  kvasir_dtrace_no_decls) {}
  else if VG_YESNO_CLO(arg, "dtrace-gzip",      kvasir_dtrace_gzip) {}
  else if VG_YESNO_CLO(arg, "output-fifo",      kvasir_output_fifo) {}
  else if VG_YESNO_CLO(arg, "decls-only",       kvasir_decls_only) {}
  else if VG_YESNO_CLO(arg, "kvasir-debug",     kvasir_print_debug_info) {}
  else if VG_STR_CLO(arg, "--program-stdout",   kvasir_program_stdout_filename){}
  else if VG_STR_CLO(arg, "--program-stderr",   kvasir_program_stderr_filename){}
  else if VG_YESNO_CLO(arg, "dyncomp",          kvasir_with_dyncomp) {}
  else if VG_YESNO_CLO(arg, "dyncomp-approximate-literals", dyncomp_approximate_literals) {}
  else if VG_YESNO_CLO(arg, "dyncomp-detailed-mode", dyncomp_detailed_mode) {}
  else if VG_BINT_CLO(arg, "--dyncomp-gc-num-tags", dyncomp_gc_after_n_tags,
                      0, 0x7fffffff) {}
  else if VG_XACT_CLO(arg, "--dyncomp-interactions=none",
                      dyncomp_dataflow_only_mode,        True) {}
  else if VG_XACT_CLO(arg, "--dyncomp-interactions=comparisons",
                      dyncomp_dataflow_comparisons_mode, True) {}
  else if VG_XACT_CLO(arg, "--dyncomp-interactions=units",
                      dyncomp_units_mode,                True) {}
  else if VG_XACT_CLO(arg, "--dyncomp-interactions=all",
                      dyncomp_dataflow_only_mode,        False) {
                      dyncomp_dataflow_comparisons_mode = dyncomp_units_mode = False; }
  else if VG_YESNO_CLO(arg, "dyncomp-debug",  dyncomp_print_debug_info) {}
  else if VG_YESNO_CLO(arg, "dyncomp-trace",  dyncomp_print_trace_all) {}
  else if VG_YESNO_CLO(arg, "dyncomp-trace-merge",  dyncomp_print_trace_info) {}
  else if VG_YESNO_CLO(arg, "dyncomp-print-inc",  dyncomp_print_incremental) {}
  else if VG_YESNO_CLO(arg, "dyncomp-separate-entry-exit",
                       dyncomp_separate_entry_exit) {}
  else if VG_YESNO_CLO(arg, "dyncomp-trace-startup", dyncomp_trace_startup) {}
  else
    return False;   // If no options match, return False so that an error
                    // message can be reported by the Valgrind core.

  // Return True if at least one option has been matched to indicate success:
  return True;
}

/* Do initializion-like tasks that we'd like to postpone until near
   the end of program startup (right before main()). For instance,
   anything that depends on shared libraries having been loaded. */
static void kvasir_late_init(void) {
  // RUDD - reimplement
/*   if (kvasir_with_dyncomp) { */
/*     const DebugInfo *si; */
/*     for (si = VG_(next_seginfo)(0); si; si =  VG_(next_seginfo)(si)) { */
/*       Addr got_addr = VG_(seginfo_sect_start)(si, Vg_SectGOT); */
/*       SizeT got_size = VG_(seginfo_sect_size)(si, Vg_SectGOT); */
/*       if (got_size) { */
/*         set_tag_for_GOT(got_addr, got_size); */
/*       } */
/*     } */
/*   } */
}

void fjalar_tool_finish() {
  if (kvasir_with_dyncomp) {

    extern char dyncomp_profile_tags;
    extern UInt numConsts;
    extern UInt mergeTagsCount;
    extern UInt merge3TagsCount;
    extern UInt merge4TagsCount;
    extern UInt mergeTagsReturn0Count;

    // Do one extra propagation of variable comparability at the end
    // of execution once all of the value comparability sets have
    // been properly updated:
    DC_extra_propagate_val_to_var_sets();

    // Now print out the .decls file at the very end of execution:
    DC_outputDeclsAtEnd();

    if (dyncomp_profile_tags) {
      printf("num. static consts in bin/tri/quad ops = %u\n", numConsts);
      printf("MERGE_TAGS calls = %u\n", mergeTagsCount);
      printf("MERGE_3_TAGS calls = %u\n", merge3TagsCount);
      printf("MERGE_4_TAGS calls = %u\n", merge4TagsCount);
      printf("MERGE_TAGS_RETURN_0 calls = %u\n", mergeTagsReturn0Count);
      printf("next tag = %u, total assigned = %u\n", nextTag, totalNumTagsAssigned);
    }

  }

  if (!dyncomp_without_dtrace) {
     finishDtraceFile();
  }
}

Bool kvasir_late_init_done = False;

void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state) {
  if (!kvasir_late_init_done) {
    kvasir_late_init();
    kvasir_late_init_done = True;
  }
  printDtraceForFunction(f_state, 1);
}

void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state) {

  if (kvasir_with_dyncomp) {
    ThreadId currentTID = VG_(get_running_tid)();

    // For DynComp, update tags of saved register values
    int i;

    UInt xAXtag = 0;
    UInt xDXtag = 0;
    UInt FPUtag = 0;

    xAXtag = VG_(get_xAX_tag)(currentTID);
    xDXtag = VG_(get_xDX_tag)(currentTID);
#if defined(VGA_amd64)
    FPUtag = VG_(get_XMM_N_tag)(currentTID, 0);
#else
    FPUtag = VG_(get_FPU_stack_top_tag)(currentTID);
#endif

    for (i = 0; i < sizeof(UWord); i++) {
      set_tag((Addr)(&(f_state->xAX)) + (Addr)i, xAXtag);
      set_tag((Addr)(&(f_state->xDX)) + (Addr)i, xDXtag);
      set_tag((Addr)(&(f_state->FPU)) + (Addr)i, FPUtag);
    }

    for (i = 4; i < 8; i++) {
      set_tag((Addr)(&(f_state->FPU)) + (Addr)i, FPUtag);
    }
  }

  printDtraceForFunction(f_state, 0);
}



// Constructors and destructors for classes that can be sub-classed:

// Default constructor that should return a particular sub-class of an
// object.  This should call VG_(calloc) the proper amount of space
// for the object and initialize it with whatever initial state is
// necessary.
VariableEntry* constructVariableEntry() {
  return (VariableEntry*)(VG_(calloc)("kvasir_main.c: constructVariableEntry", 1, sizeof(VariableEntry)));
}

TypeEntry* constructTypeEntry() {
  return (TypeEntry*)(VG_(calloc)("kvasir_main.c: constructTypeEntry", 1, sizeof(TypeEntry)));
}

// Remember that we have sub-classed FunctionEntry with
// DaikonFunctionEntry:
FunctionEntry* constructFunctionEntry() {
  return (FunctionEntry*)(VG_(calloc)("kvasir_main.c: constructFunctioneEntry", 1, sizeof(DaikonFunctionEntry)));
}

// Destructors that should clean-up and then call VG_(free) on the
// respective entries.
//
// (comment added 2006)  
// TODO: These currently cause memory leaks because these classes have
// pointer fields that refer to dynamically-allocated memory ...
void destroyVariableEntry(VariableEntry* v) {
  VG_(free)(v);
}

void destroyTypeEntry(TypeEntry* t) {
  VG_(free)(t);
}

// Remember that we have sub-classed FunctionEntry with
// DaikonFunctionEntry:
void destroyFunctionEntry(FunctionEntry* f) {
  VG_(free)((DaikonFunctionEntry*)f);
}
