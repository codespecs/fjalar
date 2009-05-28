
/*--------------------------------------------------------------------*/
/*--- Command line options.                     pub_tool_options.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2009 Julian Seward
      jseward@acm.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#ifndef __PUB_TOOL_OPTIONS_H
#define __PUB_TOOL_OPTIONS_H

#include "libvex.h"              // for VexControl


// Higher-level command-line option recognisers;  use in if/else chains. 
// Note that they assign a value to the 'qq_var' argument.  So often they
// can be used like this:
//
//   if VG_STR_CLO(arg, "--foo", clo_foo) { }
//
// But if you want to do further checking or processing, you can do this:
//
//   if VG_STR_CLO(arg, "--foo", clo_foo) { <further checking or processing> }
//
// They use GNU statement expressions to do the qq_var assignment within a
// conditional expression.

// String argument, eg. --foo=yes or --foo=no
#define VG_BOOL_CLO(qq_arg, qq_option, qq_var) \
   (VG_STREQN(VG_(strlen)(qq_option)+1, qq_arg, qq_option"=") && \
    ({ \
      Char* val = &(qq_arg)[ VG_(strlen)(qq_option)+1 ]; \
      if      VG_STREQ(val, "yes") (qq_var) = True; \
      else if VG_STREQ(val, "no")  (qq_var) = False; \
      True; \
    }) \
   )

// String argument, eg. --foo=bar
#define VG_STR_CLO(qq_arg, qq_option, qq_var) \
   (VG_STREQN(VG_(strlen)(qq_option)+1, qq_arg, qq_option"=") && \
    ({ \
      Char* val = &(qq_arg)[ VG_(strlen)(qq_option)+1 ]; \
      (qq_var) = val; \
      True; \
    }) \
   )

// Unbounded integer arg, eg. --foo=10
#define VG_INT_CLO(qq_arg, qq_option, qq_var) \
   (VG_STREQN(VG_(strlen)(qq_option)+1, qq_arg, qq_option"=") && \
    ({ \
      Char* val = &(qq_arg)[ VG_(strlen)(qq_option)+1 ]; \
      Char* s; \
      Long n = VG_(strtoll10)( val, &s ); \
      (qq_var) = n; \
      /* Check for non-numeralness, or overflow. */ \
      if ('\0' != s[0] || (qq_var) != n) VG_(err_bad_option)(qq_arg); \
      True; \
     }) \
    )

// Bounded integer arg, eg. --foo=10 ;  if the value exceeds the bounds it
// causes an abort.  'qq_base' can be 10 or 16.
#define VG_BINTN_CLO(qq_base, qq_arg, qq_option, qq_var, qq_lo, qq_hi) \
   (VG_STREQN(VG_(strlen)(qq_option)+1, qq_arg, qq_option"=") && \
    ({ \
      Char* val = &(qq_arg)[ VG_(strlen)(qq_option)+1 ]; \
      Char* s; \
      Long n = VG_(strtoll##qq_base)( val, &s ); \
      (qq_var) = n; \
      /* Check for non-numeralness, or overflow. */ \
      /* Nb: it will overflow if qq_var is unsigned and qq_val is negative! */ \
      if ('\0' != s[0] || (qq_var) != n) VG_(err_bad_option)(qq_arg); \
      /* Check bounds. */ \
      if ((qq_var) < (qq_lo) || (qq_var) > (qq_hi)) { \
         VG_(message)(Vg_UserMsg, \
                      "'%s' argument must be between %lld and %lld", \
                      (qq_option), (Long)(qq_lo), (Long)(qq_hi)); \
         VG_(err_bad_option)(qq_arg); \
      } \
      True; \
     }) \
    )

// Bounded decimal integer arg, eg. --foo=100
#define VG_BINT_CLO(qq_arg, qq_option, qq_var, qq_lo, qq_hi) \
   VG_BINTN_CLO(10, (qq_arg), qq_option, (qq_var), (qq_lo), (qq_hi))

// Bounded hexadecimal integer arg, eg. --foo=0x1fa8
#define VG_BHEX_CLO(qq_arg, qq_option, qq_var, qq_lo, qq_hi) \
   VG_BINTN_CLO(16, (qq_arg), qq_option, (qq_var), (qq_lo), (qq_hi))

// Double (decimal) arg, eg. --foo=4.6
// XXX: there's not VG_BDBL_CLO because we don't have a good way of printing
// floats at the moment!
#define VG_DBL_CLO(qq_arg, qq_option, qq_var) \
   (VG_STREQN(VG_(strlen)(qq_option)+1, qq_arg, qq_option"=") && \
    ({ \
      Char* val = &(qq_arg)[ VG_(strlen)(qq_option)+1 ]; \
      Char* s; \
      double n = VG_(strtod)( val, &s ); \
      (qq_var) = n; \
      /* Check for non-numeralness */ \
      if ('\0' != s[0]) VG_(err_bad_option)(qq_arg); \
      True; \
     }) \
    )

// Arg whose value is denoted by the exact presence of the given string;
// if it matches, qq_var is assigned the value in qq_val.
#define VG_XACT_CLO(qq_arg, qq_option, qq_var, qq_val) \
   (VG_STREQ((qq_arg), (qq_option)) && \
    ({ \
      (qq_var) = (qq_val); \
      True; \
    }) \
   )

/* Verbosity level: 0 = silent, 1 (default), > 1 = more verbose. */
extern Int  VG_(clo_verbosity);

/* Emit all messages as XML? default: NO */
/* If clo_xml is set, various other options are set in a non-default
   way.  See vg_main.c and mc_main.c. */
extern Bool VG_(clo_xml);

/* An arbitrary user-supplied string which is copied into the
   XML output, in between <usercomment> tags. */
extern HChar* VG_(clo_xml_user_comment);

/* Vex iropt control.  Tool-visible so tools can make Vex optimise
   less aggressively if that is needed (callgrind needs this). */
extern VexControl VG_(clo_vex_control);

/* Number of parents of a backtrace.  Default: 8.  */
extern Int   VG_(clo_backtrace_size);

/* Continue stack traces below main()?  Default: NO */
extern Bool VG_(clo_show_below_main);


/* Call this if a recognised option was bad for some reason.  Note:
   don't use it just because an option was unrecognised -- return
   'False' from VG_(tdict).tool_process_cmd_line_option) to indicate that --
   use it if eg. an option was given an inappropriate argument.
   This function prints an error message, then shuts down the entire system.
   It returns a Bool so it can be used in the _CLO_ macros. */
__attribute__((noreturn))
extern void VG_(err_bad_option) ( Char* opt );

/* Used to expand file names.  "option_name" is the option name, eg.
   "--log-file".  'format' is what follows, eg. "cachegrind.out.%p".  In
   'format': 
   - "%p" is replaced with PID.
   - "%q{QUAL}" is replaced with the environment variable $QUAL.  If $QUAL
     isn't set, we abort.  If the "{QUAL}" part is malformed, we abort.
   - "%%" is replaced with "%".
   Anything else after '%' causes an abort.
   If the format specifies a relative file name, it's put in the program's
   initial working directory.  If it specifies an absolute file name (ie.
   starts with '/') then it is put there.

   Note that "option_name" has no effect on the returned string: the
   returned string depends only on "format" and the PIDs and
   environment variables that it references (if any). "option_name" is
   merely used in printing error messages, if an error message needs
   to be printed due to malformedness of the "format" argument.
*/
extern Char* VG_(expand_file_name)(Char* option_name, Char* format);

#endif   // __PUB_TOOL_OPTIONS_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
