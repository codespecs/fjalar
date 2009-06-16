
/*--------------------------------------------------------------------*/
/*--- Command line options.                                        ---*/
/*---                                                  m_options.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2009 Nicholas Nethercote
      njn@valgrind.org

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

#include "pub_core_basics.h"
#include "pub_core_vki.h"
#include "pub_core_options.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcbase.h"
#include "pub_core_libcfile.h"
#include "pub_core_libcprint.h"
#include "pub_core_libcproc.h"
#include "pub_core_mallocfree.h"

// See pub_{core,tool}_options.h for explanations of all these.


/* Define, and set defaults. */
VexControl VG_(clo_vex_control);
Bool   VG_(clo_error_limit)    = True;
Int    VG_(clo_error_exitcode) = 0;
Bool   VG_(clo_db_attach)      = False;
Char*  VG_(clo_db_command)     = GDB_PATH " -nw %f %p";
Int    VG_(clo_gen_suppressions) = 0;
Int    VG_(clo_sanity_level)   = 1;
Int    VG_(clo_verbosity)      = 1;
Bool   VG_(clo_xml)            = False;
HChar* VG_(clo_xml_user_comment) = NULL;
Bool   VG_(clo_demangle)       = True;
Bool   VG_(clo_trace_children) = False;
Bool   VG_(clo_child_silent_after_fork) = False;
Int    VG_(clo_log_fd)         = 2; /* must be signed, as -1 is possible. */
Char*  VG_(clo_log_name)       = NULL;
Bool   VG_(clo_time_stamp)     = False;
Int    VG_(clo_input_fd)       = 0; /* stdin */
Int    VG_(clo_n_suppressions) = 0;
Char*  VG_(clo_suppressions)[VG_CLO_MAX_SFILES];
UChar  VG_(clo_trace_flags)    = 0; // 00000000b
UChar  VG_(clo_profile_flags)  = 0; // 00000000b
Int    VG_(clo_trace_notbelow) = 999999999;
Bool   VG_(clo_trace_syscalls) = False;
Bool   VG_(clo_trace_signals)  = False;
Bool   VG_(clo_trace_symtab)   = False;
HChar* VG_(clo_trace_symtab_patt) = "*";
Bool   VG_(clo_trace_cfi)      = False;
Bool   VG_(clo_debug_dump_syms) = False;
Bool   VG_(clo_debug_dump_line) = False;
Bool   VG_(clo_debug_dump_frames) = False;
Bool   VG_(clo_trace_redir)    = False;
Bool   VG_(clo_trace_sched)    = False;
Bool   VG_(clo_profile_heap)   = False;
Int    VG_(clo_dump_error)     = 0;
Int    VG_(clo_backtrace_size) = 12;
Char*  VG_(clo_sim_hints)      = NULL;
Bool   VG_(clo_sym_offsets)    = False;
Bool   VG_(clo_read_var_info)  = False;
Bool   VG_(clo_run_libc_freeres) = True;
Bool   VG_(clo_track_fds)      = False;
Bool   VG_(clo_show_below_main)= False;
Bool   VG_(clo_show_emwarns)   = False;
Word   VG_(clo_max_stackframe) = 2000000;
Word   VG_(clo_main_stacksize) = 0; /* use client's rlimit.stack */
Bool   VG_(clo_wait_for_gdb)   = False;
VgSmc  VG_(clo_smc_check)      = Vg_SmcStack;
HChar* VG_(clo_kernel_variant) = NULL;
Bool   VG_(clo_auto_run_dsymutil) = False;


/*====================================================================*/
/*=== Command line errors                                          ===*/
/*====================================================================*/

static void revert_to_stderr ( void )
{
   vg_assert( !VG_(logging_to_socket) );
   VG_(clo_log_fd) = 2; /* stderr */
}

__attribute__((noreturn))
void VG_(err_bad_option) ( Char* opt )
{
   revert_to_stderr();
   VG_(printf)("valgrind: Bad option '%s'; aborting.\n", opt);
   VG_(printf)("valgrind: Use --help for more information.\n");
   VG_(exit)(1);
}

__attribute__((noreturn))
void VG_(err_missing_prog) ( void  )
{
   revert_to_stderr();
   VG_(printf)("valgrind: no program specified\n");
   VG_(printf)("valgrind: Use --help for more information.\n");
   VG_(exit)(1);
}

__attribute__((noreturn))
void VG_(err_config_error) ( Char* msg )
{
   revert_to_stderr();
   VG_(printf)("valgrind: Startup or configuration error:\n   %s\n", msg);
   VG_(printf)("valgrind: Unable to start up properly.  Giving up.\n");
   VG_(exit)(1);
}

// Copies the string, prepending it with the startup working directory, and
// expanding %p and %q entries.  Returns a new, malloc'd string.
Char* VG_(expand_file_name)(Char* option_name, Char* format)
{
   static Char base_dir[VKI_PATH_MAX];
   Int len, i = 0, j = 0;
   Char* out;

   Bool ok = VG_(get_startup_wd)(base_dir, VKI_PATH_MAX);
   tl_assert(ok);

   if (VG_STREQ(format, "")) {
      // Empty name, bad.
      VG_UMSG("%s: filename is empty", option_name);
      goto bad;
   }
   
   // If 'format' starts with a '~', abort -- the user probably expected the
   // shell to expand but it didn't (see bug 195268 for details).  This means
   // that we don't allow a legitimate filename beginning with '~' but that
   // seems very unlikely.
   if (format[0] == '~') {
      VG_UMSG("%s: filename begins with '~'", option_name);
      VG_UMSG("You probably expected the shell to expand the '~', but it");
      VG_UMSG("didn't.  The rules for '~'-expansion vary from shell to shell.");
      VG_UMSG("You might have more luck using $HOME instead.");
      goto bad;
   }

   // If 'format' starts with a '/', do not prefix with startup dir.
   if (format[0] != '/') {
      j += VG_(strlen)(base_dir);
   }

   // The 10 is slop, it should be enough in most cases.
   len = j + VG_(strlen)(format) + 10;
   out = VG_(malloc)( "options.efn.1", len );
   if (format[0] != '/') {
      VG_(strcpy)(out, base_dir);
      out[j++] = '/';
   }

#define ENSURE_THIS_MUCH_SPACE(x) \
   if (j + x >= len) { \
      len += (10 + x); \
      out = VG_(realloc)("options.efn.2(multiple)", out, len); \
   }

   while (format[i]) {
      if (format[i] != '%') {
         ENSURE_THIS_MUCH_SPACE(1);
         out[j++] = format[i++];
         
      } else {
         // We saw a '%'.  What's next...
         i++;
         if      ('%' == format[i]) {
            // Replace '%%' with '%'.
            ENSURE_THIS_MUCH_SPACE(1);
            out[j++] = format[i++];
         }
         else if ('p' == format[i]) {
            // Print the PID.  Assume that it's not longer than 10 chars --
            // reasonable since 'pid' is an Int (ie. 32 bits).
            Int pid = VG_(getpid)();
            ENSURE_THIS_MUCH_SPACE(10);
            j += VG_(sprintf)(&out[j], "%d", pid);
            i++;
         } 
         else if ('q' == format[i]) {
            i++;
            if ('{' == format[i]) {
               // Get the env var name, print its contents.
               Char* qualname;
               Char* qual;
               i++;
               qualname = &format[i];
               while (True) {
                  if (0 == format[i]) {
                     VG_(message)(Vg_UserMsg, "%s: malformed %%q specifier",
                        option_name);
                     goto bad;
                  } else if ('}' == format[i]) {
                     // Temporarily replace the '}' with NUL to extract var
                     // name.
                     format[i] = 0;
                     qual = VG_(getenv)(qualname);
                     if (NULL == qual) {
                        VG_(message)(Vg_UserMsg,
                           "%s: environment variable %s is not set",
                           option_name, qualname);
                        format[i] = '}';  // Put the '}' back.
                        goto bad;
                     }
                     format[i] = '}';     // Put the '}' back.
                     i++;
                     break;
                  }
                  i++;
               }
               ENSURE_THIS_MUCH_SPACE(VG_(strlen)(qual));
               j += VG_(sprintf)(&out[j], "%s", qual);
            } else {
               VG_(message)(Vg_UserMsg,
                  "%s: expected '{' after '%%q'", option_name);
               goto bad;
            }
         } 
         else {
            // Something else, abort.
            VG_(message)(Vg_UserMsg,
               "%s: expected 'p' or 'q' or '%%' after '%%'", option_name);
            goto bad;
         }
      }
   }
   ENSURE_THIS_MUCH_SPACE(1);
   out[j++] = 0;

   return out;

  bad: {
   Char* opt =    // 2:  1 for the '=', 1 for the NUL.
      VG_(malloc)( "options.efn.3",
                   VG_(strlen)(option_name) + VG_(strlen)(format) + 2 );
   VG_(strcpy)(opt, option_name);
   VG_(strcat)(opt, "=");
   VG_(strcat)(opt, format);
   VG_(err_bad_option)(opt);
  }
}



/*--------------------------------------------------------------------*/
/*--- end                                              m_options.c ---*/
/*--------------------------------------------------------------------*/
