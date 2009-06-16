
/*--------------------------------------------------------------------*/
/*--- Redirections, etc.                          pub_tool_redir.h ---*/
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

#ifndef __PUB_TOOL_REDIR_H
#define __PUB_TOOL_REDIR_H

/* The following macros facilitate function replacement and wrapping.

   Function wrapping and function replacement are similar but not
   identical.

   A replacement for some function F simply diverts all calls to F
   to the stated replacement.  There is no way to get back to F itself
   from the replacement.

   A wrapper for a function F causes all calls to F to instead go to
   the wrapper.  However, from inside the wrapper, it is possible
   (with some difficulty) to get to F itself.

   You may notice that replacement is a special case of wrapping, in
   which the call to the original is omitted.  For implementation
   reasons, though, it is important to use the following macros
   correctly: in particular, if you want to write a replacement, make
   sure you use the VG_REPLACE_FN_ macros and not the VG_WRAP_FN_
   macros.

   Replacement
   ~~~~~~~~~~~
   To write a replacement function, do this:

      ret_type 
      VG_REPLACE_FUNCTION_ZU(zEncodedSoname,fnname) ( .. args .. )
      {
         ... body ...
      }

   zEncodedSoname should be a Z-encoded soname (see below for Z-encoding
   details) and fnname should be an unencoded fn name.  The resulting name is

      _vgrZU_zEncodedSoname_fnname

   The "_vgrZU_" is a prefix that gets discarded upon decoding.

   It is also possible to write

      ret_type 
      VG_REPLACE_FUNCTION_ZZ(zEncodedSoname,zEncodedFnname) ( .. args .. )
      {
         ... body ...
      }
   
   which means precisely the same, but the function name is also
   Z-encoded.  This can sometimes be necessary.  In this case the
   resulting function name is

      _vgrZZ_zEncodedSoname_zEncodedFnname

   When it sees this either such name, the core's symbol-table reading
   machinery and redirection machinery first Z-decode the soname and 
   if necessary the fnname.  They are encoded so that they may include
   arbitrary characters, and in particular they may contain '*', which
   acts as a wildcard.

   They then will conspire to cause calls to any function matching
   'fnname' in any object whose soname matches 'soname' to actually be
   routed to this function.  This is used in Valgrind to define dozens
   of replacements of malloc, free, etc.

   The soname must be a Z-encoded bit of text because sonames can
   contain dots etc which are not valid symbol names.  The function
   name may or may not be Z-encoded: to include wildcards it has to be,
   but Z-encoding C++ function names which are themselves already mangled
   using Zs in some way is tedious and error prone, so the _ZU variant
   allows them not to be Z-encoded.

   Note that the soname "NONE" is specially interpreted to match any
   shared object which doesn't have a soname.

   Note also that the replacement function should probably (must be?) in
   client space, so it runs on the simulated CPU.  So it must be in
   either vgpreload_<tool>.so or vgpreload_core.so.  It also only works
   with functions in shared objects, I think.
   
   It is important that the Z-encoded names contain no unencoded
   underscores, since the intercept-handlers in m_redir.c detect the
   end of the soname by looking for the first trailing underscore.

   Wrapping
   ~~~~~~~~
   This is identical to replacement, except that you should use the
   macro names

      VG_WRAP_FUNCTION_ZU
      VG_WRAP_FUNCTION_ZZ

   instead.

   Z-encoding
   ~~~~~~~~~~
   Z-encoding details: the scheme is like GHC's.  It is just about
   readable enough to make a preprocessor unnecessary.  First the
   "_vgrZU_" or "_vgrZZ_" prefix is added, and then the following
   characters are transformed.

     *         -->  Za    (asterisk)
     +         -->  Zp    (plus)
     :         -->  Zc    (colon)
     .         -->  Zd    (dot)
     _         -->  Zu    (underscore)
     -         -->  Zh    (hyphen)
     (space)   -->  Zs    (space)
     @         -->  ZA    (at)
     Z         -->  ZZ    (Z)
     (         -->  ZL    (left)
     )         -->  ZR    (right)

   Everything else is left unchanged.
*/

/* If you change these, the code in VG_(maybe_Z_demangle) needs to be
   changed accordingly.  NOTE: duplicates
   I_{WRAP,REPLACE}_SONAME_FNNAME_Z{U,Z} in valgrind.h. */

/* Use an extra level of macroisation so as to ensure the soname/fnname
   args are fully macro-expanded before pasting them together. */
#define VG_CONCAT4(_aa,_bb,_cc,_dd) _aa##_bb##_cc##_dd

#define VG_REPLACE_FUNCTION_ZU(soname,fnname) VG_CONCAT4(_vgrZU_,soname,_,fnname)
#define VG_REPLACE_FUNCTION_ZZ(soname,fnname) VG_CONCAT4(_vgrZZ_,soname,_,fnname)

#define VG_WRAP_FUNCTION_ZU(soname,fnname) VG_CONCAT4(_vgwZU_,soname,_,fnname)
#define VG_WRAP_FUNCTION_ZZ(soname,fnname) VG_CONCAT4(_vgwZZ_,soname,_,fnname)

/* --------- Some handy Z-encoded names. --------- */

// Nb: ALL THESE NAMES MUST BEGIN WITH "VG_Z_".  Why?  If we applied
// conditional compilation inconsistently we could accidentally use an
// undefined constant like VG_Z_LIBC_DOT_A, resulting in a bogus Z-encoded
// name like "_vgrZU_VG_Z_LIBC_DOT_A_foo".  This can't be detected at
// compile-time, because both the constant's name and its value are
// identifiers.  However, by always using "VG_Z_" as a prefix, we can do a
// run-time check and abort if any name has "VG_Z_" in it, because that
// indicates that the constant has been used without being defined.

/* --- Soname of the standard C library. --- */

#if defined(VGO_linux)
#  define  VG_Z_LIBC_SONAME  libcZdsoZa              // libc.so*
#elif defined(VGP_ppc32_aix5)
   /* AIX has both /usr/lib/libc.a and /usr/lib/libc_r.a. */
#  define  VG_Z_LIBC_SONAME  libcZaZdaZLshrZdoZR     // libc*.a(shr.o)
#elif defined(VGP_ppc64_aix5)
#  define  VG_Z_LIBC_SONAME  libcZaZdaZLshrZu64ZdoZR // libc*.a(shr_64.o)
#elif defined(VGO_darwin)
#  define  VG_Z_LIBC_SONAME  libSystemZdZaZddylib    // libSystem.*.dylib
#else
#  error "Unknown platform"
#endif

/* --- Soname of the GNU C++ library. --- */

// Valid on all platforms(?)
#define  VG_Z_LIBSTDCXX_SONAME  libstdcZpZpZa           // libstdc++*

/* --- Soname of XLC's C++ library. --- */

/* AIX: xlC's C++ runtime library is called libC.a, and the
   interesting symbols appear to be in ansicore_32.o or ansicore_64.o
   respectively. */
#if defined(VGP_ppc32_aix5)
#  define  VG_Z_LIBC_DOT_A   libCZdaZLansicoreZu32ZdoZR // libC.a(ansicore_32.o)
#elif defined(VGP_ppc64_aix5)
#  define  VG_Z_LIBC_DOT_A   libCZdaZLansicoreZu64ZdoZR // libC.a(ansicore_64.o)
#endif

/* --- Soname of the pthreads library. --- */

#if defined(VGO_linux) || defined(VGO_aix5)
#  define  VG_Z_LIBPTHREAD_SONAME  libpthreadZdsoZd0     // libpthread.so.0
#elif defined(VGO_darwin)
#  define  VG_Z_LIBPTHREAD_SONAME  libSystemZdZaZddylib  // libSystem.*.dylib
#else
#  error "Unknown platform"
#endif

/* --- Sonames for Linux ELF linkers. --- */

#if defined(VGO_linux)
#define  VG_Z_LD_LINUX_SO_2         ldZhlinuxZdsoZd2           // ld-linux.so.2
#define  VG_Z_LD_LINUX_X86_64_SO_2  ldZhlinuxZhx86Zh64ZdsoZd2  // ld-linux-x86-64.so.2
#define  VG_Z_LD64_SO_1             ld64ZdsoZd1                // ld64.so.1
#define  VG_Z_LD_SO_1               ldZdsoZd1                  // ld.so.1
#endif

/* --- Executable name for Darwin Mach-O linker. --- */

#if defined(VGO_darwin)
#define  VG_Z_DYLD               dyld                       // dyld
#endif


#endif   // __PUB_TOOL_REDIR_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
