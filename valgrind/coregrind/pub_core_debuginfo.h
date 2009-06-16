
/*--------------------------------------------------------------------*/
/*--- Debug info.                             pub_core_debuginfo.h ---*/
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

#ifndef __PUB_CORE_DEBUGINFO_H
#define __PUB_CORE_DEBUGINFO_H

//--------------------------------------------------------------------
// PURPOSE: This module deals with reading debug info and symbol tables
// to get file and function names, line numbers, variable types, and
// to help stack unwinding.
//--------------------------------------------------------------------

#include "pub_tool_debuginfo.h"

/* Initialise the entire module.  Must be called first of all. */
extern void VG_(di_initialise) ( void );

/* LINUX: Notify the debuginfo system about a new mapping, or the
   disappearance of such, or a permissions change on an existing
   mapping.  This is the way new debug information gets loaded.  If
   allow_SkFileV is True, it will try load debug info if the mapping
   at 'a' belongs to Valgrind; whereas normally (False) it will not do
   that.  This allows us to carefully control when the thing will read
   symbols from the Valgrind executable itself.

   If a call to VG_(di_notify_mmap) causes debug info to be read, then
   the returned ULong is an abstract handle which can later be used to
   refer to the debuginfo read as a result of this specific mapping,
   in later queries to m_debuginfo.  In this case the handle value
   will be one or above.  If the returned value is zero, no debug info
   was read. */
#if defined(VGO_linux)  ||  defined(VGO_darwin)
extern ULong VG_(di_notify_mmap)( Addr a, Bool allow_SkFileV );

extern void VG_(di_notify_munmap)( Addr a, SizeT len );

extern void VG_(di_notify_mprotect)( Addr a, SizeT len, UInt prot );

/* this should really return ULong, as per VG_(di_notify_mmap). */
extern void VG_(di_notify_pdb_debuginfo)( Int fd, Addr avma,
                                          SizeT total_size,
                                          PtrdiffT unknown_purpose__reloc );
#endif

#if defined(VGO_aix5)
// GrP fixme use this instead for darwin?
/* AIX5: Very similar, except packaged more neatly.  The supplied
   parameters describe a code segment and its associated data segment,
   that have recently been mapped in -- so we need to read debug info
   for it -- or conversely, have recently been dumped, in which case
   the relevant debug info has to be unloaded.

   The returned ULong has the same meaning as documented for
   VG_(di_notify_mmap) just above. */
extern ULong VG_(di_aix5_notify_segchange)( 
                Addr   code_start,
                Word   code_len,
                Addr   data_start,
                Word   data_len,
                UChar* file_name,
                UChar* mem_name,
                Bool   is_mainexe,
                Bool   acquire
             );
#endif

extern void VG_(di_discard_ALL_debuginfo)( void );

/* Like VG_(get_fnname), but it does not do C++ demangling nor Z-demangling
 * nor below-main renaming.
 * It should not be used for any names that will be shown to users.
 * It should only be used in cases where the names of interest will have
 * particular (ie. non-mangled) forms, or the mangled form is acceptable. */
extern
Bool VG_(get_fnname_raw) ( Addr a, Char* buf, Int nbuf );

/* Like VG_(get_fnname), but without C++ demangling.  (But it does
 * Z-demangling and below-main renaming.) */
extern
Bool VG_(get_fnname_no_cxx_demangle) ( Addr a, Char* buf, Int nbuf );

/* Use DWARF2/3 CFA information to do one step of stack unwinding. */
extern Bool VG_(use_CF_info) ( /*MOD*/Addr* ipP,
                               /*MOD*/Addr* spP,
                               /*MOD*/Addr* fpP,
                               Addr min_accessible,
                               Addr max_accessible );

/* Use MSVC FPO data to do one step of stack unwinding. */
extern Bool VG_(use_FPO_info) ( /*MOD*/Addr* ipP,
                                /*MOD*/Addr* spP,
                                /*MOD*/Addr* fpP,
                                Addr min_accessible,
                                Addr max_accessible );

/* ppc64-linux only: find the TOC pointer (R2 value) that should be in
   force at the entry point address of the function containing
   guest_code_addr.  Returns 0 if not known. */
extern Addr VG_(get_tocptr) ( Addr guest_code_addr );

/* Map a function name to its entry point and toc pointer.  Is done by
   sequential search of all symbol tables, so is very slow.  To
   mitigate the worst performance effects, you may specify a soname
   pattern, and only objects matching that pattern are searched.
   Therefore specify "*" to search all the objects.  On TOC-afflicted
   platforms, a symbol is deemed to be found only if it has a nonzero
   TOC pointer.  */
extern
Bool VG_(lookup_symbol_SLOW)(UChar* sopatt, UChar* name, Addr* pEnt, Addr* pToc);

#endif   // __PUB_CORE_DEBUGINFO_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
