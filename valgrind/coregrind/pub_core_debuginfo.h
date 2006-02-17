
/*--------------------------------------------------------------------*/
/*--- Debug info.                             pub_core_debuginfo.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Julian Seward
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
//
// And its internals are currently a mess.  Its interface is ugly, too.
//--------------------------------------------------------------------

#include "pub_tool_debuginfo.h"

/* Notify the debuginfo system about a new mapping.  This is the way
   new debug information gets loaded.  If allow_SkFileV is True, it
   will try load debug info if the mapping at 'a' belongs to Valgrind;
   whereas normally (False) it will not do that.  This allows us to
   carefully control when the thing will read symbols from the
   Valgrind executable itself. */
extern void VG_(di_notify_mmap)( Addr a, Bool allow_SkFileV );

extern void VG_(di_notify_munmap)( Addr a, SizeT len );

extern void VG_(di_notify_mprotect)( Addr a, SizeT len, UInt prot );

extern SegInfo *VG_(read_seg_symbols) ( Addr addr, SizeT len,
                                        OffT offset, const Char* filename);

extern Bool VG_(get_fnname_nodemangle)( Addr a, Char* fnname, Int n_fnname );

extern Bool VG_(use_CFI_info) ( /*MOD*/Addr* ipP,
                                /*MOD*/Addr* spP,
                                /*MOD*/Addr* fpP,
                                Addr min_accessible,
                                Addr max_accessible );

/* ppc64-linux only: find the TOC pointer (R2 value) that should be in
   force at the entry point address of the function containing
   guest_code_addr.  Returns 0 if not known. */
extern Addr VG_(get_tocptr) ( Addr guest_code_addr );

/* This is only available to core... don't demangle C++ names, but do
   do Z-demangling, match anywhere in function, and don't show
   offsets. */
extern
Bool VG_(get_fnname_Z_demangle_only) ( Addr a, Char* buf, Int nbuf );

#endif   // __PUB_CORE_DEBUGINFO_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
