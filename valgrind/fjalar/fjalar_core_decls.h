/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_core_decls.h:

Declarations of the few Valgrind core (non-tool) entities that Fjalar
uses.  Fjalar code (e.g., mc_main.c and typedata.c) includes this file
to call those entities.  Tool files must not include coregrind/pub_core_*.h (see
tests/check_headers_and_includes), so these are copied here instead.
The build checks that the copies agree with the originals (see the
fjalar_core_decls.stamp rule in Makefile.am).

*/

#ifndef FJALAR_CORE_DECLS_H
#define FJALAR_CORE_DECLS_H

#include "pub_tool_basics.h"

// From coregrind/pub_core_aspacemgr.h.
// mc_check_readable uses this to accept readable memory that Valgrind
// owns, which VG_(am_is_valid_for_client) rejects.
extern Bool VG_(am_is_valid_for_valgrind)(Addr start, SizeT len, UInt prot);

// From coregrind/pub_core_mallocfree.h.
// Used to release the demanglers' results, which are allocated in the
// VG_AR_DEMANGLE arena.  ArenaId is a typedef for Int.
extern void VG_(arena_free)(Int arena, void* ptr);
#define VG_AR_DEMANGLE 3

#endif /* FJALAR_CORE_DECLS_H */
