/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* mc_fjalar.h:

Fjalar's interface to its copy of Memcheck:  Memcheck's private header
mc_include.h, and the functions that Fjalar adds to Memcheck.
fjalar_mc_main.h defines those functions, and mc_main.c includes
fjalar_mc_main.h.  Fjalar's files include this header instead of
mc_include.h.

*/

#ifndef MC_FJALAR_H
#define MC_FJALAR_H

// mc_include.h uses these, but does not include them.
#include "pub_tool_basics.h"
#include "pub_tool_execontext.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_errormgr.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_poolalloc.h"

#include "mc_include.h"

// Copies the A and V bits and the DynComp tag of the len-byte guest
// register at guestOffset in thread tid's guest state to the len bytes
// of memory at dst.  len must be 1, 2, 4, or 8.
void mc_copy_guest_reg_state ( ThreadId tid, Int guestOffset, Addr dst,
                               SizeT len );

char mc_are_some_bytes_initialized ( Addr a, SizeT len );
Bool mc_check_writable ( Addr a, SizeT len, Addr* bad_addr );
// Returns True if the len bytes at a are addressable, defined, and
// readable by the client or by Valgrind.
Bool mc_check_readable ( Addr a, SizeT len, Addr* bad_addr );

#endif
