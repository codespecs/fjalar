/* -*- mode: C; c-basic-offset: 3; -*- */

/*--------------------------------------------------------------------*/
/*--- s390x-specific definitions.                       cg-s390x.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Cachegrind, a Valgrind tool for cache
   profiling programs.

   Copyright IBM Corp. 2010-2012

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

/* Contributed by Christian Borntraeger */

#if defined(VGA_s390x)

#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"

#include "cg_arch.h"

void VG_(configure_caches)(cache_t* I1c, cache_t* D1c, cache_t* LLc,
                           Bool all_caches_clo_defined)
{
   // z900
   //
   // Source:
   // The microarchitecture of the IBM eServer z900 processor
   // IBM Journal of Research and Development
   // Volume 46, Number 4/5, pp 381-395, July/September 2002
   //
   // Split L1 I/D cache
   // Size: 256 kB each
   // Line size: 256 bytes
   // 4-way set associative
   // L2 cache: 16 MB x 2 (16 MB per 10 CPs)  (Charles Webb)

   // z800
   //
   // Source:  Charles Webb from IBM
   //
   // Split L1 I/D cache
   // Size: 256 kB each
   // Line size: 256 bytes
   // 4-way set associative
   // L2 cache: 16 MB  (or half that size)

   // z990
   //
   // The IBM eServer z990 microprocessor
   // IBM Journal of Research and Development
   // Volume 48, Number 3/4, pp 295-309, May/July 2004 
   //
   // Split L1 I/D cache
   // Size: 256 kB each
   // Line size: 256 bytes
   // 4-way set associative
   // L2 cache: 32 MB x 4 (32 MB per book/node)  (Charles Webb)

   // z890
   //
   // Source:  Charles Webb from IBM
   //
   // Split L1 I/D cache
   // Size: 256 kB each
   // Line size: 256 bytes
   // 4-way set associative
   // L2 cache: 32 MB  (or half that size)

   // z9
   //
   // Source:  Charles Webb from IBM
   //
   // Split L1 I/D cache
   // Size: 256 kB each
   // Line size: 256 bytes
   // 4-way set associative
   // L2 cache: 40 MB x 4 (40 MB per book/node)


   // Set caches to z10 default.
   // See IBM Journal of Research and Development
   // Issue Date: Jan. 2009
   // Volume: 53 Issue:1
   // fixs390: have a table for all available models and check /proc/cpuinfo
   *I1c = (cache_t) {   65536,  4, 256 };
   *D1c = (cache_t) {  131072,  8, 256 };
   *LLc = (cache_t) {50331648, 24, 256 };

   // Warn if config not completely specified from cmd line.  Note that
   // this message is slightly different from the one we give on x86/AMD64
   // when auto-detection fails;  this lets us filter out this one (which is
   // not important) in the regression test suite without filtering the
   // x86/AMD64 one (which we want to see if it ever occurs in the
   // regression test suite).
   //
   // If you change this message, please update
   // cachegrind/tests/filter_stderr!
   //
   if (!all_caches_clo_defined) {
      VG_(dmsg)("Warning: Cannot auto-detect cache config, "
                "assuming z10-EC cache configuration\n");
   }
}

#endif

/*--------------------------------------------------------------------*/
/*--- end                                               cg-s390x.c ---*/
/*--------------------------------------------------------------------*/
