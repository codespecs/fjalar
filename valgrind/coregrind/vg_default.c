
/*--------------------------------------------------------------------*/
/*--- Default panicky definitions of template functions that tools ---*/
/*--- should override.                                             ---*/
/*---                                                vg_defaults.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Nicholas Nethercote
      njn25@cam.ac.uk

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


#include "core.h"

/* ---------------------------------------------------------------------
   Error messages (for malformed tools)
   ------------------------------------------------------------------ */

/* If the tool fails to define one or more of the required functions,
 * make it very clear what went wrong! */

__attribute__ ((noreturn))
void VG_(missing_tool_func) ( const Char* fn )
{
   VG_(printf)(
      "\nTool error:\n"
      "  The tool you have selected is missing the function `%s',\n"
      "  which is required.\n\n",
      fn);
   VG_(tool_panic)("Missing tool function");
}

static __attribute__ ((noreturn))
void malloc_panic ( const Char* fn )
{
   VG_(printf)(
      "\nTool error:\n"
      "  The tool you have selected is missing the function `%s'\n"
      "  required because it is replacing malloc() et al.\n\n",
      fn);
   VG_(tool_panic)("Missing tool function");
}

/*------------------------------------------------------------*/
/*--- Replacing malloc et al                               ---*/
/*------------------------------------------------------------*/

Bool VG_(tl_malloc_called_deliberately) = False;

/* If the tool hasn't replaced malloc(), this one can be called
   deliberately.  The lock variable ensures that this isn't called by
   accident, which could happen if a malloc()-replacing tool forgot to
   implement TL_(malloc)() or TL_(free)().  */
__attribute__ ((weak))
void* TL_(malloc)( ThreadId tid, SizeT size )
{
   if (VG_(tl_malloc_called_deliberately))
      return VG_(cli_malloc)(VG_MIN_MALLOC_SZB, size);
   else 
      malloc_panic(__PRETTY_FUNCTION__);
}

__attribute__ ((weak))
void TL_(free)( ThreadId tid, void* p )
{
   /* see comment for TL_(malloc)() above */
   if (VG_(tl_malloc_called_deliberately))
      VG_(cli_free)(p);
   else 
      malloc_panic(__PRETTY_FUNCTION__);
}

/*--------------------------------------------------------------------*/
/*--- end                                            vg_defaults.c ---*/
/*--------------------------------------------------------------------*/
