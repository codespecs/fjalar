
/*--------------------------------------------------------------------*/
/*--- Read 'stabs' format debug info.             priv_readstabs.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2013 Julian Seward 
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

#ifndef __PRIV_READSTABS_H
#define __PRIV_READSTABS_H

#include "pub_core_basics.h"      // UChar
#include "pub_core_debuginfo.h"   // DebugInfo

/*
   Stabs reader greatly improved by Nick Nethercote, Apr 02.
   This module was also extensively hacked on by Jeremy Fitzhardinge
   and Tom Hughes.
*/

/* --------------------
   Stabs reader
   -------------------- */
extern
void ML_(read_debuginfo_stabs) ( DebugInfo* di,
                                 UChar* stabC,   Int stab_sz,
                                 HChar* stabstr, Int stabstr_sz );

#endif /* ndef __PRIV_READSTABS_H */

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
