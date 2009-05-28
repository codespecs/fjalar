
/*--------------------------------------------------------------------*/
/*--- Reading of syms & debug info from PDB-format files.          ---*/
/*---                                               priv_readpdb.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.
   Spring 2008:
      derived from readelf.c and valgrind-20031012-wine/vg_symtab2.c
      derived from wine-1.0/tools/winedump/pdb.c and msc.c

   Copyright (C) 2000-2008 Julian Seward
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

#ifndef __PRIV_READPDB_H
#define __PRIV_READPDB_H

/* Returns True if OK, False for any kind of failure. */
extern Bool ML_(read_pdb_debug_info)(
               DebugInfo* di,
               Addr       obj_avma,
               PtrdiffT   unknown_purpose__reloc,
               void*      pdbimage,
               SizeT      n_pdbimage,
               Char*      pdbname,
               ULong      pdbmtime
            );

#endif /* ndef __PRIV_READPDB_H */

/*--------------------------------------------------------------------*/
/*--- end                                           priv_readpdb.h ---*/
/*--------------------------------------------------------------------*/
