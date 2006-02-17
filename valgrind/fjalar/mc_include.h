
/*--------------------------------------------------------------------*/
/*--- A header file for all parts of the MemCheck tool.            ---*/
/*---                                                 mc_include.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of MemCheck, a heavyweight Valgrind tool for
   detecting memory errors.

   Copyright (C) 2000-2005 Julian Seward
      jseward@acm.org

      Modified by Philip Guo (pgbovine@mit.edu) to serve as part of
      Fjalar, a dynamic analysis framework for C/C++ programs.

      (Moved a few declarations from mc_main.c and other files into here)

   Copyright (C) 2004-2006 Philip Guo, MIT CSAIL Program Analysis Group

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

/* Note: this header should contain declarations that are for use by
   Memcheck only -- declarations shared with Addrcheck go in mac_shared.h.
*/

#ifndef __MC_INCLUDE_H
#define __MC_INCLUDE_H

#include "mac_shared.h"

#define MC_(str)    VGAPPEND(vgMemCheck_,str)

/*------------------------------------------------------------*/
/*--- Command line options                                 ---*/
/*------------------------------------------------------------*/

/* There are no memcheck-specific ones, only mac-specific
   ones (those shared by both memcheck and addrcheck). */


/*------------------------------------------------------------*/
/*--- Functions                                            ---*/
/*------------------------------------------------------------*/

/* Functions defined in mc_main.c */
extern VG_REGPARM(1) void MC_(helperc_complain_undef) ( HWord );
extern void MC_(helperc_value_check8_fail) ( void );
extern void MC_(helperc_value_check4_fail) ( void );
extern void MC_(helperc_value_check1_fail) ( void );
extern void MC_(helperc_value_check0_fail) ( void );

extern VG_REGPARM(1) void MC_(helperc_STOREV8be) ( Addr, ULong );
extern VG_REGPARM(1) void MC_(helperc_STOREV8le) ( Addr, ULong );
extern VG_REGPARM(2) void MC_(helperc_STOREV4be) ( Addr, UWord );
extern VG_REGPARM(2) void MC_(helperc_STOREV4le) ( Addr, UWord );
extern VG_REGPARM(2) void MC_(helperc_STOREV2be) ( Addr, UWord );
extern VG_REGPARM(2) void MC_(helperc_STOREV2le) ( Addr, UWord );
extern VG_REGPARM(2) void MC_(helperc_STOREV1)   ( Addr, UWord );

extern VG_REGPARM(1) ULong MC_(helperc_LOADV8be) ( Addr );
extern VG_REGPARM(1) ULong MC_(helperc_LOADV8le) ( Addr );
extern VG_REGPARM(1) UWord MC_(helperc_LOADV4be) ( Addr );
extern VG_REGPARM(1) UWord MC_(helperc_LOADV4le) ( Addr );
extern VG_REGPARM(1) UWord MC_(helperc_LOADV2be) ( Addr );
extern VG_REGPARM(1) UWord MC_(helperc_LOADV2le) ( Addr );
extern VG_REGPARM(1) UWord MC_(helperc_LOADV1)   ( Addr );

extern void MC_(helperc_MAKE_STACK_UNINIT) ( Addr base, UWord len );

/* Functions defined in mc_translate.c */
extern
IRBB* MC_(instrument) ( VgCallbackClosure* closure,
                        IRBB* bb_in,
                        VexGuestLayout* layout,
                        VexGuestExtents* vge,
                        IRType gWordTy, IRType hWordTy );


// PG - pgbovine - begin

extern void mc_copy_address_range_state ( Addr src, Addr dst, SizeT len );
extern char mc_are_some_bytes_initialized (Addr a, SizeT len);

typedef enum {
   MC_Ok = 5, MC_AddrErr = 6, MC_ValueErr = 7
} MC_ReadResult;

// /* __inline__ */ void set_abit ( Addr a, UChar abit );

void set_abit_and_vbyte ( Addr a, UWord abit, UWord vbyte );
void set_vbyte ( Addr a, UWord vbyte );

Bool mc_check_writable ( Addr a, SizeT len, Addr* bad_addr );
MC_ReadResult mc_check_readable ( Addr a, SizeT len, Addr* bad_addr );

// PG - pgbovine - end


#endif /* ndef __MC_INCLUDE_H */

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
