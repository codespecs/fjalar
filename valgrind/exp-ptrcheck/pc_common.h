
/*--------------------------------------------------------------------*/
/*--- Ptrcheck: a pointer-use checker.                             ---*/
/*--- Exports for stuff shared between sg_ and h_ subtools.        ---*/
/*---                                                  pc_common.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Ptrcheck, a Valgrind tool for checking pointer
   use in programs.

   Copyright (C) 2008-2009 OpenWorks Ltd
      info@open-works.co.uk

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

#ifndef __PC_COMMON_H

#define __PC_COMMON_H

typedef  struct _Seg  Seg;   /* abstract every except in h_main.c */

void sg_record_error_SorG ( ThreadId tid,
                            Addr addr, SSizeT sszB,
                            HChar* expect, HChar* actual );

void h_record_heap_error( Addr a, SizeT size, Seg* vseg, Bool is_write );

void h_record_arith_error( Seg* seg1, Seg* seg2, HChar* opname );

void h_record_sysparam_error( ThreadId tid, CorePart part, Char* s,
                              Addr lo, Addr hi, Seg* seglo, Seg* seghi );

Bool pc_eq_Error ( VgRes res, Error* e1, Error* e2 );
void pc_pp_Error ( Error* err );
UInt pc_update_Error_extra ( Error* err );
Bool pc_is_recognised_suppression ( Char* name, Supp *su );
Bool pc_read_extra_suppression_info ( Int fd, Char* buf, 
                                      Int nBuf, Supp* su );
Bool pc_error_matches_suppression (Error* err, Supp* su);
Char* pc_get_error_name ( Error* err );
void pc_print_extra_suppression_info ( Error* err );

extern Bool h_clo_partial_loads_ok;
/* extern Bool h_clo_lossage_check; */
extern Bool sg_clo_enable_sg_checks;

Bool pc_process_cmd_line_options(Char* arg);
void pc_print_usage(void);
void pc_print_debug_usage(void);


#endif

/*--------------------------------------------------------------------*/
/*--- end                                              pc_common.h ---*/
/*--------------------------------------------------------------------*/
