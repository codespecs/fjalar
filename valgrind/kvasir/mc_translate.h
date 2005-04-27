/*
   This file is part of MemCheck, a heavyweight Valgrind tool for
   detecting memory errors.

   Copyright (C) 2000-2005 Julian Seward
      jseward@acm.org

      Modified by Philip Guo to cancel out memory profiling features
      and to only keep the A and V-bit memory tracking for DynComp.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

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

#ifndef MC_TRANSLATE_H
#define MC_TRANSLATE_H

// Comment this out or else it won't compile:
//typedef  IRExpr  IRAtom;

/* assign value to tmp */
#define assign(_bb,_tmp,_expr)   \
   addStmtToIRBB((_bb), IRStmt_Tmp((_tmp),(_expr)))

/* add stmt to a bb */
#define stmt(_bb,_stmt)    \
   addStmtToIRBB((_bb), (_stmt))

/* build various kinds of expressions */
#define binop(_op, _arg1, _arg2) IRExpr_Binop((_op),(_arg1),(_arg2))
#define unop(_op, _arg)          IRExpr_Unop((_op),(_arg))
#define mkU8(_n)                 IRExpr_Const(IRConst_U8(_n))
#define mkU16(_n)                IRExpr_Const(IRConst_U16(_n))
#define mkU32(_n)                IRExpr_Const(IRConst_U32(_n))
#define mkU64(_n)                IRExpr_Const(IRConst_U64(_n))
#define mkV128(_n)               IRExpr_Const(IRConst_V128(_n))
#define mkexpr(_tmp)             IRExpr_Tmp((_tmp))

Bool sameKindedAtoms ( /*IRAtom*/ IRExpr* a1, /*IRAtom*/ IRExpr* a2 );
IRType  shadowType ( IRType ty );

#endif
