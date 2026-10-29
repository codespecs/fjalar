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


#ifndef MC_TRANSLATE_H
#define MC_TRANSLATE_H

#include "pub_tool_basics.h"
#include "pub_tool_poolalloc.h"     // For mc_include.h
#include "pub_tool_hashtable.h"     // For mc_include.h
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)
#include "pub_tool_xarray.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"

/* Memcheck's state during instrumentation, which mc_translate.c defines.
   Fjalar code uses it only through the functions declared below. */
typedef struct _MCEnv MCEnv;

/* Carries around state during DynComp instrumentation. */
struct _DCEnv;

typedef
   struct _DCEnv {
      /* MODIFIED: the bb being constructed.  IRStmts are added. */
      IRSB* bb;

      /* MODIFIED: a table [0 .. #temps_in_original_bb-1] which maps
         original temps to their current their current shadow temp.
         Initially all entries are IRTemp_INVALID.  Entries are added
         lazily since many original temps are not used due to
         optimisation prior to instrumentation.  Note that floating
         point original tmps are shadowed by integer tmps of the same
         size, and Bit-typed original tmps are shadowed by the type
         Ity_I8.  See comment below. */
      IRTemp* tmpMap;
      UInt     n_originalTmps; /* for range checking */

      /* MODIFIED: a table [0 .. #temps_in_original_bb-1] which maps
         each original temp to the slot of MC_(helperc_LOAD_TAG_N)
         that holds the tags of the bytes loaded into it, or to -1.
         NULL if a load is an interaction (see loadIsInteraction_DC).
         See expr2tags_WrTmp_DC. */
      Int* loadTagSnapshots;
      Int  n_loadTagSnapshots; /* number of slots in use */

      /* READONLY: the guest layout.  This indicates which parts of
         the guest state should be regarded as 'always defined'. */
      const VexGuestLayout* layout;
      /* READONLY: the host word type.  Needed for constructing
         arguments of type 'HWord' to be passed to helper functions.
         Ity_I32 or Ity_I64 only. */
      IRType hWordTy;

      MCEnv* mce;
      /* READONLY: whether to print the statements that DynComp adds
         (Memcheck's trace flag). */
      Bool trace;

      /* MODIFIED: Original address of guest instruction whose IR
         we're now processing, as taken from the last IMark we saw. */
      Addr origAddr;

      /* READONLY: the bb being instrumented. */
      const IRSB* sb_in;
      /* MODIFIED: the index in sb_in of the statement being
         instrumented. */
      Int stmtIndex;
      /* READONLY: a table [0 .. #temps_in_original_bb-1] whose
         entries are True for the temporaries that only carry flags
         forward; see findFlagsCarryingTmps_DC.  NULL unless
         --dyncomp-interactions is comparisons. */
      Bool* tmpCarriesFlags;
      /* MODIFIED: a table [0 .. 2 * #temps_in_original_bb-1] whose
         entries 2*t and 2*t+1 are the pending carry tags of t, a
         temporary that carries flags, once its assignment has been
         instrumented; see notePendingCarryTags_DC.  NULL unless
         tmpCarriesFlags is non-NULL. */
      IRExpr** tmpPendingCarryTags;

      /* MODIFIED: True if the most recent PUT to the CC_OP field of the
         flags thunk stored a constant that says that an sbb instruction
         set the flags. */
      Bool sbbThunk;
   }
   DCEnv;


/*------------------------------------------------------------*/
/*--- Constructing IR fragments                            ---*/
/*------------------------------------------------------------*/

/* add stmt to a bb */
static inline void stmt_DC ( HChar cat, DCEnv* dce, IRStmt* st ) {
   if (dce->trace) {
      VG_(printf)("D %c: ", cat);
      ppIRStmt(st);
      VG_(printf)("\n");
   }
   addStmtToIRSB(dce->bb, st);
}

/* assign value to tmp */
static inline void assign_DC ( HChar cat, DCEnv* dce, IRTemp tmp, IRExpr* expr ) {
  stmt_DC(cat, dce, IRStmt_WrTmp(tmp,expr));
}

/* build various kinds of expressions */
#define triop(_op, _arg1, _arg2, _arg3) \
                                 IRExpr_Triop((_op),(_arg1),(_arg2),(_arg3))
#define binop(_op, _arg1, _arg2) IRExpr_Binop((_op),(_arg1),(_arg2))
#define unop(_op, _arg)          IRExpr_Unop((_op),(_arg))
#define mkU1(_n)                 IRExpr_Const(IRConst_U1(_n))
#define mkU8(_n)                 IRExpr_Const(IRConst_U8(_n))
#define mkU16(_n)                IRExpr_Const(IRConst_U16(_n))
#define mkU32(_n)                IRExpr_Const(IRConst_U32(_n))
#define mkU64(_n)                IRExpr_Const(IRConst_U64(_n))
#define mkV128(_n)               IRExpr_Const(IRConst_V128(_n))
#define mkexpr(_tmp)             IRExpr_RdTmp((_tmp))

/* An atom is either an IRExpr_Const or an IRExpr_Tmp, as defined by
   isIRAtom() in libvex_ir.h.  Because this instrumenter expects flat
   input, most of this code deals in atoms.  Usefully, a value atom
   always has a V-value which is also an atom: constants are shadowed
   by constants, and temps are shadowed by the corresponding shadow
   temporary. */

typedef  IRExpr  IRAtom;

/* Defined in fjalar_mc_translate.h. */
void mc_stmt ( HChar cat, MCEnv* mce, IRStmt* st );
IRTemp newTemp_DC ( MCEnv* mce, IRType ty );
IRType shadowTypeV_DC ( IRType ty );
void init_DCEnv_from_MCEnv ( DCEnv* dce, MCEnv* mce );

#endif
