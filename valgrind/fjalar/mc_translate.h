/*

   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
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
#include "pub_tool_hashtable.h"     // For mc_include.h
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)
#include "pub_tool_xarray.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"

// See below for comments explaining what this is for.
typedef
   enum __attribute__((packed)) { HuUnU=0, HuPCa=1, HuOth=2 }
   HowUsed;

/*------------------------------------------------------------*/
/*--- Memcheck running state, and tmp management.          ---*/
/*------------------------------------------------------------*/

/* For a few (maybe 1%) IROps, we have both a cheaper, less exact vbit
   propagation scheme, and a more expensive, more precise vbit propagation
   scheme.  This enum describes, for such an IROp, which scheme to use. */
typedef
   enum {
      // Use the cheaper, less-exact variant.
      DLcheap=4,
      // Choose between cheap and expensive based on analysis of the block
      // to be instrumented.  Note that the choice may be done on a
      // per-instance basis of the IROp that this DetailLevel describes.
      DLauto,
      // Use the more expensive, more-exact variant.
      DLexpensive
   }
   DetailLevel;


/* A readonly part of the running state.  For IROps that have both a
   less-exact and more-exact interpretation, records which interpretation is
   to be used.  */
typedef
   struct {
      // For Add32/64 and Sub32/64, all 3 settings are allowed.  For the
      // DLauto case, a per-instance decision is to be made by inspecting
      // the associated tmp's entry in MCEnv.tmpHowUsed.
      DetailLevel dl_Add32;
      DetailLevel dl_Add64;
      DetailLevel dl_Sub32;
      DetailLevel dl_Sub64;
      // For Cmp{EQ,NE}{64,32,16,8}, only DLcheap and DLexpensive are
      // allowed.
      DetailLevel dl_CmpEQ64_CmpNE64;
      DetailLevel dl_CmpEQ32_CmpNE32;
      DetailLevel dl_CmpEQ16_CmpNE16;
      DetailLevel dl_CmpEQ8_CmpNE8;
   }
   DetailLevelByOp;


/* Carries info about a particular tmp.  The tmp's number is not
   recorded, as this is implied by (equal to) its index in the tmpMap
   in MCEnv.  The tmp's type is also not recorded, as this is present
   in MCEnv.sb->tyenv.

   When .kind is Orig, .shadowV and .shadowB may give the identities
   of the temps currently holding the associated definedness (shadowV)
   and origin (shadowB) values, or these may be IRTemp_INVALID if code
   to compute such values has not yet been emitted.

   When .kind is VSh or BSh then the tmp is holds a V- or B- value,
   and so .shadowV and .shadowB must be IRTemp_INVALID, since it is
   illogical for a shadow tmp itself to be shadowed.
*/
typedef
   enum { Orig=1, VSh=2, BSh=3, DC=4 }
   TempKind;

typedef
   struct {
      TempKind kind;
      IRTemp   shadowV;
      IRTemp   shadowB;
   }
   TempMapEnt;


/* A |HowUsed| value carries analysis results about how values are used,
   pertaining to whether we need to instrument integer adds expensively or
   not.  The running state carries a (readonly) mapping from original tmp to
   a HowUsed value for it.  A usage value can be one of three values,
   forming a 3-point chain lattice.

      HuOth   ("Other") used in some arbitrary way
       |
      HuPCa   ("PCast") used *only* in effectively a PCast, in which all
       |      we care about is the all-defined vs not-all-defined distinction
       |
      HuUnU   ("Unused") not used at all.

   The "safe" (don't-know) end of the lattice is "HuOth".  See comments
   below in |preInstrumentationAnalysis| for further details.
*/
/* DECLARED ABOVE:
typedef
   enum __attribute__((packed)) { HuUnU=0, HuPCa=1, HuOth=2 }
   HowUsed;
*/

// Not actually necessary, but we don't want to waste D1 space.
STATIC_ASSERT(sizeof(HowUsed) == 1);


/* Carries around state during memcheck instrumentation. */
typedef
   struct _MCEnv {
      /* MODIFIED: the superblock being constructed.  IRStmts are
         added. */
      IRSB* sb;
      Bool  trace;

      /* MODIFIED: a table [0 .. #temps_in_sb-1] which gives the
         current kind and possibly shadow temps for each temp in the
         IRSB being constructed.  Note that it does not contain the
         type of each tmp.  If you want to know the type, look at the
         relevant entry in sb->tyenv.  It follows that at all times
         during the instrumentation process, the valid indices for
         tmpMap and sb->tyenv are identical, being 0 .. N-1 where N is
         total number of Orig, V- and B- temps allocated so far.

         The reason for this strange split (types in one place, all
         other info in another) is that we need the types to be
         attached to sb so as to make it possible to do
         "typeOfIRExpr(mce->bb->tyenv, ...)" at various places in the
         instrumentation process. */
      XArray* /* of TempMapEnt */ tmpMap;

      /* READONLY: contains details of which ops should be expensively
         instrumented. */
      DetailLevelByOp dlbo;

      /* READONLY: for each original tmp, how the tmp is used.  This is
         computed by |preInstrumentationAnalysis|.  Valid indices are
         0 .. #temps_in_sb-1 (same as for tmpMap). */
      HowUsed* tmpHowUsed;

      /* READONLY: the guest layout.  This indicates which parts of
         the guest state should be regarded as 'always defined'. */
      const VexGuestLayout* layout;

      /* READONLY: the host word type.  Needed for constructing
         arguments of type 'HWord' to be passed to helper functions.
         Ity_I32 or Ity_I64 only. */
      IRType hWordTy;
   }
   MCEnv;

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

      /* READONLY: the guest layout.  This indicates which parts of
         the guest state should be regarded as 'always defined'. */
      const VexGuestLayout* layout;
      /* READONLY: the host word type.  Needed for constructing
         arguments of type 'HWord' to be passed to helper functions.
         Ity_I32 or Ity_I64 only. */
      IRType hWordTy;

      MCEnv* mce;

      /* MODIFIED: Original address of guest instruction whose IR
         we're now processing, as taken from the last IMark we saw. */
      Addr origAddr;
   }
   DCEnv;


/*------------------------------------------------------------*/
/*--- Constructing IR fragments                            ---*/
/*------------------------------------------------------------*/

/* add stmt to a bb */
static inline void stmt ( HChar cat, MCEnv* mce, IRStmt* st ) {
   if (mce->trace) {
      printf("  %c: ", cat);
      ppIRStmt(st);
      printf("\n");
   }
   addStmtToIRSB(mce->sb, st);
}

static inline void stmt_DC ( HChar cat, DCEnv* dce, IRStmt* st ) {
   if (dce->mce->trace) {
      printf("D %c: ", cat);
      ppIRStmt(st);
      printf("\n");
   }
   addStmtToIRSB(dce->bb, st);
}

/* assign value to tmp */
static inline void assign ( HChar cat, MCEnv* mce, IRTemp tmp, IRExpr* expr ) {
  stmt(cat, mce, IRStmt_WrTmp(tmp,expr));
}

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

IRTemp newTemp ( MCEnv* mce, IRType ty, TempKind kind );

Bool sameKindedAtoms ( IRAtom* a1, IRAtom* a2 );
IRType  shadowTypeV ( IRType ty );

#endif
