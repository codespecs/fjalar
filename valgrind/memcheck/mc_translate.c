
/*--------------------------------------------------------------------*/
/*--- Instrument IR to perform memory checking operations.         ---*/
/*---                                               mc_translate.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of MemCheck, a heavyweight Valgrind tool for
   detecting memory errors.

   Copyright (C) 2000-2009 Julian Seward 
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

#include "pub_tool_basics.h"
#include "pub_tool_hashtable.h"     // For mc_include.h
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_machine.h"     // VG_(fnptr_to_fnentry)
#include "pub_tool_xarray.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"

#include "mc_include.h"


/* This file implements the Memcheck instrumentation, and in
   particular contains the core of its undefined value detection
   machinery.  For a comprehensive background of the terminology,
   algorithms and rationale used herein, read:

     Using Valgrind to detect undefined value errors with
     bit-precision

     Julian Seward and Nicholas Nethercote

     2005 USENIX Annual Technical Conference (General Track),
     Anaheim, CA, USA, April 10-15, 2005.

   ----

   Here is as good a place as any to record exactly when V bits are and
   should be checked, why, and what function is responsible.

   
   Memcheck complains when an undefined value is used:

   1. In the condition of a conditional branch.  Because it could cause
      incorrect control flow, and thus cause incorrect externally-visible
      behaviour.  [mc_translate.c:complainIfUndefined]

   2. As an argument to a system call, or as the value that specifies
      the system call number.  Because it could cause an incorrect
      externally-visible side effect.  [mc_translate.c:mc_pre_reg_read]

   3. As the address in a load or store.  Because it could cause an
      incorrect value to be used later, which could cause externally-visible
      behaviour (eg. via incorrect control flow or an incorrect system call
      argument)  [complainIfUndefined]

   4. As the target address of a branch.  Because it could cause incorrect
      control flow.  [complainIfUndefined]

   5. As an argument to setenv, unsetenv, or putenv.  Because it could put
      an incorrect value into the external environment.
      [mc_replace_strmem.c:VG_WRAP_FUNCTION_ZU(*, *env)]

   6. As the index in a GETI or PUTI operation.  I'm not sure why... (njn).
      [complainIfUndefined]

   7. As an argument to the VALGRIND_CHECK_MEM_IS_DEFINED and
      VALGRIND_CHECK_VALUE_IS_DEFINED client requests.  Because the user
      requested it.  [in memcheck.h]


   Memcheck also complains, but should not, when an undefined value is used:

   8. As the shift value in certain SIMD shift operations (but not in the
      standard integer shift operations).  This inconsistency is due to
      historical reasons.)  [complainIfUndefined]


   Memcheck does not complain, but should, when an undefined value is used:

   9. As an input to a client request.  Because the client request may
      affect the visible behaviour -- see bug #144362 for an example
      involving the malloc replacements in vg_replace_malloc.c and
      VALGRIND_NON_SIMD_CALL* requests, where an uninitialised argument
      isn't identified.  That bug report also has some info on how to solve
      the problem.  [valgrind.h:VALGRIND_DO_CLIENT_REQUEST]


   In practice, 1 and 2 account for the vast majority of cases.
*/

/*------------------------------------------------------------*/
/*--- Forward decls                                        ---*/
/*------------------------------------------------------------*/

struct _MCEnv;

static IRType  shadowTypeV ( IRType ty );
static IRExpr* expr2vbits ( struct _MCEnv* mce, IRExpr* e );
static IRTemp  findShadowTmpB ( struct _MCEnv* mce, IRTemp orig );


/*------------------------------------------------------------*/
/*--- Memcheck running state, and tmp management.          ---*/
/*------------------------------------------------------------*/

/* Carries around state during memcheck instrumentation. */
typedef
   struct _MCEnv {
      /* MODIFIED: the superblock being constructed.  IRStmts are
         added. */
      IRSB* bb;
      Bool  trace;

      /* MODIFIED: a table [0 .. #temps_in_original_bb-1] which maps
         original temps to their current their current shadow temp.
         Initially all entries are IRTemp_INVALID.  Entries are added
         lazily since many original temps are not used due to
         optimisation prior to instrumentation.  Note that floating
         point original tmps are shadowed by integer tmps of the same
         size, and Bit-typed original tmps are shadowed by the type
         Ity_I8.  See comment below. */
      IRTemp* tmpMapV;        /* V-bit tmp shadows */
      IRTemp* tmpMapB; /* origin tracking tmp shadows */
      Int     n_originalTmps; /* for range checking */

      /* MODIFIED: indicates whether "bogus" literals have so far been
         found.  Starts off False, and may change to True. */
      Bool    bogusLiterals;

      /* READONLY: the guest layout.  This indicates which parts of
         the guest state should be regarded as 'always defined'. */
      VexGuestLayout* layout;

      /* READONLY: the host word type.  Needed for constructing
         arguments of type 'HWord' to be passed to helper functions.
         Ity_I32 or Ity_I64 only. */
      IRType hWordTy;
   }
   MCEnv;

/* SHADOW TMP MANAGEMENT.  Shadow tmps are allocated lazily (on
   demand), as they are encountered.  This is for two reasons.

   (1) (less important reason): Many original tmps are unused due to
   initial IR optimisation, and we do not want to spaces in tables
   tracking them.

   Shadow IRTemps are therefore allocated on demand.  mce.tmpMap is a
   table indexed [0 .. n_types-1], which gives the current shadow for
   each original tmp, or INVALID_IRTEMP if none is so far assigned.
   It is necessary to support making multiple assignments to a shadow
   -- specifically, after testing a shadow for definedness, it needs
   to be made defined.  But IR's SSA property disallows this.  

   (2) (more important reason): Therefore, when a shadow needs to get
   a new value, a new temporary is created, the value is assigned to
   that, and the tmpMap is updated to reflect the new binding.

   A corollary is that if the tmpMap maps a given tmp to
   IRTemp_INVALID and we are hoping to read that shadow tmp, it means
   there's a read-before-write error in the original tmps.  The IR
   sanity checker should catch all such anomalies, however.  
*/

/* Find the tmp currently shadowing the given original tmp.  If none
   so far exists, allocate one.  */
static IRTemp findShadowTmpV ( MCEnv* mce, IRTemp orig )
{
   tl_assert(orig < mce->n_originalTmps);
   if (mce->tmpMapV[orig] == IRTemp_INVALID) {
      mce->tmpMapV[orig] 
         = newIRTemp(mce->bb->tyenv, 
                     shadowTypeV(mce->bb->tyenv->types[orig]));
   }
   return mce->tmpMapV[orig];
}

/* Allocate a new shadow for the given original tmp.  This means any
   previous shadow is abandoned.  This is needed because it is
   necessary to give a new value to a shadow once it has been tested
   for undefinedness, but unfortunately IR's SSA property disallows
   this.  Instead we must abandon the old shadow, allocate a new one
   and use that instead. */
static void newShadowTmpV ( MCEnv* mce, IRTemp orig )
{
   tl_assert(orig < mce->n_originalTmps);
   mce->tmpMapV[orig] 
      = newIRTemp(mce->bb->tyenv, 
                  shadowTypeV(mce->bb->tyenv->types[orig]));
}


/*------------------------------------------------------------*/
/*--- IRAtoms -- a subset of IRExprs                       ---*/
/*------------------------------------------------------------*/

/* An atom is either an IRExpr_Const or an IRExpr_Tmp, as defined by
   isIRAtom() in libvex_ir.h.  Because this instrumenter expects flat
   input, most of this code deals in atoms.  Usefully, a value atom
   always has a V-value which is also an atom: constants are shadowed
   by constants, and temps are shadowed by the corresponding shadow
   temporary. */

typedef  IRExpr  IRAtom;

/* (used for sanity checks only): is this an atom which looks
   like it's from original code? */
static Bool isOriginalAtom ( MCEnv* mce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_RdTmp && a1->Iex.RdTmp.tmp < mce->n_originalTmps)
      return True;
   return False;
}

/* (used for sanity checks only): is this an atom which looks
   like it's from shadow code? */
static Bool isShadowAtom ( MCEnv* mce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_RdTmp && a1->Iex.RdTmp.tmp >= mce->n_originalTmps)
      return True;
   return False;
}

/* (used for sanity checks only): check that both args are atoms and
   are identically-kinded. */
static Bool sameKindedAtoms ( IRAtom* a1, IRAtom* a2 )
{
   if (a1->tag == Iex_RdTmp && a2->tag == Iex_RdTmp)
      return True;
   if (a1->tag == Iex_Const && a2->tag == Iex_Const)
      return True;
   return False;
}


/*------------------------------------------------------------*/
/*--- Type management                                      ---*/
/*------------------------------------------------------------*/

/* Shadow state is always accessed using integer types.  This returns
   an integer type with the same size (as per sizeofIRType) as the
   given type.  The only valid shadow types are Bit, I8, I16, I32,
   I64, V128. */

static IRType shadowTypeV ( IRType ty )
{
   switch (ty) {
      case Ity_I1:
      case Ity_I8:
      case Ity_I16:
      case Ity_I32: 
      case Ity_I64: 
      case Ity_I128: return ty;
      case Ity_F32:  return Ity_I32;
      case Ity_F64:  return Ity_I64;
      case Ity_V128: return Ity_V128;
      default: ppIRType(ty); 
               VG_(tool_panic)("memcheck:shadowTypeV");
   }
}

/* Produce a 'defined' value of the given shadow type.  Should only be
   supplied shadow types (Bit/I8/I16/I32/UI64). */
static IRExpr* definedOfType ( IRType ty ) {
   switch (ty) {
      case Ity_I1:   return IRExpr_Const(IRConst_U1(False));
      case Ity_I8:   return IRExpr_Const(IRConst_U8(0));
      case Ity_I16:  return IRExpr_Const(IRConst_U16(0));
      case Ity_I32:  return IRExpr_Const(IRConst_U32(0));
      case Ity_I64:  return IRExpr_Const(IRConst_U64(0));
      case Ity_V128: return IRExpr_Const(IRConst_V128(0x0000));
      default:       VG_(tool_panic)("memcheck:definedOfType");
   }
}


/*------------------------------------------------------------*/
/*--- Constructing IR fragments                            ---*/
/*------------------------------------------------------------*/

/* add stmt to a bb */
static inline void stmt ( HChar cat, MCEnv* mce, IRStmt* st ) {
   if (mce->trace) {
      VG_(printf)("  %c: ", cat);
      ppIRStmt(st);
      VG_(printf)("\n");
   }
   addStmtToIRSB(mce->bb, st);
}

/* assign value to tmp */
static inline 
void assign ( HChar cat, MCEnv* mce, IRTemp tmp, IRExpr* expr ) {
  stmt(cat, mce, IRStmt_WrTmp(tmp,expr));
}

/* build various kinds of expressions */
#define binop(_op, _arg1, _arg2) IRExpr_Binop((_op),(_arg1),(_arg2))
#define unop(_op, _arg)          IRExpr_Unop((_op),(_arg))
#define mkU8(_n)                 IRExpr_Const(IRConst_U8(_n))
#define mkU16(_n)                IRExpr_Const(IRConst_U16(_n))
#define mkU32(_n)                IRExpr_Const(IRConst_U32(_n))
#define mkU64(_n)                IRExpr_Const(IRConst_U64(_n))
#define mkV128(_n)               IRExpr_Const(IRConst_V128(_n))
#define mkexpr(_tmp)             IRExpr_RdTmp((_tmp))

/* Bind the given expression to a new temporary, and return the
   temporary.  This effectively converts an arbitrary expression into
   an atom.

   'ty' is the type of 'e' and hence the type that the new temporary
   needs to be.  But passing it is redundant, since we can deduce the
   type merely by inspecting 'e'.  So at least that fact to assert
   that the two types agree. */
static IRAtom* assignNew ( HChar cat, MCEnv* mce, IRType ty, IRExpr* e ) {
   IRTemp t;
   IRType tyE = typeOfIRExpr(mce->bb->tyenv, e);
   tl_assert(tyE == ty); /* so 'ty' is redundant (!) */
   t = newIRTemp(mce->bb->tyenv, ty);
   assign(cat, mce, t, e);
   return mkexpr(t);
}


/*------------------------------------------------------------*/
/*--- Constructing definedness primitive ops               ---*/
/*------------------------------------------------------------*/

/* --------- Defined-if-either-defined --------- */

static IRAtom* mkDifD8 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I8, binop(Iop_And8, a1, a2));
}

static IRAtom* mkDifD16 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I16, binop(Iop_And16, a1, a2));
}

static IRAtom* mkDifD32 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I32, binop(Iop_And32, a1, a2));
}

static IRAtom* mkDifD64 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I64, binop(Iop_And64, a1, a2));
}

static IRAtom* mkDifDV128 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_V128, binop(Iop_AndV128, a1, a2));
}

/* --------- Undefined-if-either-undefined --------- */

static IRAtom* mkUifU8 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I8, binop(Iop_Or8, a1, a2));
}

static IRAtom* mkUifU16 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I16, binop(Iop_Or16, a1, a2));
}

static IRAtom* mkUifU32 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I32, binop(Iop_Or32, a1, a2));
}

static IRAtom* mkUifU64 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_I64, binop(Iop_Or64, a1, a2));
}

static IRAtom* mkUifUV128 ( MCEnv* mce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(mce,a1));
   tl_assert(isShadowAtom(mce,a2));
   return assignNew('V', mce, Ity_V128, binop(Iop_OrV128, a1, a2));
}

static IRAtom* mkUifU ( MCEnv* mce, IRType vty, IRAtom* a1, IRAtom* a2 ) {
   switch (vty) {
      case Ity_I8:   return mkUifU8(mce, a1, a2);
      case Ity_I16:  return mkUifU16(mce, a1, a2);
      case Ity_I32:  return mkUifU32(mce, a1, a2);
      case Ity_I64:  return mkUifU64(mce, a1, a2);
      case Ity_V128: return mkUifUV128(mce, a1, a2);
      default:
         VG_(printf)("\n"); ppIRType(vty); VG_(printf)("\n");
         VG_(tool_panic)("memcheck:mkUifU");
   }
}

/* --------- The Left-family of operations. --------- */

static IRAtom* mkLeft8 ( MCEnv* mce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(mce,a1));
   return assignNew('V', mce, Ity_I8, unop(Iop_Left8, a1));
}

static IRAtom* mkLeft16 ( MCEnv* mce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(mce,a1));
   return assignNew('V', mce, Ity_I16, unop(Iop_Left16, a1));
}

static IRAtom* mkLeft32 ( MCEnv* mce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(mce,a1));
   return assignNew('V', mce, Ity_I32, unop(Iop_Left32, a1));
}

static IRAtom* mkLeft64 ( MCEnv* mce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(mce,a1));
   return assignNew('V', mce, Ity_I64, unop(Iop_Left64, a1));
}

/* --------- 'Improvement' functions for AND/OR. --------- */

/* ImproveAND(data, vbits) = data OR vbits.  Defined (0) data 0s give
   defined (0); all other -> undefined (1).
*/
static IRAtom* mkImproveAND8 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', mce, Ity_I8, binop(Iop_Or8, data, vbits));
}

static IRAtom* mkImproveAND16 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', mce, Ity_I16, binop(Iop_Or16, data, vbits));
}

static IRAtom* mkImproveAND32 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', mce, Ity_I32, binop(Iop_Or32, data, vbits));
}

static IRAtom* mkImproveAND64 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', mce, Ity_I64, binop(Iop_Or64, data, vbits));
}

static IRAtom* mkImproveANDV128 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', mce, Ity_V128, binop(Iop_OrV128, data, vbits));
}

/* ImproveOR(data, vbits) = ~data OR vbits.  Defined (0) data 1s give
   defined (0); all other -> undefined (1).
*/
static IRAtom* mkImproveOR8 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', mce, Ity_I8, 
             binop(Iop_Or8, 
                   assignNew('V', mce, Ity_I8, unop(Iop_Not8, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR16 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', mce, Ity_I16, 
             binop(Iop_Or16, 
                   assignNew('V', mce, Ity_I16, unop(Iop_Not16, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR32 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', mce, Ity_I32, 
             binop(Iop_Or32, 
                   assignNew('V', mce, Ity_I32, unop(Iop_Not32, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR64 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', mce, Ity_I64, 
             binop(Iop_Or64, 
                   assignNew('V', mce, Ity_I64, unop(Iop_Not64, data)), 
                   vbits) );
}

static IRAtom* mkImproveORV128 ( MCEnv* mce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(mce, data));
   tl_assert(isShadowAtom(mce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', mce, Ity_V128, 
             binop(Iop_OrV128, 
                   assignNew('V', mce, Ity_V128, unop(Iop_NotV128, data)), 
                   vbits) );
}

/* --------- Pessimising casts. --------- */

static IRAtom* mkPCastTo( MCEnv* mce, IRType dst_ty, IRAtom* vbits ) 
{
   IRType  src_ty;
   IRAtom* tmp1;
   /* Note, dst_ty is a shadow type, not an original type. */
   /* First of all, collapse vbits down to a single bit. */
   tl_assert(isShadowAtom(mce,vbits));
   src_ty = typeOfIRExpr(mce->bb->tyenv, vbits);

   /* Fast-track some common cases */
   if (src_ty == Ity_I32 && dst_ty == Ity_I32)
      return assignNew('V', mce, Ity_I32, unop(Iop_CmpwNEZ32, vbits));

   if (src_ty == Ity_I64 && dst_ty == Ity_I64)
      return assignNew('V', mce, Ity_I64, unop(Iop_CmpwNEZ64, vbits));

   if (src_ty == Ity_I32 && dst_ty == Ity_I64) {
      IRAtom* tmp = assignNew('V', mce, Ity_I32, unop(Iop_CmpwNEZ32, vbits));
      return assignNew('V', mce, Ity_I64, binop(Iop_32HLto64, tmp, tmp));
   }

   /* Else do it the slow way .. */
   tmp1   = NULL;
   switch (src_ty) {
      case Ity_I1:
         tmp1 = vbits;
         break;
      case Ity_I8: 
         tmp1 = assignNew('V', mce, Ity_I1, unop(Iop_CmpNEZ8, vbits));
         break;
      case Ity_I16: 
         tmp1 = assignNew('V', mce, Ity_I1, unop(Iop_CmpNEZ16, vbits));
         break;
      case Ity_I32: 
         tmp1 = assignNew('V', mce, Ity_I1, unop(Iop_CmpNEZ32, vbits));
         break;
      case Ity_I64: 
         tmp1 = assignNew('V', mce, Ity_I1, unop(Iop_CmpNEZ64, vbits));
         break;
      case Ity_I128: {
         /* Gah.  Chop it in half, OR the halves together, and compare
            that with zero. */
         IRAtom* tmp2 = assignNew('V', mce, Ity_I64, unop(Iop_128HIto64, vbits));
         IRAtom* tmp3 = assignNew('V', mce, Ity_I64, unop(Iop_128to64, vbits));
         IRAtom* tmp4 = assignNew('V', mce, Ity_I64, binop(Iop_Or64, tmp2, tmp3));
         tmp1         = assignNew('V', mce, Ity_I1, 
                                       unop(Iop_CmpNEZ64, tmp4));
         break;
      }
      default:
         ppIRType(src_ty);
         VG_(tool_panic)("mkPCastTo(1)");
   }
   tl_assert(tmp1);
   /* Now widen up to the dst type. */
   switch (dst_ty) {
      case Ity_I1:
         return tmp1;
      case Ity_I8: 
         return assignNew('V', mce, Ity_I8, unop(Iop_1Sto8, tmp1));
      case Ity_I16: 
         return assignNew('V', mce, Ity_I16, unop(Iop_1Sto16, tmp1));
      case Ity_I32: 
         return assignNew('V', mce, Ity_I32, unop(Iop_1Sto32, tmp1));
      case Ity_I64: 
         return assignNew('V', mce, Ity_I64, unop(Iop_1Sto64, tmp1));
      case Ity_V128:
         tmp1 = assignNew('V', mce, Ity_I64,  unop(Iop_1Sto64, tmp1));
         tmp1 = assignNew('V', mce, Ity_V128, binop(Iop_64HLtoV128, tmp1, tmp1));
         return tmp1;
      case Ity_I128:
         tmp1 = assignNew('V', mce, Ity_I64,  unop(Iop_1Sto64, tmp1));
         tmp1 = assignNew('V', mce, Ity_I128, binop(Iop_64HLto128, tmp1, tmp1));
         return tmp1;
      default: 
         ppIRType(dst_ty);
         VG_(tool_panic)("mkPCastTo(2)");
   }
}

/* --------- Accurate interpretation of CmpEQ/CmpNE. --------- */
/* 
   Normally, we can do CmpEQ/CmpNE by doing UifU on the arguments, and
   PCasting to Ity_U1.  However, sometimes it is necessary to be more
   accurate.  The insight is that the result is defined if two
   corresponding bits can be found, one from each argument, so that
   both bits are defined but are different -- that makes EQ say "No"
   and NE say "Yes".  Hence, we compute an improvement term and DifD
   it onto the "normal" (UifU) result.

   The result is:

   PCastTo<1> (
      -- naive version
      PCastTo<sz>( UifU<sz>(vxx, vyy) )

      `DifD<sz>`

      -- improvement term
      PCastTo<sz>( PCast<sz>( CmpEQ<sz> ( vec, 1...1 ) ) )
   )

   where
     vec contains 0 (defined) bits where the corresponding arg bits 
     are defined but different, and 1 bits otherwise.

     vec = Or<sz>( vxx,   // 0 iff bit defined
                   vyy,   // 0 iff bit defined
                   Not<sz>(Xor<sz>( xx, yy )) // 0 iff bits different
                 )
                    
     If any bit of vec is 0, the result is defined and so the 
     improvement term should produce 0...0, else it should produce
     1...1.

     Hence require for the improvement term:

        if vec == 1...1 then 1...1 else 0...0
     ->
        PCast<sz>( CmpEQ<sz> ( vec, 1...1 ) )

   This was extensively re-analysed and checked on 6 July 05.
*/
static IRAtom* expensiveCmpEQorNE ( MCEnv*  mce,
                                    IRType  ty,
                                    IRAtom* vxx, IRAtom* vyy, 
                                    IRAtom* xx,  IRAtom* yy )
{
   IRAtom *naive, *vec, *improvement_term;
   IRAtom *improved, *final_cast, *top;
   IROp   opDIFD, opUIFU, opXOR, opNOT, opCMP, opOR;

   tl_assert(isShadowAtom(mce,vxx));
   tl_assert(isShadowAtom(mce,vyy));
   tl_assert(isOriginalAtom(mce,xx));
   tl_assert(isOriginalAtom(mce,yy));
   tl_assert(sameKindedAtoms(vxx,xx));
   tl_assert(sameKindedAtoms(vyy,yy));
 
   switch (ty) {
      case Ity_I32:
         opOR   = Iop_Or32;
         opDIFD = Iop_And32;
         opUIFU = Iop_Or32;
         opNOT  = Iop_Not32;
         opXOR  = Iop_Xor32;
         opCMP  = Iop_CmpEQ32;
         top    = mkU32(0xFFFFFFFF);
         break;
      case Ity_I64:
         opOR   = Iop_Or64;
         opDIFD = Iop_And64;
         opUIFU = Iop_Or64;
         opNOT  = Iop_Not64;
         opXOR  = Iop_Xor64;
         opCMP  = Iop_CmpEQ64;
         top    = mkU64(0xFFFFFFFFFFFFFFFFULL);
         break;
      default:
         VG_(tool_panic)("expensiveCmpEQorNE");
   }

   naive 
      = mkPCastTo(mce,ty,
                  assignNew('V', mce, ty, binop(opUIFU, vxx, vyy)));

   vec 
      = assignNew(
           'V', mce,ty, 
           binop( opOR,
                  assignNew('V', mce,ty, binop(opOR, vxx, vyy)),
                  assignNew(
                     'V', mce,ty, 
                     unop( opNOT,
                           assignNew('V', mce,ty, binop(opXOR, xx, yy))))));

   improvement_term
      = mkPCastTo( mce,ty,
                   assignNew('V', mce,Ity_I1, binop(opCMP, vec, top)));

   improved
      = assignNew( 'V', mce,ty, binop(opDIFD, naive, improvement_term) );

   final_cast
      = mkPCastTo( mce, Ity_I1, improved );

   return final_cast;
}


/* --------- Semi-accurate interpretation of CmpORD. --------- */

/* CmpORD32{S,U} does PowerPC-style 3-way comparisons:

      CmpORD32S(x,y) = 1<<3   if  x <s y
                     = 1<<2   if  x >s y
                     = 1<<1   if  x == y

   and similarly the unsigned variant.  The default interpretation is:

      CmpORD32{S,U}#(x,y,x#,y#) = PCast(x# `UifU` y#)  
                                  & (7<<1)

   The "& (7<<1)" reflects the fact that all result bits except 3,2,1
   are zero and therefore defined (viz, zero).

   Also deal with a special case better:

      CmpORD32S(x,0)

   Here, bit 3 (LT) of the result is a copy of the top bit of x and
   will be defined even if the rest of x isn't.  In which case we do:

      CmpORD32S#(x,x#,0,{impliedly 0}#)
         = PCast(x#) & (3<<1)      -- standard interp for GT#,EQ#
           | (x# >>u 31) << 3      -- LT# = x#[31]

   Analogous handling for CmpORD64{S,U}.
*/
static Bool isZeroU32 ( IRAtom* e )
{
   return
      toBool( e->tag == Iex_Const
              && e->Iex.Const.con->tag == Ico_U32
              && e->Iex.Const.con->Ico.U32 == 0 );
}

static Bool isZeroU64 ( IRAtom* e )
{
   return
      toBool( e->tag == Iex_Const
              && e->Iex.Const.con->tag == Ico_U64
              && e->Iex.Const.con->Ico.U64 == 0 );
}

static IRAtom* doCmpORD ( MCEnv*  mce,
                          IROp    cmp_op,
                          IRAtom* xxhash, IRAtom* yyhash, 
                          IRAtom* xx,     IRAtom* yy )
{
   Bool   m64    = cmp_op == Iop_CmpORD64S || cmp_op == Iop_CmpORD64U;
   Bool   syned  = cmp_op == Iop_CmpORD64S || cmp_op == Iop_CmpORD32S;
   IROp   opOR   = m64 ? Iop_Or64  : Iop_Or32;
   IROp   opAND  = m64 ? Iop_And64 : Iop_And32;
   IROp   opSHL  = m64 ? Iop_Shl64 : Iop_Shl32;
   IROp   opSHR  = m64 ? Iop_Shr64 : Iop_Shr32;
   IRType ty     = m64 ? Ity_I64   : Ity_I32;
   Int    width  = m64 ? 64        : 32;

   Bool (*isZero)(IRAtom*) = m64 ? isZeroU64 : isZeroU32;

   IRAtom* threeLeft1 = NULL;
   IRAtom* sevenLeft1 = NULL;

   tl_assert(isShadowAtom(mce,xxhash));
   tl_assert(isShadowAtom(mce,yyhash));
   tl_assert(isOriginalAtom(mce,xx));
   tl_assert(isOriginalAtom(mce,yy));
   tl_assert(sameKindedAtoms(xxhash,xx));
   tl_assert(sameKindedAtoms(yyhash,yy));
   tl_assert(cmp_op == Iop_CmpORD32S || cmp_op == Iop_CmpORD32U
             || cmp_op == Iop_CmpORD64S || cmp_op == Iop_CmpORD64U);

   if (0) {
      ppIROp(cmp_op); VG_(printf)(" "); 
      ppIRExpr(xx); VG_(printf)(" "); ppIRExpr( yy ); VG_(printf)("\n");
   }

   if (syned && isZero(yy)) {
      /* fancy interpretation */
      /* if yy is zero, then it must be fully defined (zero#). */
      tl_assert(isZero(yyhash));
      threeLeft1 = m64 ? mkU64(3<<1) : mkU32(3<<1);
      return
         binop(
            opOR,
            assignNew(
               'V', mce,ty,
               binop(
                  opAND,
                  mkPCastTo(mce,ty, xxhash), 
                  threeLeft1
               )),
            assignNew(
               'V', mce,ty,
               binop(
                  opSHL,
                  assignNew(
                     'V', mce,ty,
                     binop(opSHR, xxhash, mkU8(width-1))),
                  mkU8(3)
               ))
	 );
   } else {
      /* standard interpretation */
      sevenLeft1 = m64 ? mkU64(7<<1) : mkU32(7<<1);
      return 
         binop( 
            opAND, 
            mkPCastTo( mce,ty,
                       mkUifU(mce,ty, xxhash,yyhash)),
            sevenLeft1
         );
   }
}


/*------------------------------------------------------------*/
/*--- Emit a test and complaint if something is undefined. ---*/
/*------------------------------------------------------------*/

static IRAtom* schemeE ( MCEnv* mce, IRExpr* e ); /* fwds */


/* Set the annotations on a dirty helper to indicate that the stack
   pointer and instruction pointers might be read.  This is the
   behaviour of all 'emit-a-complaint' style functions we might
   call. */

static void setHelperAnns ( MCEnv* mce, IRDirty* di ) {
   di->nFxState = 2;
   di->fxState[0].fx     = Ifx_Read;
   di->fxState[0].offset = mce->layout->offset_SP;
   di->fxState[0].size   = mce->layout->sizeof_SP;
   di->fxState[1].fx     = Ifx_Read;
   di->fxState[1].offset = mce->layout->offset_IP;
   di->fxState[1].size   = mce->layout->sizeof_IP;
}


/* Check the supplied **original** atom for undefinedness, and emit a
   complaint if so.  Once that happens, mark it as defined.  This is
   possible because the atom is either a tmp or literal.  If it's a
   tmp, it will be shadowed by a tmp, and so we can set the shadow to
   be defined.  In fact as mentioned above, we will have to allocate a
   new tmp to carry the new 'defined' shadow value, and update the
   original->tmp mapping accordingly; we cannot simply assign a new
   value to an existing shadow tmp as this breaks SSAness -- resulting
   in the post-instrumentation sanity checker spluttering in disapproval. 
*/
static void complainIfUndefined ( MCEnv* mce, IRAtom* atom )
{
   IRAtom*  vatom;
   IRType   ty;
   Int      sz;
   IRDirty* di;
   IRAtom*  cond;
   IRAtom*  origin;
   void*    fn;
   HChar*   nm;
   IRExpr** args;
   Int      nargs;

   // Don't do V bit tests if we're not reporting undefined value errors.
   if (MC_(clo_mc_level) == 1)
      return;

   /* Since the original expression is atomic, there's no duplicated
      work generated by making multiple V-expressions for it.  So we
      don't really care about the possibility that someone else may
      also create a V-interpretion for it. */
   tl_assert(isOriginalAtom(mce, atom));
   vatom = expr2vbits( mce, atom );
   tl_assert(isShadowAtom(mce, vatom));
   tl_assert(sameKindedAtoms(atom, vatom));

   ty = typeOfIRExpr(mce->bb->tyenv, vatom);

   /* sz is only used for constructing the error message */
   sz = ty==Ity_I1 ? 0 : sizeofIRType(ty);

   cond = mkPCastTo( mce, Ity_I1, vatom );
   /* cond will be 0 if all defined, and 1 if any not defined. */

   /* Get the origin info for the value we are about to check.  At
      least, if we are doing origin tracking.  If not, use a dummy
      zero origin. */
   if (MC_(clo_mc_level) == 3) {
      origin = schemeE( mce, atom );
      if (mce->hWordTy == Ity_I64) {
         origin = assignNew( 'B', mce, Ity_I64, unop(Iop_32Uto64, origin) );
      }
   } else {
      origin = NULL;
   }

   fn    = NULL;
   nm    = NULL;
   args  = NULL;
   nargs = -1;

   switch (sz) {
      case 0:
         if (origin) {
            fn    = &MC_(helperc_value_check0_fail_w_o);
            nm    = "MC_(helperc_value_check0_fail_w_o)";
            args  = mkIRExprVec_1(origin);
            nargs = 1;
         } else {
            fn    = &MC_(helperc_value_check0_fail_no_o);
            nm    = "MC_(helperc_value_check0_fail_no_o)";
            args  = mkIRExprVec_0();
            nargs = 0;
         }
         break;
      case 1:
         if (origin) {
            fn    = &MC_(helperc_value_check1_fail_w_o);
            nm    = "MC_(helperc_value_check1_fail_w_o)";
            args  = mkIRExprVec_1(origin);
            nargs = 1;
         } else {
            fn    = &MC_(helperc_value_check1_fail_no_o);
            nm    = "MC_(helperc_value_check1_fail_no_o)";
            args  = mkIRExprVec_0();
            nargs = 0;
         }
         break;
      case 4:
         if (origin) {
            fn    = &MC_(helperc_value_check4_fail_w_o);
            nm    = "MC_(helperc_value_check4_fail_w_o)";
            args  = mkIRExprVec_1(origin);
            nargs = 1;
         } else {
            fn    = &MC_(helperc_value_check4_fail_no_o);
            nm    = "MC_(helperc_value_check4_fail_no_o)";
            args  = mkIRExprVec_0();
            nargs = 0;
         }
         break;
      case 8:
         if (origin) {
            fn    = &MC_(helperc_value_check8_fail_w_o);
            nm    = "MC_(helperc_value_check8_fail_w_o)";
            args  = mkIRExprVec_1(origin);
            nargs = 1;
         } else {
            fn    = &MC_(helperc_value_check8_fail_no_o);
            nm    = "MC_(helperc_value_check8_fail_no_o)";
            args  = mkIRExprVec_0();
            nargs = 0;
         }
         break;
      case 2:
      case 16:
         if (origin) {
            fn    = &MC_(helperc_value_checkN_fail_w_o);
            nm    = "MC_(helperc_value_checkN_fail_w_o)";
            args  = mkIRExprVec_2( mkIRExpr_HWord( sz ), origin);
            nargs = 2;
         } else {
            fn    = &MC_(helperc_value_checkN_fail_no_o);
            nm    = "MC_(helperc_value_checkN_fail_no_o)";
            args  = mkIRExprVec_1( mkIRExpr_HWord( sz ) );
            nargs = 1;
         }
         break;
      default:
         VG_(tool_panic)("unexpected szB");
   }

   tl_assert(fn);
   tl_assert(nm);
   tl_assert(args);
   tl_assert(nargs >= 0 && nargs <= 2);
   tl_assert( (MC_(clo_mc_level) == 3 && origin != NULL)
              || (MC_(clo_mc_level) == 2 && origin == NULL) );

   di = unsafeIRDirty_0_N( nargs/*regparms*/, nm, 
                           VG_(fnptr_to_fnentry)( fn ), args );
   di->guard = cond;
   setHelperAnns( mce, di );
   stmt( 'V', mce, IRStmt_Dirty(di));

   /* Set the shadow tmp to be defined.  First, update the
      orig->shadow tmp mapping to reflect the fact that this shadow is
      getting a new value. */
   tl_assert(isIRAtom(vatom));
   /* sameKindedAtoms ... */
   if (vatom->tag == Iex_RdTmp) {
      tl_assert(atom->tag == Iex_RdTmp);
      newShadowTmpV(mce, atom->Iex.RdTmp.tmp);
      assign('V', mce, findShadowTmpV(mce, atom->Iex.RdTmp.tmp), 
                       definedOfType(ty));
   }
}


/*------------------------------------------------------------*/
/*--- Shadowing PUTs/GETs, and indexed variants thereof    ---*/
/*------------------------------------------------------------*/

/* Examine the always-defined sections declared in layout to see if
   the (offset,size) section is within one.  Note, is is an error to
   partially fall into such a region: (offset,size) should either be
   completely in such a region or completely not-in such a region.  
*/
static Bool isAlwaysDefd ( MCEnv* mce, Int offset, Int size )
{
   Int minoffD, maxoffD, i;
   Int minoff = offset;
   Int maxoff = minoff + size - 1;
   tl_assert((minoff & ~0xFFFF) == 0);
   tl_assert((maxoff & ~0xFFFF) == 0);

   for (i = 0; i < mce->layout->n_alwaysDefd; i++) {
      minoffD = mce->layout->alwaysDefd[i].offset;
      maxoffD = minoffD + mce->layout->alwaysDefd[i].size - 1;
      tl_assert((minoffD & ~0xFFFF) == 0);
      tl_assert((maxoffD & ~0xFFFF) == 0);

      if (maxoff < minoffD || maxoffD < minoff)
         continue; /* no overlap */
      if (minoff >= minoffD && maxoff <= maxoffD)
         return True; /* completely contained in an always-defd section */

      VG_(tool_panic)("memcheck:isAlwaysDefd:partial overlap");
   }
   return False; /* could not find any containing section */
}


/* Generate into bb suitable actions to shadow this Put.  If the state
   slice is marked 'always defined', do nothing.  Otherwise, write the
   supplied V bits to the shadow state.  We can pass in either an
   original atom or a V-atom, but not both.  In the former case the
   relevant V-bits are then generated from the original.
*/
static
void do_shadow_PUT ( MCEnv* mce,  Int offset, 
                     IRAtom* atom, IRAtom* vatom )
{
   IRType ty;

   // Don't do shadow PUTs if we're not doing undefined value checking.
   // Their absence lets Vex's optimiser remove all the shadow computation
   // that they depend on, which includes GETs of the shadow registers.
   if (MC_(clo_mc_level) == 1)
      return;
   
   if (atom) {
      tl_assert(!vatom);
      tl_assert(isOriginalAtom(mce, atom));
      vatom = expr2vbits( mce, atom );
   } else {
      tl_assert(vatom);
      tl_assert(isShadowAtom(mce, vatom));
   }

   ty = typeOfIRExpr(mce->bb->tyenv, vatom);
   tl_assert(ty != Ity_I1);
   if (isAlwaysDefd(mce, offset, sizeofIRType(ty))) {
      /* later: no ... */
      /* emit code to emit a complaint if any of the vbits are 1. */
      /* complainIfUndefined(mce, atom); */
   } else {
      /* Do a plain shadow Put. */
      stmt( 'V', mce, IRStmt_Put( offset + mce->layout->total_sizeB, vatom ) );
   }
}


/* Return an expression which contains the V bits corresponding to the
   given GETI (passed in in pieces). 
*/
static
void do_shadow_PUTI ( MCEnv* mce, 
                      IRRegArray* descr, 
                      IRAtom* ix, Int bias, IRAtom* atom )
{
   IRAtom* vatom;
   IRType  ty, tyS;
   Int     arrSize;;

   // Don't do shadow PUTIs if we're not doing undefined value checking.
   // Their absence lets Vex's optimiser remove all the shadow computation
   // that they depend on, which includes GETIs of the shadow registers.
   if (MC_(clo_mc_level) == 1)
      return;
   
   tl_assert(isOriginalAtom(mce,atom));
   vatom = expr2vbits( mce, atom );
   tl_assert(sameKindedAtoms(atom, vatom));
   ty   = descr->elemTy;
   tyS  = shadowTypeV(ty);
   arrSize = descr->nElems * sizeofIRType(ty);
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom(mce,ix));
   complainIfUndefined(mce,ix);
   if (isAlwaysDefd(mce, descr->base, arrSize)) {
      /* later: no ... */
      /* emit code to emit a complaint if any of the vbits are 1. */
      /* complainIfUndefined(mce, atom); */
   } else {
      /* Do a cloned version of the Put that refers to the shadow
         area. */
      IRRegArray* new_descr 
         = mkIRRegArray( descr->base + mce->layout->total_sizeB, 
                         tyS, descr->nElems);
      stmt( 'V', mce, IRStmt_PutI( new_descr, ix, bias, vatom ));
   }
}


/* Return an expression which contains the V bits corresponding to the
   given GET (passed in in pieces). 
*/
static 
IRExpr* shadow_GET ( MCEnv* mce, Int offset, IRType ty )
{
   IRType tyS = shadowTypeV(ty);
   tl_assert(ty != Ity_I1);
   if (isAlwaysDefd(mce, offset, sizeofIRType(ty))) {
      /* Always defined, return all zeroes of the relevant type */
      return definedOfType(tyS);
   } else {
      /* return a cloned version of the Get that refers to the shadow
         area. */
      /* FIXME: this isn't an atom! */
      return IRExpr_Get( offset + mce->layout->total_sizeB, tyS );
   }
}


/* Return an expression which contains the V bits corresponding to the
   given GETI (passed in in pieces). 
*/
static
IRExpr* shadow_GETI ( MCEnv* mce, 
                      IRRegArray* descr, IRAtom* ix, Int bias )
{
   IRType ty   = descr->elemTy;
   IRType tyS  = shadowTypeV(ty);
   Int arrSize = descr->nElems * sizeofIRType(ty);
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom(mce,ix));
   complainIfUndefined(mce,ix);
   if (isAlwaysDefd(mce, descr->base, arrSize)) {
      /* Always defined, return all zeroes of the relevant type */
      return definedOfType(tyS);
   } else {
      /* return a cloned version of the Get that refers to the shadow
         area. */
      IRRegArray* new_descr 
         = mkIRRegArray( descr->base + mce->layout->total_sizeB, 
                         tyS, descr->nElems);
      return IRExpr_GetI( new_descr, ix, bias );
   }
}


/*------------------------------------------------------------*/
/*--- Generating approximations for unknown operations,    ---*/
/*--- using lazy-propagate semantics                       ---*/
/*------------------------------------------------------------*/

/* Lazy propagation of undefinedness from two values, resulting in the
   specified shadow type. 
*/
static
IRAtom* mkLazy2 ( MCEnv* mce, IRType finalVty, IRAtom* va1, IRAtom* va2 )
{
   IRAtom* at;
   IRType t1 = typeOfIRExpr(mce->bb->tyenv, va1);
   IRType t2 = typeOfIRExpr(mce->bb->tyenv, va2);
   tl_assert(isShadowAtom(mce,va1));
   tl_assert(isShadowAtom(mce,va2));

   /* The general case is inefficient because PCast is an expensive
      operation.  Here are some special cases which use PCast only
      once rather than twice. */

   /* I64 x I64 -> I64 */
   if (t1 == Ity_I64 && t2 == Ity_I64 && finalVty == Ity_I64) {
      if (0) VG_(printf)("mkLazy2: I64 x I64 -> I64\n");
      at = mkUifU(mce, Ity_I64, va1, va2);
      at = mkPCastTo(mce, Ity_I64, at);
      return at;
   }

   /* I64 x I64 -> I32 */
   if (t1 == Ity_I64 && t2 == Ity_I64 && finalVty == Ity_I32) {
      if (0) VG_(printf)("mkLazy2: I64 x I64 -> I32\n");
      at = mkUifU(mce, Ity_I64, va1, va2);
      at = mkPCastTo(mce, Ity_I32, at);
      return at;
   }

   if (0) {
      VG_(printf)("mkLazy2 ");
      ppIRType(t1);
      VG_(printf)("_");
      ppIRType(t2);
      VG_(printf)("_");
      ppIRType(finalVty);
      VG_(printf)("\n");
   }

   /* General case: force everything via 32-bit intermediaries. */
   at = mkPCastTo(mce, Ity_I32, va1);
   at = mkUifU(mce, Ity_I32, at, mkPCastTo(mce, Ity_I32, va2));
   at = mkPCastTo(mce, finalVty, at);
   return at;
}


/* 3-arg version of the above. */
static
IRAtom* mkLazy3 ( MCEnv* mce, IRType finalVty, 
                  IRAtom* va1, IRAtom* va2, IRAtom* va3 )
{
   IRAtom* at;
   IRType t1 = typeOfIRExpr(mce->bb->tyenv, va1);
   IRType t2 = typeOfIRExpr(mce->bb->tyenv, va2);
   IRType t3 = typeOfIRExpr(mce->bb->tyenv, va3);
   tl_assert(isShadowAtom(mce,va1));
   tl_assert(isShadowAtom(mce,va2));
   tl_assert(isShadowAtom(mce,va3));

   /* The general case is inefficient because PCast is an expensive
      operation.  Here are some special cases which use PCast only
      twice rather than three times. */

   /* I32 x I64 x I64 -> I64 */
   /* Standard FP idiom: rm x FParg1 x FParg2 -> FPresult */
   if (t1 == Ity_I32 && t2 == Ity_I64 && t3 == Ity_I64 
       && finalVty == Ity_I64) {
      if (0) VG_(printf)("mkLazy3: I32 x I64 x I64 -> I64\n");
      /* Widen 1st arg to I64.  Since 1st arg is typically a rounding
         mode indication which is fully defined, this should get
         folded out later. */
      at = mkPCastTo(mce, Ity_I64, va1);
      /* Now fold in 2nd and 3rd args. */
      at = mkUifU(mce, Ity_I64, at, va2);
      at = mkUifU(mce, Ity_I64, at, va3);
      /* and PCast once again. */
      at = mkPCastTo(mce, Ity_I64, at);
      return at;
   }

   /* I32 x I64 x I64 -> I32 */
   if (t1 == Ity_I32 && t2 == Ity_I64 && t3 == Ity_I64 
       && finalVty == Ity_I32) {
      if (0) VG_(printf)("mkLazy3: I32 x I64 x I64 -> I64\n");
      at = mkPCastTo(mce, Ity_I64, va1);
      at = mkUifU(mce, Ity_I64, at, va2);
      at = mkUifU(mce, Ity_I64, at, va3);
      at = mkPCastTo(mce, Ity_I32, at);
      return at;
   }

   if (1) {
      VG_(printf)("mkLazy3: ");
      ppIRType(t1);
      VG_(printf)(" x ");
      ppIRType(t2);
      VG_(printf)(" x ");
      ppIRType(t3);
      VG_(printf)(" -> ");
      ppIRType(finalVty);
      VG_(printf)("\n");
   }

   tl_assert(0);
   /* General case: force everything via 32-bit intermediaries. */
   /*
   at = mkPCastTo(mce, Ity_I32, va1);
   at = mkUifU(mce, Ity_I32, at, mkPCastTo(mce, Ity_I32, va2));
   at = mkUifU(mce, Ity_I32, at, mkPCastTo(mce, Ity_I32, va3));
   at = mkPCastTo(mce, finalVty, at);
   return at;
   */
}


/* 4-arg version of the above. */
static
IRAtom* mkLazy4 ( MCEnv* mce, IRType finalVty, 
                  IRAtom* va1, IRAtom* va2, IRAtom* va3, IRAtom* va4 )
{
   IRAtom* at;
   IRType t1 = typeOfIRExpr(mce->bb->tyenv, va1);
   IRType t2 = typeOfIRExpr(mce->bb->tyenv, va2);
   IRType t3 = typeOfIRExpr(mce->bb->tyenv, va3);
   IRType t4 = typeOfIRExpr(mce->bb->tyenv, va4);
   tl_assert(isShadowAtom(mce,va1));
   tl_assert(isShadowAtom(mce,va2));
   tl_assert(isShadowAtom(mce,va3));
   tl_assert(isShadowAtom(mce,va4));

   /* The general case is inefficient because PCast is an expensive
      operation.  Here are some special cases which use PCast only
      twice rather than three times. */

   /* I32 x I64 x I64 x I64 -> I64 */
   /* Standard FP idiom: rm x FParg1 x FParg2 x FParg3 -> FPresult */
   if (t1 == Ity_I32 && t2 == Ity_I64 && t3 == Ity_I64 && t4 == Ity_I64
       && finalVty == Ity_I64) {
      if (0) VG_(printf)("mkLazy4: I32 x I64 x I64 x I64 -> I64\n");
      /* Widen 1st arg to I64.  Since 1st arg is typically a rounding
         mode indication which is fully defined, this should get
         folded out later. */
      at = mkPCastTo(mce, Ity_I64, va1);
      /* Now fold in 2nd, 3rd, 4th args. */
      at = mkUifU(mce, Ity_I64, at, va2);
      at = mkUifU(mce, Ity_I64, at, va3);
      at = mkUifU(mce, Ity_I64, at, va4);
      /* and PCast once again. */
      at = mkPCastTo(mce, Ity_I64, at);
      return at;
   }

   if (1) {
      VG_(printf)("mkLazy4: ");
      ppIRType(t1);
      VG_(printf)(" x ");
      ppIRType(t2);
      VG_(printf)(" x ");
      ppIRType(t3);
      VG_(printf)(" x ");
      ppIRType(t4);
      VG_(printf)(" -> ");
      ppIRType(finalVty);
      VG_(printf)("\n");
   }

   tl_assert(0);
}


/* Do the lazy propagation game from a null-terminated vector of
   atoms.  This is presumably the arguments to a helper call, so the
   IRCallee info is also supplied in order that we can know which
   arguments should be ignored (via the .mcx_mask field). 
*/
static
IRAtom* mkLazyN ( MCEnv* mce, 
                  IRAtom** exprvec, IRType finalVtype, IRCallee* cee )
{
   Int     i;
   IRAtom* here;
   IRAtom* curr;
   IRType  mergeTy;
   IRType  mergeTy64 = True;

   /* Decide on the type of the merge intermediary.  If all relevant
      args are I64, then it's I64.  In all other circumstances, use
      I32. */
   for (i = 0; exprvec[i]; i++) {
      tl_assert(i < 32);
      tl_assert(isOriginalAtom(mce, exprvec[i]));
      if (cee->mcx_mask & (1<<i))
         continue;
      if (typeOfIRExpr(mce->bb->tyenv, exprvec[i]) != Ity_I64)
         mergeTy64 = False;
   }

   mergeTy = mergeTy64  ? Ity_I64  : Ity_I32;
   curr    = definedOfType(mergeTy);

   for (i = 0; exprvec[i]; i++) {
      tl_assert(i < 32);
      tl_assert(isOriginalAtom(mce, exprvec[i]));
      /* Only take notice of this arg if the callee's mc-exclusion
         mask does not say it is to be excluded. */
      if (cee->mcx_mask & (1<<i)) {
         /* the arg is to be excluded from definedness checking.  Do
            nothing. */
         if (0) VG_(printf)("excluding %s(%d)\n", cee->name, i);
      } else {
         /* calculate the arg's definedness, and pessimistically merge
            it in. */
         here = mkPCastTo( mce, mergeTy, expr2vbits(mce, exprvec[i]) );
         curr = mergeTy64 
                   ? mkUifU64(mce, here, curr)
                   : mkUifU32(mce, here, curr);
      }
   }
   return mkPCastTo(mce, finalVtype, curr );
}


/*------------------------------------------------------------*/
/*--- Generating expensive sequences for exact carry-chain ---*/
/*--- propagation in add/sub and related operations.       ---*/
/*------------------------------------------------------------*/

static
IRAtom* expensiveAddSub ( MCEnv*  mce,
                          Bool    add,
                          IRType  ty,
                          IRAtom* qaa, IRAtom* qbb, 
                          IRAtom* aa,  IRAtom* bb )
{
   IRAtom *a_min, *b_min, *a_max, *b_max;
   IROp   opAND, opOR, opXOR, opNOT, opADD, opSUB;

   tl_assert(isShadowAtom(mce,qaa));
   tl_assert(isShadowAtom(mce,qbb));
   tl_assert(isOriginalAtom(mce,aa));
   tl_assert(isOriginalAtom(mce,bb));
   tl_assert(sameKindedAtoms(qaa,aa));
   tl_assert(sameKindedAtoms(qbb,bb));

   switch (ty) {
      case Ity_I32:
         opAND = Iop_And32;
         opOR  = Iop_Or32;
         opXOR = Iop_Xor32;
         opNOT = Iop_Not32;
         opADD = Iop_Add32;
         opSUB = Iop_Sub32;
         break;
      case Ity_I64:
         opAND = Iop_And64;
         opOR  = Iop_Or64;
         opXOR = Iop_Xor64;
         opNOT = Iop_Not64;
         opADD = Iop_Add64;
         opSUB = Iop_Sub64;
         break;
      default:
         VG_(tool_panic)("expensiveAddSub");
   }

   // a_min = aa & ~qaa
   a_min = assignNew('V', mce,ty, 
                     binop(opAND, aa,
                                  assignNew('V', mce,ty, unop(opNOT, qaa))));

   // b_min = bb & ~qbb
   b_min = assignNew('V', mce,ty, 
                     binop(opAND, bb,
                                  assignNew('V', mce,ty, unop(opNOT, qbb))));

   // a_max = aa | qaa
   a_max = assignNew('V', mce,ty, binop(opOR, aa, qaa));

   // b_max = bb | qbb
   b_max = assignNew('V', mce,ty, binop(opOR, bb, qbb));

   if (add) {
      // result = (qaa | qbb) | ((a_min + b_min) ^ (a_max + b_max))
      return
      assignNew('V', mce,ty,
         binop( opOR,
                assignNew('V', mce,ty, binop(opOR, qaa, qbb)),
                assignNew('V', mce,ty, 
                   binop( opXOR, 
                          assignNew('V', mce,ty, binop(opADD, a_min, b_min)),
                          assignNew('V', mce,ty, binop(opADD, a_max, b_max))
                   )
                )
         )
      );
   } else {
      // result = (qaa | qbb) | ((a_min - b_max) ^ (a_max + b_min))
      return
      assignNew('V', mce,ty,
         binop( opOR,
                assignNew('V', mce,ty, binop(opOR, qaa, qbb)),
                assignNew('V', mce,ty, 
                   binop( opXOR, 
                          assignNew('V', mce,ty, binop(opSUB, a_min, b_max)),
                          assignNew('V', mce,ty, binop(opSUB, a_max, b_min))
                   )
                )
         )
      );
   }

}


/*------------------------------------------------------------*/
/*--- Scalar shifts.                                       ---*/
/*------------------------------------------------------------*/

/* Produce an interpretation for (aa << bb) (or >>s, >>u).  The basic
   idea is to shift the definedness bits by the original shift amount.
   This introduces 0s ("defined") in new positions for left shifts and
   unsigned right shifts, and copies the top definedness bit for
   signed right shifts.  So, conveniently, applying the original shift
   operator to the definedness bits for the left arg is exactly the
   right thing to do:

      (qaa << bb)

   However if the shift amount is undefined then the whole result
   is undefined.  Hence need:

      (qaa << bb) `UifU` PCast(qbb)

   If the shift amount bb is a literal than qbb will say 'all defined'
   and the UifU and PCast will get folded out by post-instrumentation
   optimisation.
*/
static IRAtom* scalarShift ( MCEnv*  mce,
                             IRType  ty,
                             IROp    original_op,
                             IRAtom* qaa, IRAtom* qbb, 
                             IRAtom* aa,  IRAtom* bb )
{
   tl_assert(isShadowAtom(mce,qaa));
   tl_assert(isShadowAtom(mce,qbb));
   tl_assert(isOriginalAtom(mce,aa));
   tl_assert(isOriginalAtom(mce,bb));
   tl_assert(sameKindedAtoms(qaa,aa));
   tl_assert(sameKindedAtoms(qbb,bb));
   return 
      assignNew(
         'V', mce, ty,
         mkUifU( mce, ty,
                 assignNew('V', mce, ty, binop(original_op, qaa, bb)),
                 mkPCastTo(mce, ty, qbb)
         )
   );
}


/*------------------------------------------------------------*/
/*--- Helpers for dealing with vector primops.             ---*/
/*------------------------------------------------------------*/

/* Vector pessimisation -- pessimise within each lane individually. */

static IRAtom* mkPCast8x16 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_V128, unop(Iop_CmpNEZ8x16, at));
}

static IRAtom* mkPCast16x8 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_V128, unop(Iop_CmpNEZ16x8, at));
}

static IRAtom* mkPCast32x4 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_V128, unop(Iop_CmpNEZ32x4, at));
}

static IRAtom* mkPCast64x2 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_V128, unop(Iop_CmpNEZ64x2, at));
}

static IRAtom* mkPCast32x2 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_I64, unop(Iop_CmpNEZ32x2, at));
}

static IRAtom* mkPCast16x4 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_I64, unop(Iop_CmpNEZ16x4, at));
}

static IRAtom* mkPCast8x8 ( MCEnv* mce, IRAtom* at )
{
   return assignNew('V', mce, Ity_I64, unop(Iop_CmpNEZ8x8, at));
}


/* Here's a simple scheme capable of handling ops derived from SSE1
   code and while only generating ops that can be efficiently
   implemented in SSE1. */

/* All-lanes versions are straightforward:

   binary32Fx4(x,y)   ==> PCast32x4(UifUV128(x#,y#))

   unary32Fx4(x,y)    ==> PCast32x4(x#)

   Lowest-lane-only versions are more complex:

   binary32F0x4(x,y)  ==> SetV128lo32(
                             x#, 
                             PCast32(V128to32(UifUV128(x#,y#))) 
                          )

   This is perhaps not so obvious.  In particular, it's faster to
   do a V128-bit UifU and then take the bottom 32 bits than the more
   obvious scheme of taking the bottom 32 bits of each operand
   and doing a 32-bit UifU.  Basically since UifU is fast and 
   chopping lanes off vector values is slow.

   Finally:

   unary32F0x4(x)     ==> SetV128lo32(
                             x#, 
                             PCast32(V128to32(x#)) 
                          )

   Where:

   PCast32(v#)   = 1Sto32(CmpNE32(v#,0))
   PCast32x4(v#) = CmpNEZ32x4(v#)
*/

static
IRAtom* binary32Fx4 ( MCEnv* mce, IRAtom* vatomX, IRAtom* vatomY )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   tl_assert(isShadowAtom(mce, vatomY));
   at = mkUifUV128(mce, vatomX, vatomY);
   at = assignNew('V', mce, Ity_V128, mkPCast32x4(mce, at));
   return at;
}

static
IRAtom* unary32Fx4 ( MCEnv* mce, IRAtom* vatomX )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   at = assignNew('V', mce, Ity_V128, mkPCast32x4(mce, vatomX));
   return at;
}

static
IRAtom* binary32F0x4 ( MCEnv* mce, IRAtom* vatomX, IRAtom* vatomY )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   tl_assert(isShadowAtom(mce, vatomY));
   at = mkUifUV128(mce, vatomX, vatomY);
   at = assignNew('V', mce, Ity_I32, unop(Iop_V128to32, at));
   at = mkPCastTo(mce, Ity_I32, at);
   at = assignNew('V', mce, Ity_V128, binop(Iop_SetV128lo32, vatomX, at));
   return at;
}

static
IRAtom* unary32F0x4 ( MCEnv* mce, IRAtom* vatomX )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   at = assignNew('V', mce, Ity_I32, unop(Iop_V128to32, vatomX));
   at = mkPCastTo(mce, Ity_I32, at);
   at = assignNew('V', mce, Ity_V128, binop(Iop_SetV128lo32, vatomX, at));
   return at;
}

/* --- ... and ... 64Fx2 versions of the same ... --- */

static
IRAtom* binary64Fx2 ( MCEnv* mce, IRAtom* vatomX, IRAtom* vatomY )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   tl_assert(isShadowAtom(mce, vatomY));
   at = mkUifUV128(mce, vatomX, vatomY);
   at = assignNew('V', mce, Ity_V128, mkPCast64x2(mce, at));
   return at;
}

static
IRAtom* unary64Fx2 ( MCEnv* mce, IRAtom* vatomX )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   at = assignNew('V', mce, Ity_V128, mkPCast64x2(mce, vatomX));
   return at;
}

static
IRAtom* binary64F0x2 ( MCEnv* mce, IRAtom* vatomX, IRAtom* vatomY )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   tl_assert(isShadowAtom(mce, vatomY));
   at = mkUifUV128(mce, vatomX, vatomY);
   at = assignNew('V', mce, Ity_I64, unop(Iop_V128to64, at));
   at = mkPCastTo(mce, Ity_I64, at);
   at = assignNew('V', mce, Ity_V128, binop(Iop_SetV128lo64, vatomX, at));
   return at;
}

static
IRAtom* unary64F0x2 ( MCEnv* mce, IRAtom* vatomX )
{
   IRAtom* at;
   tl_assert(isShadowAtom(mce, vatomX));
   at = assignNew('V', mce, Ity_I64, unop(Iop_V128to64, vatomX));
   at = mkPCastTo(mce, Ity_I64, at);
   at = assignNew('V', mce, Ity_V128, binop(Iop_SetV128lo64, vatomX, at));
   return at;
}

/* --- --- Vector saturated narrowing --- --- */

/* This is quite subtle.  What to do is simple:

   Let the original narrowing op be QNarrowW{S,U}xN.  Produce:

      the-narrowing-op( PCastWxN(vatom1), PCastWxN(vatom2))

   Why this is right is not so simple.  Consider a lane in the args,
   vatom1 or 2, doesn't matter.

   After the PCast, that lane is all 0s (defined) or all
   1s(undefined).

   Both signed and unsigned saturating narrowing of all 0s produces
   all 0s, which is what we want.

   The all-1s case is more complex.  Unsigned narrowing interprets an
   all-1s input as the largest unsigned integer, and so produces all
   1s as a result since that is the largest unsigned value at the
   smaller width.

   Signed narrowing interprets all 1s as -1.  Fortunately, -1 narrows
   to -1, so we still wind up with all 1s at the smaller width.

   So: In short, pessimise the args, then apply the original narrowing
   op.
*/
static
IRAtom* vectorNarrowV128 ( MCEnv* mce, IROp narrow_op, 
                          IRAtom* vatom1, IRAtom* vatom2)
{
   IRAtom *at1, *at2, *at3;
   IRAtom* (*pcast)( MCEnv*, IRAtom* );
   switch (narrow_op) {
      case Iop_QNarrow32Sx4: pcast = mkPCast32x4; break;
      case Iop_QNarrow32Ux4: pcast = mkPCast32x4; break;
      case Iop_QNarrow16Sx8: pcast = mkPCast16x8; break;
      case Iop_QNarrow16Ux8: pcast = mkPCast16x8; break;
      default: VG_(tool_panic)("vectorNarrowV128");
   }
   tl_assert(isShadowAtom(mce,vatom1));
   tl_assert(isShadowAtom(mce,vatom2));
   at1 = assignNew('V', mce, Ity_V128, pcast(mce, vatom1));
   at2 = assignNew('V', mce, Ity_V128, pcast(mce, vatom2));
   at3 = assignNew('V', mce, Ity_V128, binop(narrow_op, at1, at2));
   return at3;
}

static
IRAtom* vectorNarrow64 ( MCEnv* mce, IROp narrow_op, 
                         IRAtom* vatom1, IRAtom* vatom2)
{
   IRAtom *at1, *at2, *at3;
   IRAtom* (*pcast)( MCEnv*, IRAtom* );
   switch (narrow_op) {
      case Iop_QNarrow32Sx2: pcast = mkPCast32x2; break;
      case Iop_QNarrow16Sx4: pcast = mkPCast16x4; break;
      case Iop_QNarrow16Ux4: pcast = mkPCast16x4; break;
      default: VG_(tool_panic)("vectorNarrow64");
   }
   tl_assert(isShadowAtom(mce,vatom1));
   tl_assert(isShadowAtom(mce,vatom2));
   at1 = assignNew('V', mce, Ity_I64, pcast(mce, vatom1));
   at2 = assignNew('V', mce, Ity_I64, pcast(mce, vatom2));
   at3 = assignNew('V', mce, Ity_I64, binop(narrow_op, at1, at2));
   return at3;
}


/* --- --- Vector integer arithmetic --- --- */

/* Simple ... UifU the args and per-lane pessimise the results. */

/* --- V128-bit versions --- */

static
IRAtom* binary8Ix16 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifUV128(mce, vatom1, vatom2);
   at = mkPCast8x16(mce, at);
   return at;   
}

static
IRAtom* binary16Ix8 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifUV128(mce, vatom1, vatom2);
   at = mkPCast16x8(mce, at);
   return at;   
}

static
IRAtom* binary32Ix4 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifUV128(mce, vatom1, vatom2);
   at = mkPCast32x4(mce, at);
   return at;   
}

static
IRAtom* binary64Ix2 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifUV128(mce, vatom1, vatom2);
   at = mkPCast64x2(mce, at);
   return at;   
}

/* --- 64-bit versions --- */

static
IRAtom* binary8Ix8 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifU64(mce, vatom1, vatom2);
   at = mkPCast8x8(mce, at);
   return at;   
}

static
IRAtom* binary16Ix4 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifU64(mce, vatom1, vatom2);
   at = mkPCast16x4(mce, at);
   return at;   
}

static
IRAtom* binary32Ix2 ( MCEnv* mce, IRAtom* vatom1, IRAtom* vatom2 )
{
   IRAtom* at;
   at = mkUifU64(mce, vatom1, vatom2);
   at = mkPCast32x2(mce, at);
   return at;   
}


/*------------------------------------------------------------*/
/*--- Generate shadow values from all kinds of IRExprs.    ---*/
/*------------------------------------------------------------*/

static 
IRAtom* expr2vbits_Qop ( MCEnv* mce,
                         IROp op,
                         IRAtom* atom1, IRAtom* atom2, 
                         IRAtom* atom3, IRAtom* atom4 )
{
   IRAtom* vatom1 = expr2vbits( mce, atom1 );
   IRAtom* vatom2 = expr2vbits( mce, atom2 );
   IRAtom* vatom3 = expr2vbits( mce, atom3 );
   IRAtom* vatom4 = expr2vbits( mce, atom4 );

   tl_assert(isOriginalAtom(mce,atom1));
   tl_assert(isOriginalAtom(mce,atom2));
   tl_assert(isOriginalAtom(mce,atom3));
   tl_assert(isOriginalAtom(mce,atom4));
   tl_assert(isShadowAtom(mce,vatom1));
   tl_assert(isShadowAtom(mce,vatom2));
   tl_assert(isShadowAtom(mce,vatom3));
   tl_assert(isShadowAtom(mce,vatom4));
   tl_assert(sameKindedAtoms(atom1,vatom1));
   tl_assert(sameKindedAtoms(atom2,vatom2));
   tl_assert(sameKindedAtoms(atom3,vatom3));
   tl_assert(sameKindedAtoms(atom4,vatom4));
   switch (op) {
      case Iop_MAddF64:
      case Iop_MAddF64r32:
      case Iop_MSubF64:
      case Iop_MSubF64r32:
         /* I32(rm) x F64 x F64 x F64 -> F64 */
         return mkLazy4(mce, Ity_I64, vatom1, vatom2, vatom3, vatom4);
      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Qop");
   }
}


static 
IRAtom* expr2vbits_Triop ( MCEnv* mce,
                           IROp op,
                           IRAtom* atom1, IRAtom* atom2, IRAtom* atom3 )
{
   IRAtom* vatom1 = expr2vbits( mce, atom1 );
   IRAtom* vatom2 = expr2vbits( mce, atom2 );
   IRAtom* vatom3 = expr2vbits( mce, atom3 );

   tl_assert(isOriginalAtom(mce,atom1));
   tl_assert(isOriginalAtom(mce,atom2));
   tl_assert(isOriginalAtom(mce,atom3));
   tl_assert(isShadowAtom(mce,vatom1));
   tl_assert(isShadowAtom(mce,vatom2));
   tl_assert(isShadowAtom(mce,vatom3));
   tl_assert(sameKindedAtoms(atom1,vatom1));
   tl_assert(sameKindedAtoms(atom2,vatom2));
   tl_assert(sameKindedAtoms(atom3,vatom3));
   switch (op) {
      case Iop_AddF64:
      case Iop_AddF64r32:
      case Iop_SubF64:
      case Iop_SubF64r32:
      case Iop_MulF64:
      case Iop_MulF64r32:
      case Iop_DivF64:
      case Iop_DivF64r32:
      case Iop_ScaleF64:
      case Iop_Yl2xF64:
      case Iop_Yl2xp1F64:
      case Iop_AtanF64:
      case Iop_PRemF64:
      case Iop_PRem1F64:
         /* I32(rm) x F64 x F64 -> F64 */
         return mkLazy3(mce, Ity_I64, vatom1, vatom2, vatom3);
      case Iop_PRemC3210F64:
      case Iop_PRem1C3210F64:
         /* I32(rm) x F64 x F64 -> I32 */
         return mkLazy3(mce, Ity_I32, vatom1, vatom2, vatom3);
      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Triop");
   }
}


static 
IRAtom* expr2vbits_Binop ( MCEnv* mce,
                           IROp op,
                           IRAtom* atom1, IRAtom* atom2 )
{
   IRType  and_or_ty;
   IRAtom* (*uifu)    (MCEnv*, IRAtom*, IRAtom*);
   IRAtom* (*difd)    (MCEnv*, IRAtom*, IRAtom*);
   IRAtom* (*improve) (MCEnv*, IRAtom*, IRAtom*);

   IRAtom* vatom1 = expr2vbits( mce, atom1 );
   IRAtom* vatom2 = expr2vbits( mce, atom2 );

   tl_assert(isOriginalAtom(mce,atom1));
   tl_assert(isOriginalAtom(mce,atom2));
   tl_assert(isShadowAtom(mce,vatom1));
   tl_assert(isShadowAtom(mce,vatom2));
   tl_assert(sameKindedAtoms(atom1,vatom1));
   tl_assert(sameKindedAtoms(atom2,vatom2));
   switch (op) {

      /* 64-bit SIMD */

      case Iop_ShrN16x4:
      case Iop_ShrN32x2:
      case Iop_SarN8x8:
      case Iop_SarN16x4:
      case Iop_SarN32x2:
      case Iop_ShlN16x4:
      case Iop_ShlN32x2:
      case Iop_ShlN8x8:
         /* Same scheme as with all other shifts. */
         complainIfUndefined(mce, atom2);
         return assignNew('V', mce, Ity_I64, binop(op, vatom1, atom2));

      case Iop_QNarrow32Sx2:
      case Iop_QNarrow16Sx4:
      case Iop_QNarrow16Ux4:
         return vectorNarrow64(mce, op, vatom1, vatom2);

      case Iop_Min8Ux8:
      case Iop_Max8Ux8:
      case Iop_Avg8Ux8:
      case Iop_QSub8Sx8:
      case Iop_QSub8Ux8:
      case Iop_Sub8x8:
      case Iop_CmpGT8Sx8:
      case Iop_CmpEQ8x8:
      case Iop_QAdd8Sx8:
      case Iop_QAdd8Ux8:
      case Iop_Add8x8:
         return binary8Ix8(mce, vatom1, vatom2);

      case Iop_Min16Sx4:
      case Iop_Max16Sx4:
      case Iop_Avg16Ux4:
      case Iop_QSub16Ux4:
      case Iop_QSub16Sx4:
      case Iop_Sub16x4:
      case Iop_Mul16x4:
      case Iop_MulHi16Sx4:
      case Iop_MulHi16Ux4:
      case Iop_CmpGT16Sx4:
      case Iop_CmpEQ16x4:
      case Iop_QAdd16Sx4:
      case Iop_QAdd16Ux4:
      case Iop_Add16x4:
         return binary16Ix4(mce, vatom1, vatom2);

      case Iop_Sub32x2:
      case Iop_Mul32x2:
      case Iop_CmpGT32Sx2:
      case Iop_CmpEQ32x2:
      case Iop_Add32x2:
         return binary32Ix2(mce, vatom1, vatom2);

      /* 64-bit data-steering */
      case Iop_InterleaveLO32x2:
      case Iop_InterleaveLO16x4:
      case Iop_InterleaveLO8x8:
      case Iop_InterleaveHI32x2:
      case Iop_InterleaveHI16x4:
      case Iop_InterleaveHI8x8:
      case Iop_CatOddLanes16x4:
      case Iop_CatEvenLanes16x4:
         return assignNew('V', mce, Ity_I64, binop(op, vatom1, vatom2));

      /* Perm8x8: rearrange values in left arg using steering values
        from right arg.  So rearrange the vbits in the same way but
        pessimise wrt steering values. */
      case Iop_Perm8x8:
         return mkUifU64(
                   mce,
                   assignNew('V', mce, Ity_I64, binop(op, vatom1, atom2)),
                   mkPCast8x8(mce, vatom2)
                );

      /* V128-bit SIMD */

      case Iop_ShrN16x8:
      case Iop_ShrN32x4:
      case Iop_ShrN64x2:
      case Iop_SarN16x8:
      case Iop_SarN32x4:
      case Iop_ShlN16x8:
      case Iop_ShlN32x4:
      case Iop_ShlN64x2:
      case Iop_ShlN8x16:
      case Iop_SarN8x16:
         /* Same scheme as with all other shifts.  Note: 22 Oct 05:
            this is wrong now, scalar shifts are done properly lazily.
            Vector shifts should be fixed too. */
         complainIfUndefined(mce, atom2);
         return assignNew('V', mce, Ity_V128, binop(op, vatom1, atom2));

      /* V x V shifts/rotates are done using the standard lazy scheme. */
      case Iop_Shl8x16:
      case Iop_Shr8x16:
      case Iop_Sar8x16:
      case Iop_Rol8x16:
         return mkUifUV128(mce,
                   assignNew('V', mce, Ity_V128, binop(op, vatom1, atom2)),
                   mkPCast8x16(mce,vatom2)
                );

      case Iop_Shl16x8:
      case Iop_Shr16x8:
      case Iop_Sar16x8:
      case Iop_Rol16x8:
         return mkUifUV128(mce,
                   assignNew('V', mce, Ity_V128, binop(op, vatom1, atom2)),
                   mkPCast16x8(mce,vatom2)
                );

      case Iop_Shl32x4:
      case Iop_Shr32x4:
      case Iop_Sar32x4:
      case Iop_Rol32x4:
         return mkUifUV128(mce,
                   assignNew('V', mce, Ity_V128, binop(op, vatom1, atom2)),
                   mkPCast32x4(mce,vatom2)
                );

      case Iop_QSub8Ux16:
      case Iop_QSub8Sx16:
      case Iop_Sub8x16:
      case Iop_Min8Ux16:
      case Iop_Min8Sx16:
      case Iop_Max8Ux16:
      case Iop_Max8Sx16:
      case Iop_CmpGT8Sx16:
      case Iop_CmpGT8Ux16:
      case Iop_CmpEQ8x16:
      case Iop_Avg8Ux16:
      case Iop_Avg8Sx16:
      case Iop_QAdd8Ux16:
      case Iop_QAdd8Sx16:
      case Iop_Add8x16:
         return binary8Ix16(mce, vatom1, vatom2);

      case Iop_QSub16Ux8:
      case Iop_QSub16Sx8:
      case Iop_Sub16x8:
      case Iop_Mul16x8:
      case Iop_MulHi16Sx8:
      case Iop_MulHi16Ux8:
      case Iop_Min16Sx8:
      case Iop_Min16Ux8:
      case Iop_Max16Sx8:
      case Iop_Max16Ux8:
      case Iop_CmpGT16Sx8:
      case Iop_CmpGT16Ux8:
      case Iop_CmpEQ16x8:
      case Iop_Avg16Ux8:
      case Iop_Avg16Sx8:
      case Iop_QAdd16Ux8:
      case Iop_QAdd16Sx8:
      case Iop_Add16x8:
         return binary16Ix8(mce, vatom1, vatom2);

      case Iop_Sub32x4:
      case Iop_CmpGT32Sx4:
      case Iop_CmpGT32Ux4:
      case Iop_CmpEQ32x4:
      case Iop_QAdd32Sx4:
      case Iop_QAdd32Ux4:
      case Iop_QSub32Sx4:
      case Iop_QSub32Ux4:
      case Iop_Avg32Ux4:
      case Iop_Avg32Sx4:
      case Iop_Add32x4:
      case Iop_Max32Ux4:
      case Iop_Max32Sx4:
      case Iop_Min32Ux4:
      case Iop_Min32Sx4:
         return binary32Ix4(mce, vatom1, vatom2);

      case Iop_Sub64x2:
      case Iop_Add64x2:
         return binary64Ix2(mce, vatom1, vatom2);

      case Iop_QNarrow32Sx4:
      case Iop_QNarrow32Ux4:
      case Iop_QNarrow16Sx8:
      case Iop_QNarrow16Ux8:
         return vectorNarrowV128(mce, op, vatom1, vatom2);

      case Iop_Sub64Fx2:
      case Iop_Mul64Fx2:
      case Iop_Min64Fx2:
      case Iop_Max64Fx2:
      case Iop_Div64Fx2:
      case Iop_CmpLT64Fx2:
      case Iop_CmpLE64Fx2:
      case Iop_CmpEQ64Fx2:
      case Iop_CmpUN64Fx2:
      case Iop_Add64Fx2:
         return binary64Fx2(mce, vatom1, vatom2);      

      case Iop_Sub64F0x2:
      case Iop_Mul64F0x2:
      case Iop_Min64F0x2:
      case Iop_Max64F0x2:
      case Iop_Div64F0x2:
      case Iop_CmpLT64F0x2:
      case Iop_CmpLE64F0x2:
      case Iop_CmpEQ64F0x2:
      case Iop_CmpUN64F0x2:
      case Iop_Add64F0x2:
         return binary64F0x2(mce, vatom1, vatom2);      

      case Iop_Sub32Fx4:
      case Iop_Mul32Fx4:
      case Iop_Min32Fx4:
      case Iop_Max32Fx4:
      case Iop_Div32Fx4:
      case Iop_CmpLT32Fx4:
      case Iop_CmpLE32Fx4:
      case Iop_CmpEQ32Fx4:
      case Iop_CmpUN32Fx4:
      case Iop_CmpGT32Fx4:
      case Iop_CmpGE32Fx4:
      case Iop_Add32Fx4:
         return binary32Fx4(mce, vatom1, vatom2);      

      case Iop_Sub32F0x4:
      case Iop_Mul32F0x4:
      case Iop_Min32F0x4:
      case Iop_Max32F0x4:
      case Iop_Div32F0x4:
      case Iop_CmpLT32F0x4:
      case Iop_CmpLE32F0x4:
      case Iop_CmpEQ32F0x4:
      case Iop_CmpUN32F0x4:
      case Iop_Add32F0x4:
         return binary32F0x4(mce, vatom1, vatom2);      

      /* V128-bit data-steering */
      case Iop_SetV128lo32:
      case Iop_SetV128lo64:
      case Iop_64HLtoV128:
      case Iop_InterleaveLO64x2:
      case Iop_InterleaveLO32x4:
      case Iop_InterleaveLO16x8:
      case Iop_InterleaveLO8x16:
      case Iop_InterleaveHI64x2:
      case Iop_InterleaveHI32x4:
      case Iop_InterleaveHI16x8:
      case Iop_InterleaveHI8x16:
         return assignNew('V', mce, Ity_V128, binop(op, vatom1, vatom2));
 
     /* Perm8x16: rearrange values in left arg using steering values
        from right arg.  So rearrange the vbits in the same way but
        pessimise wrt steering values. */
      case Iop_Perm8x16:
         return mkUifUV128(
                   mce,
                   assignNew('V', mce, Ity_V128, binop(op, vatom1, atom2)),
                   mkPCast8x16(mce, vatom2)
                );

     /* These two take the lower half of each 16-bit lane, sign/zero
        extend it to 32, and multiply together, producing a 32x4
        result (and implicitly ignoring half the operand bits).  So
        treat it as a bunch of independent 16x8 operations, but then
        do 32-bit shifts left-right to copy the lower half results
        (which are all 0s or all 1s due to PCasting in binary16Ix8)
        into the upper half of each result lane. */
      case Iop_MullEven16Ux8:
      case Iop_MullEven16Sx8: {
         IRAtom* at;
         at = binary16Ix8(mce,vatom1,vatom2);
         at = assignNew('V', mce, Ity_V128, binop(Iop_ShlN32x4, at, mkU8(16)));
         at = assignNew('V', mce, Ity_V128, binop(Iop_SarN32x4, at, mkU8(16)));
	 return at;
      }

      /* Same deal as Iop_MullEven16{S,U}x8 */
      case Iop_MullEven8Ux16:
      case Iop_MullEven8Sx16: {
         IRAtom* at;
         at = binary8Ix16(mce,vatom1,vatom2);
         at = assignNew('V', mce, Ity_V128, binop(Iop_ShlN16x8, at, mkU8(8)));
         at = assignNew('V', mce, Ity_V128, binop(Iop_SarN16x8, at, mkU8(8)));
	 return at;
      }

      /* narrow 2xV128 into 1xV128, hi half from left arg, in a 2 x
         32x4 -> 16x8 laneage, discarding the upper half of each lane.
         Simply apply same op to the V bits, since this really no more
         than a data steering operation. */
      case Iop_Narrow32x4: 
      case Iop_Narrow16x8: 
         return assignNew('V', mce, Ity_V128, 
                                    binop(op, vatom1, vatom2));

      case Iop_ShrV128:
      case Iop_ShlV128:
         /* Same scheme as with all other shifts.  Note: 10 Nov 05:
            this is wrong now, scalar shifts are done properly lazily.
            Vector shifts should be fixed too. */
         complainIfUndefined(mce, atom2);
         return assignNew('V', mce, Ity_V128, binop(op, vatom1, atom2));


      /* I128-bit data-steering */
      case Iop_64HLto128:
         return assignNew('V', mce, Ity_I128, binop(op, vatom1, vatom2));

      /* Scalar floating point */

      case Iop_RoundF64toInt:
      case Iop_RoundF64toF32:
      case Iop_F64toI64:
      case Iop_I64toF64:
      case Iop_SinF64:
      case Iop_CosF64:
      case Iop_TanF64:
      case Iop_2xm1F64:
      case Iop_SqrtF64:
         /* I32(rm) x I64/F64 -> I64/F64 */
         return mkLazy2(mce, Ity_I64, vatom1, vatom2);

      case Iop_F64toI32:
      case Iop_F64toF32:
         /* First arg is I32 (rounding mode), second is F64 (data). */
         return mkLazy2(mce, Ity_I32, vatom1, vatom2);

      case Iop_F64toI16:
         /* First arg is I32 (rounding mode), second is F64 (data). */
         return mkLazy2(mce, Ity_I16, vatom1, vatom2);

      case Iop_CmpF64:
         return mkLazy2(mce, Ity_I32, vatom1, vatom2);

      /* non-FP after here */

      case Iop_DivModU64to32:
      case Iop_DivModS64to32:
         return mkLazy2(mce, Ity_I64, vatom1, vatom2);

      case Iop_DivModU128to64:
      case Iop_DivModS128to64:
         return mkLazy2(mce, Ity_I128, vatom1, vatom2);

      case Iop_16HLto32:
         return assignNew('V', mce, Ity_I32, binop(op, vatom1, vatom2));
      case Iop_32HLto64:
         return assignNew('V', mce, Ity_I64, binop(op, vatom1, vatom2));

      case Iop_MullS64:
      case Iop_MullU64: {
         IRAtom* vLo64 = mkLeft64(mce, mkUifU64(mce, vatom1,vatom2));
         IRAtom* vHi64 = mkPCastTo(mce, Ity_I64, vLo64);
         return assignNew('V', mce, Ity_I128, binop(Iop_64HLto128, vHi64, vLo64));
      }

      case Iop_MullS32:
      case Iop_MullU32: {
         IRAtom* vLo32 = mkLeft32(mce, mkUifU32(mce, vatom1,vatom2));
         IRAtom* vHi32 = mkPCastTo(mce, Ity_I32, vLo32);
         return assignNew('V', mce, Ity_I64, binop(Iop_32HLto64, vHi32, vLo32));
      }

      case Iop_MullS16:
      case Iop_MullU16: {
         IRAtom* vLo16 = mkLeft16(mce, mkUifU16(mce, vatom1,vatom2));
         IRAtom* vHi16 = mkPCastTo(mce, Ity_I16, vLo16);
         return assignNew('V', mce, Ity_I32, binop(Iop_16HLto32, vHi16, vLo16));
      }

      case Iop_MullS8:
      case Iop_MullU8: {
         IRAtom* vLo8 = mkLeft8(mce, mkUifU8(mce, vatom1,vatom2));
         IRAtom* vHi8 = mkPCastTo(mce, Ity_I8, vLo8);
         return assignNew('V', mce, Ity_I16, binop(Iop_8HLto16, vHi8, vLo8));
      }

      case Iop_DivS32:
      case Iop_DivU32:
         return mkLazy2(mce, Ity_I32, vatom1, vatom2);

      case Iop_DivS64:
      case Iop_DivU64:
         return mkLazy2(mce, Ity_I64, vatom1, vatom2);

      case Iop_Add32:
         if (mce->bogusLiterals)
            return expensiveAddSub(mce,True,Ity_I32, 
                                   vatom1,vatom2, atom1,atom2);
         else
            goto cheap_AddSub32;
      case Iop_Sub32:
         if (mce->bogusLiterals)
            return expensiveAddSub(mce,False,Ity_I32, 
                                   vatom1,vatom2, atom1,atom2);
         else
            goto cheap_AddSub32;

      cheap_AddSub32:
      case Iop_Mul32:
         return mkLeft32(mce, mkUifU32(mce, vatom1,vatom2));

      case Iop_CmpORD32S:
      case Iop_CmpORD32U:
      case Iop_CmpORD64S:
      case Iop_CmpORD64U:
         return doCmpORD(mce, op, vatom1,vatom2, atom1,atom2);

      case Iop_Add64:
         if (mce->bogusLiterals)
            return expensiveAddSub(mce,True,Ity_I64, 
                                   vatom1,vatom2, atom1,atom2);
         else
            goto cheap_AddSub64;
      case Iop_Sub64:
         if (mce->bogusLiterals)
            return expensiveAddSub(mce,False,Ity_I64, 
                                   vatom1,vatom2, atom1,atom2);
         else
            goto cheap_AddSub64;

      cheap_AddSub64:
      case Iop_Mul64:
         return mkLeft64(mce, mkUifU64(mce, vatom1,vatom2));

      case Iop_Mul16:
      case Iop_Add16:
      case Iop_Sub16:
         return mkLeft16(mce, mkUifU16(mce, vatom1,vatom2));

      case Iop_Sub8:
      case Iop_Add8:
         return mkLeft8(mce, mkUifU8(mce, vatom1,vatom2));

      case Iop_CmpEQ64: 
      case Iop_CmpNE64:
         if (mce->bogusLiterals)
            return expensiveCmpEQorNE(mce,Ity_I64, vatom1,vatom2, atom1,atom2 );
         else
            goto cheap_cmp64;
      cheap_cmp64:
      case Iop_CmpLE64S: case Iop_CmpLE64U: 
      case Iop_CmpLT64U: case Iop_CmpLT64S:
         return mkPCastTo(mce, Ity_I1, mkUifU64(mce, vatom1,vatom2));

      case Iop_CmpEQ32: 
      case Iop_CmpNE32:
         if (mce->bogusLiterals)
            return expensiveCmpEQorNE(mce,Ity_I32, vatom1,vatom2, atom1,atom2 );
         else
            goto cheap_cmp32;
      cheap_cmp32:
      case Iop_CmpLE32S: case Iop_CmpLE32U: 
      case Iop_CmpLT32U: case Iop_CmpLT32S:
         return mkPCastTo(mce, Ity_I1, mkUifU32(mce, vatom1,vatom2));

      case Iop_CmpEQ16: case Iop_CmpNE16:
         return mkPCastTo(mce, Ity_I1, mkUifU16(mce, vatom1,vatom2));

      case Iop_CmpEQ8: case Iop_CmpNE8:
         return mkPCastTo(mce, Ity_I1, mkUifU8(mce, vatom1,vatom2));

      case Iop_Shl64: case Iop_Shr64: case Iop_Sar64:
         return scalarShift( mce, Ity_I64, op, vatom1,vatom2, atom1,atom2 );

      case Iop_Shl32: case Iop_Shr32: case Iop_Sar32:
         return scalarShift( mce, Ity_I32, op, vatom1,vatom2, atom1,atom2 );

      case Iop_Shl16: case Iop_Shr16: case Iop_Sar16:
         return scalarShift( mce, Ity_I16, op, vatom1,vatom2, atom1,atom2 );

      case Iop_Shl8: case Iop_Shr8:
         return scalarShift( mce, Ity_I8, op, vatom1,vatom2, atom1,atom2 );

      case Iop_AndV128:
         uifu = mkUifUV128; difd = mkDifDV128; 
         and_or_ty = Ity_V128; improve = mkImproveANDV128; goto do_And_Or;
      case Iop_And64:
         uifu = mkUifU64; difd = mkDifD64; 
         and_or_ty = Ity_I64; improve = mkImproveAND64; goto do_And_Or;
      case Iop_And32:
         uifu = mkUifU32; difd = mkDifD32; 
         and_or_ty = Ity_I32; improve = mkImproveAND32; goto do_And_Or;
      case Iop_And16:
         uifu = mkUifU16; difd = mkDifD16; 
         and_or_ty = Ity_I16; improve = mkImproveAND16; goto do_And_Or;
      case Iop_And8:
         uifu = mkUifU8; difd = mkDifD8; 
         and_or_ty = Ity_I8; improve = mkImproveAND8; goto do_And_Or;

      case Iop_OrV128:
         uifu = mkUifUV128; difd = mkDifDV128; 
         and_or_ty = Ity_V128; improve = mkImproveORV128; goto do_And_Or;
      case Iop_Or64:
         uifu = mkUifU64; difd = mkDifD64; 
         and_or_ty = Ity_I64; improve = mkImproveOR64; goto do_And_Or;
      case Iop_Or32:
         uifu = mkUifU32; difd = mkDifD32; 
         and_or_ty = Ity_I32; improve = mkImproveOR32; goto do_And_Or;
      case Iop_Or16:
         uifu = mkUifU16; difd = mkDifD16; 
         and_or_ty = Ity_I16; improve = mkImproveOR16; goto do_And_Or;
      case Iop_Or8:
         uifu = mkUifU8; difd = mkDifD8; 
         and_or_ty = Ity_I8; improve = mkImproveOR8; goto do_And_Or;

      do_And_Or:
         return
         assignNew(
            'V', mce, 
            and_or_ty,
            difd(mce, uifu(mce, vatom1, vatom2),
                      difd(mce, improve(mce, atom1, vatom1),
                                improve(mce, atom2, vatom2) ) ) );

      case Iop_Xor8:
         return mkUifU8(mce, vatom1, vatom2);
      case Iop_Xor16:
         return mkUifU16(mce, vatom1, vatom2);
      case Iop_Xor32:
         return mkUifU32(mce, vatom1, vatom2);
      case Iop_Xor64:
         return mkUifU64(mce, vatom1, vatom2);
      case Iop_XorV128:
         return mkUifUV128(mce, vatom1, vatom2);

      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Binop");
   }
}


static 
IRExpr* expr2vbits_Unop ( MCEnv* mce, IROp op, IRAtom* atom )
{
   IRAtom* vatom = expr2vbits( mce, atom );
   tl_assert(isOriginalAtom(mce,atom));
   switch (op) {

      case Iop_Sqrt64Fx2:
         return unary64Fx2(mce, vatom);

      case Iop_Sqrt64F0x2:
         return unary64F0x2(mce, vatom);

      case Iop_Sqrt32Fx4:
      case Iop_RSqrt32Fx4:
      case Iop_Recip32Fx4:
      case Iop_I32UtoFx4:
      case Iop_I32StoFx4:
      case Iop_QFtoI32Ux4_RZ:
      case Iop_QFtoI32Sx4_RZ:
      case Iop_RoundF32x4_RM:
      case Iop_RoundF32x4_RP:
      case Iop_RoundF32x4_RN:
      case Iop_RoundF32x4_RZ:
         return unary32Fx4(mce, vatom);

      case Iop_Sqrt32F0x4:
      case Iop_RSqrt32F0x4:
      case Iop_Recip32F0x4:
         return unary32F0x4(mce, vatom);

      case Iop_32UtoV128:
      case Iop_64UtoV128:
      case Iop_Dup8x16:
      case Iop_Dup16x8:
      case Iop_Dup32x4:
         return assignNew('V', mce, Ity_V128, unop(op, vatom));

      case Iop_F32toF64: 
      case Iop_I32toF64:
      case Iop_NegF64:
      case Iop_AbsF64:
      case Iop_Est5FRSqrt:
      case Iop_RoundF64toF64_NEAREST:
      case Iop_RoundF64toF64_NegINF:
      case Iop_RoundF64toF64_PosINF:
      case Iop_RoundF64toF64_ZERO:
      case Iop_Clz64:
      case Iop_Ctz64:
         return mkPCastTo(mce, Ity_I64, vatom);

      case Iop_Clz32:
      case Iop_Ctz32:
      case Iop_TruncF64asF32:
         return mkPCastTo(mce, Ity_I32, vatom);

      case Iop_1Uto64:
      case Iop_8Uto64:
      case Iop_8Sto64:
      case Iop_16Uto64:
      case Iop_16Sto64:
      case Iop_32Sto64:
      case Iop_32Uto64:
      case Iop_V128to64:
      case Iop_V128HIto64:
      case Iop_128HIto64:
      case Iop_128to64:
         return assignNew('V', mce, Ity_I64, unop(op, vatom));

      case Iop_64to32:
      case Iop_64HIto32:
      case Iop_1Uto32:
      case Iop_1Sto32:
      case Iop_8Uto32:
      case Iop_16Uto32:
      case Iop_16Sto32:
      case Iop_8Sto32:
      case Iop_V128to32:
         return assignNew('V', mce, Ity_I32, unop(op, vatom));

      case Iop_8Sto16:
      case Iop_8Uto16:
      case Iop_32to16:
      case Iop_32HIto16:
      case Iop_64to16:
         return assignNew('V', mce, Ity_I16, unop(op, vatom));

      case Iop_1Uto8:
      case Iop_16to8:
      case Iop_16HIto8:
      case Iop_32to8:
      case Iop_64to8:
         return assignNew('V', mce, Ity_I8, unop(op, vatom));

      case Iop_32to1:
         return assignNew('V', mce, Ity_I1, unop(Iop_32to1, vatom));

      case Iop_64to1:
         return assignNew('V', mce, Ity_I1, unop(Iop_64to1, vatom));

      case Iop_ReinterpF64asI64:
      case Iop_ReinterpI64asF64:
      case Iop_ReinterpI32asF32:
      case Iop_NotV128:
      case Iop_Not64:
      case Iop_Not32:
      case Iop_Not16:
      case Iop_Not8:
      case Iop_Not1:
         return vatom;

      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Unop");
   }
}


/* Worker function; do not call directly. */
static
IRAtom* expr2vbits_Load_WRK ( MCEnv* mce, 
                              IREndness end, IRType ty, 
                              IRAtom* addr, UInt bias )
{
   void*    helper;
   Char*    hname;
   IRDirty* di;
   IRTemp   datavbits;
   IRAtom*  addrAct;

   tl_assert(isOriginalAtom(mce,addr));
   tl_assert(end == Iend_LE || end == Iend_BE);

   /* First, emit a definedness test for the address.  This also sets
      the address (shadow) to 'defined' following the test. */
   complainIfUndefined( mce, addr );

   /* Now cook up a call to the relevant helper function, to read the
      data V bits from shadow memory. */
   ty = shadowTypeV(ty);

   if (end == Iend_LE) {   
      switch (ty) {
         case Ity_I64: helper = &MC_(helperc_LOADV64le);
                       hname = "MC_(helperc_LOADV64le)";
                       break;
         case Ity_I32: helper = &MC_(helperc_LOADV32le);
                       hname = "MC_(helperc_LOADV32le)";
                       break;
         case Ity_I16: helper = &MC_(helperc_LOADV16le);
                       hname = "MC_(helperc_LOADV16le)";
                       break;
         case Ity_I8:  helper = &MC_(helperc_LOADV8);
                       hname = "MC_(helperc_LOADV8)";
                       break;
         default:      ppIRType(ty);
                       VG_(tool_panic)("memcheck:do_shadow_Load(LE)");
      }
   } else {
      switch (ty) {
         case Ity_I64: helper = &MC_(helperc_LOADV64be);
                       hname = "MC_(helperc_LOADV64be)";
                       break;
         case Ity_I32: helper = &MC_(helperc_LOADV32be);
                       hname = "MC_(helperc_LOADV32be)";
                       break;
         case Ity_I16: helper = &MC_(helperc_LOADV16be);
                       hname = "MC_(helperc_LOADV16be)";
                       break;
         case Ity_I8:  helper = &MC_(helperc_LOADV8);
                       hname = "MC_(helperc_LOADV8)";
                       break;
         default:      ppIRType(ty);
                       VG_(tool_panic)("memcheck:do_shadow_Load(BE)");
      }
   }

   /* Generate the actual address into addrAct. */
   if (bias == 0) {
      addrAct = addr;
   } else {
      IROp    mkAdd;
      IRAtom* eBias;
      IRType  tyAddr  = mce->hWordTy;
      tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );
      mkAdd   = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
      eBias   = tyAddr==Ity_I32 ? mkU32(bias) : mkU64(bias);
      addrAct = assignNew('V', mce, tyAddr, binop(mkAdd, addr, eBias) );
   }

   /* We need to have a place to park the V bits we're just about to
      read. */
   datavbits = newIRTemp(mce->bb->tyenv, ty);
   di = unsafeIRDirty_1_N( datavbits, 
                           1/*regparms*/, 
                           hname, VG_(fnptr_to_fnentry)( helper ), 
                           mkIRExprVec_1( addrAct ));
   setHelperAnns( mce, di );
   stmt( 'V', mce, IRStmt_Dirty(di) );

   return mkexpr(datavbits);
}


static
IRAtom* expr2vbits_Load ( MCEnv* mce, 
                          IREndness end, IRType ty, 
                          IRAtom* addr, UInt bias )
{
   IRAtom *v64hi, *v64lo;
   tl_assert(end == Iend_LE || end == Iend_BE);
   switch (shadowTypeV(ty)) {
      case Ity_I8: 
      case Ity_I16: 
      case Ity_I32: 
      case Ity_I64:
         return expr2vbits_Load_WRK(mce, end, ty, addr, bias);
      case Ity_V128:
         if (end == Iend_LE) {
            v64lo = expr2vbits_Load_WRK(mce, end, Ity_I64, addr, bias);
            v64hi = expr2vbits_Load_WRK(mce, end, Ity_I64, addr, bias+8);
         } else {
            v64hi = expr2vbits_Load_WRK(mce, end, Ity_I64, addr, bias);
            v64lo = expr2vbits_Load_WRK(mce, end, Ity_I64, addr, bias+8);
         }
         return assignNew( 'V', mce, 
                           Ity_V128, 
                           binop(Iop_64HLtoV128, v64hi, v64lo));
      default:
         VG_(tool_panic)("expr2vbits_Load");
   }
}


static
IRAtom* expr2vbits_Mux0X ( MCEnv* mce, 
                           IRAtom* cond, IRAtom* expr0, IRAtom* exprX )
{
   IRAtom *vbitsC, *vbits0, *vbitsX;
   IRType ty;
   /* Given Mux0X(cond,expr0,exprX), generate
         Mux0X(cond,expr0#,exprX#) `UifU` PCast(cond#)
      That is, steer the V bits like the originals, but trash the 
      result if the steering value is undefined.  This gives 
      lazy propagation. */
   tl_assert(isOriginalAtom(mce, cond));
   tl_assert(isOriginalAtom(mce, expr0));
   tl_assert(isOriginalAtom(mce, exprX));

   vbitsC = expr2vbits(mce, cond);
   vbits0 = expr2vbits(mce, expr0);
   vbitsX = expr2vbits(mce, exprX);
   ty = typeOfIRExpr(mce->bb->tyenv, vbits0);

   return
      mkUifU(mce, ty, assignNew('V', mce, ty, 
                                     IRExpr_Mux0X(cond, vbits0, vbitsX)),
                      mkPCastTo(mce, ty, vbitsC) );
}      

/* --------- This is the main expression-handling function. --------- */

static
IRExpr* expr2vbits ( MCEnv* mce, IRExpr* e )
{
   switch (e->tag) {

      case Iex_Get:
         return shadow_GET( mce, e->Iex.Get.offset, e->Iex.Get.ty );

      case Iex_GetI:
         return shadow_GETI( mce, e->Iex.GetI.descr, 
                                  e->Iex.GetI.ix, e->Iex.GetI.bias );

      case Iex_RdTmp:
         return IRExpr_RdTmp( findShadowTmpV(mce, e->Iex.RdTmp.tmp) );

      case Iex_Const:
         return definedOfType(shadowTypeV(typeOfIRExpr(mce->bb->tyenv, e)));

      case Iex_Qop:
         return expr2vbits_Qop(
                   mce,
                   e->Iex.Qop.op,
                   e->Iex.Qop.arg1, e->Iex.Qop.arg2,
		   e->Iex.Qop.arg3, e->Iex.Qop.arg4
                );

      case Iex_Triop:
         return expr2vbits_Triop(
                   mce,
                   e->Iex.Triop.op,
                   e->Iex.Triop.arg1, e->Iex.Triop.arg2, e->Iex.Triop.arg3
                );

      case Iex_Binop:
         return expr2vbits_Binop(
                   mce,
                   e->Iex.Binop.op,
                   e->Iex.Binop.arg1, e->Iex.Binop.arg2
                );

      case Iex_Unop:
         return expr2vbits_Unop( mce, e->Iex.Unop.op, e->Iex.Unop.arg );

      case Iex_Load:
         return expr2vbits_Load( mce, e->Iex.Load.end,
                                      e->Iex.Load.ty, 
                                      e->Iex.Load.addr, 0/*addr bias*/ );

      case Iex_CCall:
         return mkLazyN( mce, e->Iex.CCall.args, 
                              e->Iex.CCall.retty,
                              e->Iex.CCall.cee );

      case Iex_Mux0X:
         return expr2vbits_Mux0X( mce, e->Iex.Mux0X.cond, e->Iex.Mux0X.expr0, 
                                       e->Iex.Mux0X.exprX);

      default: 
         VG_(printf)("\n");
         ppIRExpr(e);
         VG_(printf)("\n");
         VG_(tool_panic)("memcheck: expr2vbits");
   }
}

/*------------------------------------------------------------*/
/*--- Generate shadow stmts from all kinds of IRStmts.     ---*/
/*------------------------------------------------------------*/

/* Widen a value to the host word size. */

static
IRExpr* zwidenToHostWord ( MCEnv* mce, IRAtom* vatom )
{
   IRType ty, tyH;

   /* vatom is vbits-value and as such can only have a shadow type. */
   tl_assert(isShadowAtom(mce,vatom));

   ty  = typeOfIRExpr(mce->bb->tyenv, vatom);
   tyH = mce->hWordTy;

   if (tyH == Ity_I32) {
      switch (ty) {
         case Ity_I32:
            return vatom;
         case Ity_I16:
            return assignNew('V', mce, tyH, unop(Iop_16Uto32, vatom));
         case Ity_I8:
            return assignNew('V', mce, tyH, unop(Iop_8Uto32, vatom));
         default:
            goto unhandled;
      }
   } else
   if (tyH == Ity_I64) {
      switch (ty) {
         case Ity_I32:
            return assignNew('V', mce, tyH, unop(Iop_32Uto64, vatom));
         case Ity_I16:
            return assignNew('V', mce, tyH, unop(Iop_32Uto64, 
                   assignNew('V', mce, Ity_I32, unop(Iop_16Uto32, vatom))));
         case Ity_I8:
            return assignNew('V', mce, tyH, unop(Iop_32Uto64, 
                   assignNew('V', mce, Ity_I32, unop(Iop_8Uto32, vatom))));
         default:
            goto unhandled;
      }
   } else {
      goto unhandled;
   }
  unhandled:
   VG_(printf)("\nty = "); ppIRType(ty); VG_(printf)("\n");
   VG_(tool_panic)("zwidenToHostWord");
}


/* Generate a shadow store.  addr is always the original address atom.
   You can pass in either originals or V-bits for the data atom, but
   obviously not both.  */

static 
void do_shadow_Store ( MCEnv* mce, 
                       IREndness end,
                       IRAtom* addr, UInt bias,
                       IRAtom* data, IRAtom* vdata )
{
   IROp     mkAdd;
   IRType   ty, tyAddr;
   void*    helper = NULL;
   Char*    hname = NULL;
   IRConst* c;

   tyAddr = mce->hWordTy;
   mkAdd  = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
   tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );
   tl_assert( end == Iend_LE || end == Iend_BE );

   if (data) {
      tl_assert(!vdata);
      tl_assert(isOriginalAtom(mce, data));
      tl_assert(bias == 0);
      vdata = expr2vbits( mce, data );
   } else {
      tl_assert(vdata);
   }

   tl_assert(isOriginalAtom(mce,addr));
   tl_assert(isShadowAtom(mce,vdata));

   ty = typeOfIRExpr(mce->bb->tyenv, vdata);

   // If we're not doing undefined value checking, pretend that this value
   // is "all valid".  That lets Vex's optimiser remove some of the V bit
   // shadow computation ops that precede it.
   if (MC_(clo_mc_level) == 1) {
      switch (ty) {
         case Ity_V128: c = IRConst_V128(V_BITS16_DEFINED); break; // V128 weirdness
         case Ity_I64:  c = IRConst_U64 (V_BITS64_DEFINED); break;
         case Ity_I32:  c = IRConst_U32 (V_BITS32_DEFINED); break;
         case Ity_I16:  c = IRConst_U16 (V_BITS16_DEFINED); break;
         case Ity_I8:   c = IRConst_U8  (V_BITS8_DEFINED);  break;
         default:       VG_(tool_panic)("memcheck:do_shadow_Store(LE)");
      }
      vdata = IRExpr_Const( c );
   }

   /* First, emit a definedness test for the address.  This also sets
      the address (shadow) to 'defined' following the test. */
   complainIfUndefined( mce, addr );

   /* Now decide which helper function to call to write the data V
      bits into shadow memory. */
   if (end == Iend_LE) {
      switch (ty) {
         case Ity_V128: /* we'll use the helper twice */
         case Ity_I64: helper = &MC_(helperc_STOREV64le);
                       hname = "MC_(helperc_STOREV64le)";
                       break;
         case Ity_I32: helper = &MC_(helperc_STOREV32le);
                       hname = "MC_(helperc_STOREV32le)";
                       break;
         case Ity_I16: helper = &MC_(helperc_STOREV16le);
                       hname = "MC_(helperc_STOREV16le)";
                       break;
         case Ity_I8:  helper = &MC_(helperc_STOREV8);
                       hname = "MC_(helperc_STOREV8)";
                       break;
         default:      VG_(tool_panic)("memcheck:do_shadow_Store(LE)");
      }
   } else {
      switch (ty) {
         case Ity_V128: /* we'll use the helper twice */
         case Ity_I64: helper = &MC_(helperc_STOREV64be);
                       hname = "MC_(helperc_STOREV64be)";
                       break;
         case Ity_I32: helper = &MC_(helperc_STOREV32be);
                       hname = "MC_(helperc_STOREV32be)";
                       break;
         case Ity_I16: helper = &MC_(helperc_STOREV16be);
                       hname = "MC_(helperc_STOREV16be)";
                       break;
         case Ity_I8:  helper = &MC_(helperc_STOREV8);
                       hname = "MC_(helperc_STOREV8)";
                       break;
         default:      VG_(tool_panic)("memcheck:do_shadow_Store(BE)");
      }
   }

   if (ty == Ity_V128) {

      /* V128-bit case */
      /* See comment in next clause re 64-bit regparms */
      /* also, need to be careful about endianness */

      Int     offLo64, offHi64;
      IRDirty *diLo64, *diHi64;
      IRAtom  *addrLo64, *addrHi64;
      IRAtom  *vdataLo64, *vdataHi64;
      IRAtom  *eBiasLo64, *eBiasHi64;

      if (end == Iend_LE) {
         offLo64 = 0;
         offHi64 = 8;
      } else {
         offLo64 = 8;
         offHi64 = 0;
      }

      eBiasLo64 = tyAddr==Ity_I32 ? mkU32(bias+offLo64) : mkU64(bias+offLo64);
      addrLo64  = assignNew('V', mce, tyAddr, binop(mkAdd, addr, eBiasLo64) );
      vdataLo64 = assignNew('V', mce, Ity_I64, unop(Iop_V128to64, vdata));
      diLo64    = unsafeIRDirty_0_N( 
                     1/*regparms*/, 
                     hname, VG_(fnptr_to_fnentry)( helper ), 
                     mkIRExprVec_2( addrLo64, vdataLo64 )
                  );
      eBiasHi64 = tyAddr==Ity_I32 ? mkU32(bias+offHi64) : mkU64(bias+offHi64);
      addrHi64  = assignNew('V', mce, tyAddr, binop(mkAdd, addr, eBiasHi64) );
      vdataHi64 = assignNew('V', mce, Ity_I64, unop(Iop_V128HIto64, vdata));
      diHi64    = unsafeIRDirty_0_N( 
                     1/*regparms*/, 
                     hname, VG_(fnptr_to_fnentry)( helper ), 
                     mkIRExprVec_2( addrHi64, vdataHi64 )
                  );
      setHelperAnns( mce, diLo64 );
      setHelperAnns( mce, diHi64 );
      stmt( 'V', mce, IRStmt_Dirty(diLo64) );
      stmt( 'V', mce, IRStmt_Dirty(diHi64) );

   } else {

      IRDirty *di;
      IRAtom  *addrAct;

      /* 8/16/32/64-bit cases */
      /* Generate the actual address into addrAct. */
      if (bias == 0) {
         addrAct = addr;
      } else {
         IRAtom* eBias   = tyAddr==Ity_I32 ? mkU32(bias) : mkU64(bias);
         addrAct = assignNew('V', mce, tyAddr, binop(mkAdd, addr, eBias));
      }

      if (ty == Ity_I64) {
         /* We can't do this with regparm 2 on 32-bit platforms, since
            the back ends aren't clever enough to handle 64-bit
            regparm args.  Therefore be different. */
         di = unsafeIRDirty_0_N( 
                 1/*regparms*/, 
                 hname, VG_(fnptr_to_fnentry)( helper ), 
                 mkIRExprVec_2( addrAct, vdata )
              );
      } else {
         di = unsafeIRDirty_0_N( 
                 2/*regparms*/, 
                 hname, VG_(fnptr_to_fnentry)( helper ), 
                 mkIRExprVec_2( addrAct,
                                zwidenToHostWord( mce, vdata ))
              );
      }
      setHelperAnns( mce, di );
      stmt( 'V', mce, IRStmt_Dirty(di) );
   }

}


/* Do lazy pessimistic propagation through a dirty helper call, by
   looking at the annotations on it.  This is the most complex part of
   Memcheck. */

static IRType szToITy ( Int n )
{
   switch (n) {
      case 1: return Ity_I8;
      case 2: return Ity_I16;
      case 4: return Ity_I32;
      case 8: return Ity_I64;
      default: VG_(tool_panic)("szToITy(memcheck)");
   }
}

static
void do_shadow_Dirty ( MCEnv* mce, IRDirty* d )
{
   Int       i, n, toDo, gSz, gOff;
   IRAtom    *src, *here, *curr;
   IRType    tySrc, tyDst;
   IRTemp    dst;
   IREndness end;

   /* What's the native endianness?  We need to know this. */
#  if defined(VG_BIGENDIAN)
   end = Iend_BE;
#  elif defined(VG_LITTLEENDIAN)
   end = Iend_LE;
#  else
#    error "Unknown endianness"
#  endif

   /* First check the guard. */
   complainIfUndefined(mce, d->guard);

   /* Now round up all inputs and PCast over them. */
   curr = definedOfType(Ity_I32);

   /* Inputs: unmasked args */
   for (i = 0; d->args[i]; i++) {
      if (d->cee->mcx_mask & (1<<i)) {
         /* ignore this arg */
      } else {
         here = mkPCastTo( mce, Ity_I32, expr2vbits(mce, d->args[i]) );
         curr = mkUifU32(mce, here, curr);
      }
   }

   /* Inputs: guest state that we read. */
   for (i = 0; i < d->nFxState; i++) {
      tl_assert(d->fxState[i].fx != Ifx_None);
      if (d->fxState[i].fx == Ifx_Write)
         continue;

      /* Ignore any sections marked as 'always defined'. */
      if (isAlwaysDefd(mce, d->fxState[i].offset, d->fxState[i].size )) {
         if (0)
         VG_(printf)("memcheck: Dirty gst: ignored off %d, sz %d\n",
                     d->fxState[i].offset, d->fxState[i].size );
         continue;
      }

      /* This state element is read or modified.  So we need to
         consider it.  If larger than 8 bytes, deal with it in 8-byte
         chunks. */
      gSz  = d->fxState[i].size;
      gOff = d->fxState[i].offset;
      tl_assert(gSz > 0);
      while (True) {
         if (gSz == 0) break;
         n = gSz <= 8 ? gSz : 8;
         /* update 'curr' with UifU of the state slice 
            gOff .. gOff+n-1 */
         tySrc = szToITy( n );
         src   = assignNew( 'V', mce, tySrc, 
                                 shadow_GET(mce, gOff, tySrc ) );
         here = mkPCastTo( mce, Ity_I32, src );
         curr = mkUifU32(mce, here, curr);
         gSz -= n;
         gOff += n;
      }

   }

   /* Inputs: memory.  First set up some info needed regardless of
      whether we're doing reads or writes. */

   if (d->mFx != Ifx_None) {
      /* Because we may do multiple shadow loads/stores from the same
         base address, it's best to do a single test of its
         definedness right now.  Post-instrumentation optimisation
         should remove all but this test. */
      IRType tyAddr;
      tl_assert(d->mAddr);
      complainIfUndefined(mce, d->mAddr);

      tyAddr = typeOfIRExpr(mce->bb->tyenv, d->mAddr);
      tl_assert(tyAddr == Ity_I32 || tyAddr == Ity_I64);
      tl_assert(tyAddr == mce->hWordTy); /* not really right */
   }

   /* Deal with memory inputs (reads or modifies) */
   if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify) {
      toDo   = d->mSize;
      /* chew off 32-bit chunks.  We don't care about the endianness
         since it's all going to be condensed down to a single bit,
         but nevertheless choose an endianness which is hopefully
         native to the platform. */
      while (toDo >= 4) {
         here = mkPCastTo( 
                   mce, Ity_I32,
                   expr2vbits_Load ( mce, end, Ity_I32, 
                                     d->mAddr, d->mSize - toDo )
                );
         curr = mkUifU32(mce, here, curr);
         toDo -= 4;
      }
      /* chew off 16-bit chunks */
      while (toDo >= 2) {
         here = mkPCastTo( 
                   mce, Ity_I32,
                   expr2vbits_Load ( mce, end, Ity_I16, 
                                     d->mAddr, d->mSize - toDo )
                );
         curr = mkUifU32(mce, here, curr);
         toDo -= 2;
      }
      tl_assert(toDo == 0); /* also need to handle 1-byte excess */
   }

   /* Whew!  So curr is a 32-bit V-value summarising pessimistically
      all the inputs to the helper.  Now we need to re-distribute the
      results to all destinations. */

   /* Outputs: the destination temporary, if there is one. */
   if (d->tmp != IRTemp_INVALID) {
      dst   = findShadowTmpV(mce, d->tmp);
      tyDst = typeOfIRTemp(mce->bb->tyenv, d->tmp);
      assign( 'V', mce, dst, mkPCastTo( mce, tyDst, curr) );
   }

   /* Outputs: guest state that we write or modify. */
   for (i = 0; i < d->nFxState; i++) {
      tl_assert(d->fxState[i].fx != Ifx_None);
      if (d->fxState[i].fx == Ifx_Read)
         continue;
      /* Ignore any sections marked as 'always defined'. */
      if (isAlwaysDefd(mce, d->fxState[i].offset, d->fxState[i].size ))
         continue;
      /* This state element is written or modified.  So we need to
         consider it.  If larger than 8 bytes, deal with it in 8-byte
         chunks. */
      gSz  = d->fxState[i].size;
      gOff = d->fxState[i].offset;
      tl_assert(gSz > 0);
      while (True) {
         if (gSz == 0) break;
         n = gSz <= 8 ? gSz : 8;
         /* Write suitably-casted 'curr' to the state slice 
            gOff .. gOff+n-1 */
         tyDst = szToITy( n );
         do_shadow_PUT( mce, gOff,
                             NULL, /* original atom */
                             mkPCastTo( mce, tyDst, curr ) );
         gSz -= n;
         gOff += n;
      }
   }

   /* Outputs: memory that we write or modify.  Same comments about
      endianness as above apply. */
   if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify) {
      toDo   = d->mSize;
      /* chew off 32-bit chunks */
      while (toDo >= 4) {
         do_shadow_Store( mce, end, d->mAddr, d->mSize - toDo,
                          NULL, /* original data */
                          mkPCastTo( mce, Ity_I32, curr ) );
         toDo -= 4;
      }
      /* chew off 16-bit chunks */
      while (toDo >= 2) {
         do_shadow_Store( mce, end, d->mAddr, d->mSize - toDo,
                          NULL, /* original data */
                          mkPCastTo( mce, Ity_I16, curr ) );
         toDo -= 2;
      }
      tl_assert(toDo == 0); /* also need to handle 1-byte excess */
   }

}

/* We have an ABI hint telling us that [base .. base+len-1] is to
   become undefined ("writable").  Generate code to call a helper to
   notify the A/V bit machinery of this fact.

   We call 
   void MC_(helperc_MAKE_STACK_UNINIT) ( Addr base, UWord len,
                                                    Addr nia );
*/
static
void do_AbiHint ( MCEnv* mce, IRExpr* base, Int len, IRExpr* nia )
{
   IRDirty* di;
   /* Minor optimisation: if not doing origin tracking, ignore the
      supplied nia and pass zero instead.  This is on the basis that
      MC_(helperc_MAKE_STACK_UNINIT) will ignore it anyway, and we can
      almost always generate a shorter instruction to put zero into a
      register than any other value. */
   if (MC_(clo_mc_level) < 3)
      nia = mkIRExpr_HWord(0);

   di = unsafeIRDirty_0_N(
           0/*regparms*/,
           "MC_(helperc_MAKE_STACK_UNINIT)",
           VG_(fnptr_to_fnentry)( &MC_(helperc_MAKE_STACK_UNINIT) ),
           mkIRExprVec_3( base, mkIRExpr_HWord( (UInt)len), nia )
        );
   stmt( 'V', mce, IRStmt_Dirty(di) );
}


/*------------------------------------------------------------*/
/*--- Memcheck main                                        ---*/
/*------------------------------------------------------------*/

static void schemeS ( MCEnv* mce, IRStmt* st );

static Bool isBogusAtom ( IRAtom* at )
{
   ULong n = 0;
   IRConst* con;
   tl_assert(isIRAtom(at));
   if (at->tag == Iex_RdTmp)
      return False;
   tl_assert(at->tag == Iex_Const);
   con = at->Iex.Const.con;
   switch (con->tag) {
      case Ico_U1:   return False;
      case Ico_U8:   n = (ULong)con->Ico.U8; break;
      case Ico_U16:  n = (ULong)con->Ico.U16; break;
      case Ico_U32:  n = (ULong)con->Ico.U32; break;
      case Ico_U64:  n = (ULong)con->Ico.U64; break;
      case Ico_F64:  return False;
      case Ico_F64i: return False;
      case Ico_V128: return False;
      default: ppIRExpr(at); tl_assert(0);
   }
   /* VG_(printf)("%llx\n", n); */
   return (/*32*/    n == 0xFEFEFEFFULL
           /*32*/ || n == 0x80808080ULL
           /*32*/ || n == 0x7F7F7F7FULL
           /*64*/ || n == 0xFFFFFFFFFEFEFEFFULL
           /*64*/ || n == 0xFEFEFEFEFEFEFEFFULL
           /*64*/ || n == 0x0000000000008080ULL
           /*64*/ || n == 0x8080808080808080ULL
           /*64*/ || n == 0x0101010101010101ULL
          );
}

static Bool checkForBogusLiterals ( /*FLAT*/ IRStmt* st )
{
   Int      i;
   IRExpr*  e;
   IRDirty* d;
   switch (st->tag) {
      case Ist_WrTmp:
         e = st->Ist.WrTmp.data;
         switch (e->tag) {
            case Iex_Get:
            case Iex_RdTmp:
               return False;
            case Iex_Const:
               return isBogusAtom(e);
            case Iex_Unop: 
               return isBogusAtom(e->Iex.Unop.arg);
            case Iex_GetI:
               return isBogusAtom(e->Iex.GetI.ix);
            case Iex_Binop: 
               return isBogusAtom(e->Iex.Binop.arg1)
                      || isBogusAtom(e->Iex.Binop.arg2);
            case Iex_Triop: 
               return isBogusAtom(e->Iex.Triop.arg1)
                      || isBogusAtom(e->Iex.Triop.arg2)
                      || isBogusAtom(e->Iex.Triop.arg3);
            case Iex_Qop: 
               return isBogusAtom(e->Iex.Qop.arg1)
                      || isBogusAtom(e->Iex.Qop.arg2)
                      || isBogusAtom(e->Iex.Qop.arg3)
                      || isBogusAtom(e->Iex.Qop.arg4);
            case Iex_Mux0X:
               return isBogusAtom(e->Iex.Mux0X.cond)
                      || isBogusAtom(e->Iex.Mux0X.expr0)
                      || isBogusAtom(e->Iex.Mux0X.exprX);
            case Iex_Load: 
               return isBogusAtom(e->Iex.Load.addr);
            case Iex_CCall:
               for (i = 0; e->Iex.CCall.args[i]; i++)
                  if (isBogusAtom(e->Iex.CCall.args[i]))
                     return True;
               return False;
            default: 
               goto unhandled;
         }
      case Ist_Dirty:
         d = st->Ist.Dirty.details;
         for (i = 0; d->args[i]; i++)
            if (isBogusAtom(d->args[i]))
               return True;
         if (d->guard && isBogusAtom(d->guard))
            return True;
         if (d->mAddr && isBogusAtom(d->mAddr))
            return True;
         return False;
      case Ist_Put:
         return isBogusAtom(st->Ist.Put.data);
      case Ist_PutI:
         return isBogusAtom(st->Ist.PutI.ix) 
                || isBogusAtom(st->Ist.PutI.data);
      case Ist_Store:
         return isBogusAtom(st->Ist.Store.addr) 
                || isBogusAtom(st->Ist.Store.data);
      case Ist_Exit:
         return isBogusAtom(st->Ist.Exit.guard);
      case Ist_AbiHint:
         return isBogusAtom(st->Ist.AbiHint.base)
                || isBogusAtom(st->Ist.AbiHint.nia);
      case Ist_NoOp:
      case Ist_IMark:
      case Ist_MBE:
         return False;
      default: 
      unhandled:
         ppIRStmt(st);
         VG_(tool_panic)("hasBogusLiterals");
   }
}


IRSB* MC_(instrument) ( VgCallbackClosure* closure,
                        IRSB* bb_in, 
                        VexGuestLayout* layout, 
                        VexGuestExtents* vge,
                        IRType gWordTy, IRType hWordTy )
{
   Bool    verboze = 0||False;
   Bool    bogus;
   Int     i, j, first_stmt;
   IRStmt* st;
   MCEnv   mce;
   IRSB*   bb;

   if (gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
   }

   /* Check we're not completely nuts */
   tl_assert(sizeof(UWord)  == sizeof(void*));
   tl_assert(sizeof(Word)   == sizeof(void*));
   tl_assert(sizeof(Addr)   == sizeof(void*));
   tl_assert(sizeof(ULong)  == 8);
   tl_assert(sizeof(Long)   == 8);
   tl_assert(sizeof(Addr64) == 8);
   tl_assert(sizeof(UInt)   == 4);
   tl_assert(sizeof(Int)    == 4);

   tl_assert(MC_(clo_mc_level) >= 1 && MC_(clo_mc_level) <= 3);

   /* Set up SB */
   bb = deepCopyIRSBExceptStmts(bb_in);

   /* Set up the running environment.  Only .bb is modified as we go
      along. */
   mce.bb             = bb;
   mce.trace          = verboze;
   mce.layout         = layout;
   mce.n_originalTmps = bb->tyenv->types_used;
   mce.hWordTy        = hWordTy;
   mce.bogusLiterals  = False;
   mce.tmpMapV        = LibVEX_Alloc(mce.n_originalTmps * sizeof(IRTemp));
   mce.tmpMapB        = LibVEX_Alloc(mce.n_originalTmps * sizeof(IRTemp));
   for (i = 0; i < mce.n_originalTmps; i++) {
      mce.tmpMapV[i] = IRTemp_INVALID;
      mce.tmpMapB[i] = IRTemp_INVALID;
   }

   /* Make a preliminary inspection of the statements, to see if there
      are any dodgy-looking literals.  If there are, we generate
      extra-detailed (hence extra-expensive) instrumentation in
      places.  Scan the whole bb even if dodgyness is found earlier,
      so that the flatness assertion is applied to all stmts. */

   bogus = False;

   for (i = 0; i < bb_in->stmts_used; i++) {

      st = bb_in->stmts[i];
      tl_assert(st);
      tl_assert(isFlatIRStmt(st));

      if (!bogus) {
         bogus = checkForBogusLiterals(st);
         if (0 && bogus) {
            VG_(printf)("bogus: ");
            ppIRStmt(st);
            VG_(printf)("\n");
         }
      }

   }

   mce.bogusLiterals = bogus;

   /* Copy verbatim any IR preamble preceding the first IMark */

   tl_assert(mce.bb == bb);

   i = 0;
   while (i < bb_in->stmts_used && bb_in->stmts[i]->tag != Ist_IMark) {

      st = bb_in->stmts[i];
      tl_assert(st);
      tl_assert(isFlatIRStmt(st));

      stmt( 'C', &mce, bb_in->stmts[i] );
      i++;
   }

   /* Nasty problem.  IR optimisation of the pre-instrumented IR may
      cause the IR following the preamble to contain references to IR
      temporaries defined in the preamble.  Because the preamble isn't
      instrumented, these temporaries don't have any shadows.
      Nevertheless uses of them following the preamble will cause
      memcheck to generate references to their shadows.  End effect is
      to cause IR sanity check failures, due to references to
      non-existent shadows.  This is only evident for the complex
      preambles used for function wrapping on TOC-afflicted platforms
      (ppc64-linux, ppc32-aix5, ppc64-aix5).

      The following loop therefore scans the preamble looking for
      assignments to temporaries.  For each one found it creates an
      assignment to the corresponding (V) shadow temp, marking it as
      'defined'.  This is the same resulting IR as if the main
      instrumentation loop before had been applied to the statement
      'tmp = CONSTANT'.

      Similarly, if origin tracking is enabled, we must generate an
      assignment for the corresponding origin (B) shadow, claiming
      no-origin, as appropriate for a defined value.
   */
   for (j = 0; j < i; j++) {
      if (bb_in->stmts[j]->tag == Ist_WrTmp) {
         /* findShadowTmpV checks its arg is an original tmp;
            no need to assert that here. */
         IRTemp tmp_o = bb_in->stmts[j]->Ist.WrTmp.tmp;
         IRTemp tmp_v = findShadowTmpV(&mce, tmp_o);
         IRType ty_v  = typeOfIRTemp(bb->tyenv, tmp_v);
         assign( 'V', &mce, tmp_v, definedOfType( ty_v ) );
         if (MC_(clo_mc_level) == 3) {
            IRTemp tmp_b = findShadowTmpB(&mce, tmp_o);
            tl_assert(typeOfIRTemp(bb->tyenv, tmp_b) == Ity_I32);
            assign( 'B', &mce, tmp_b, mkU32(0)/* UNKNOWN ORIGIN */);
         }
         if (0) {
            VG_(printf)("create shadow tmp(s) for preamble tmp [%d] ty ", j);
            ppIRType( ty_v );
            VG_(printf)("\n");
         }
      }
   }

   /* Iterate over the remaining stmts to generate instrumentation. */

   tl_assert(bb_in->stmts_used > 0);
   tl_assert(i >= 0);
   tl_assert(i < bb_in->stmts_used);
   tl_assert(bb_in->stmts[i]->tag == Ist_IMark);

   for (/* use current i*/; i <  bb_in->stmts_used; i++) {

      st = bb_in->stmts[i];
      first_stmt = bb->stmts_used;

      if (verboze) {
         VG_(printf)("\n");
         ppIRStmt(st);
         VG_(printf)("\n");
      }

      if (MC_(clo_mc_level) == 3)
         schemeS( &mce, st );

      /* Generate instrumentation code for each stmt ... */

      switch (st->tag) {

         case Ist_WrTmp:
            assign( 'V', &mce, findShadowTmpV(&mce, st->Ist.WrTmp.tmp), 
                               expr2vbits( &mce, st->Ist.WrTmp.data) );
            break;

         case Ist_Put:
            do_shadow_PUT( &mce, 
                           st->Ist.Put.offset,
                           st->Ist.Put.data,
                           NULL /* shadow atom */ );
            break;

         case Ist_PutI:
            do_shadow_PUTI( &mce, 
                            st->Ist.PutI.descr,
                            st->Ist.PutI.ix,
                            st->Ist.PutI.bias,
                            st->Ist.PutI.data );
            break;

         case Ist_Store:
            do_shadow_Store( &mce, st->Ist.Store.end,
                                   st->Ist.Store.addr, 0/* addr bias */,
                                   st->Ist.Store.data,
                                   NULL /* shadow data */ );
            break;

         case Ist_Exit:
            complainIfUndefined( &mce, st->Ist.Exit.guard );
            break;

         case Ist_IMark:
            break;

         case Ist_NoOp:
         case Ist_MBE:
            break;

         case Ist_Dirty:
            do_shadow_Dirty( &mce, st->Ist.Dirty.details );
            break;

         case Ist_AbiHint:
            do_AbiHint( &mce, st->Ist.AbiHint.base,
                              st->Ist.AbiHint.len,
                              st->Ist.AbiHint.nia );
            break;

         default:
            VG_(printf)("\n");
            ppIRStmt(st);
            VG_(printf)("\n");
            VG_(tool_panic)("memcheck: unhandled IRStmt");

      } /* switch (st->tag) */

      if (0 && verboze) {
         for (j = first_stmt; j < bb->stmts_used; j++) {
            VG_(printf)("   ");
            ppIRStmt(bb->stmts[j]);
            VG_(printf)("\n");
         }
         VG_(printf)("\n");
      }

      /* ... and finally copy the stmt itself to the output. */
      stmt('C', &mce, st);

   }

   /* Now we need to complain if the jump target is undefined. */
   first_stmt = bb->stmts_used;

   if (verboze) {
      VG_(printf)("bb->next = ");
      ppIRExpr(bb->next);
      VG_(printf)("\n\n");
   }

   complainIfUndefined( &mce, bb->next );

   if (0 && verboze) {
      for (j = first_stmt; j < bb->stmts_used; j++) {
         VG_(printf)("   ");
         ppIRStmt(bb->stmts[j]);
         VG_(printf)("\n");
      }
      VG_(printf)("\n");
   }

   return bb;
}

/*------------------------------------------------------------*/
/*--- Post-tree-build final tidying                        ---*/
/*------------------------------------------------------------*/

/* This exploits the observation that Memcheck often produces
   repeated conditional calls of the form

   Dirty G MC_(helperc_value_check0/1/4/8_fail)(UInt otag)

   with the same guard expression G guarding the same helper call.
   The second and subsequent calls are redundant.  This usually
   results from instrumentation of guest code containing multiple
   memory references at different constant offsets from the same base
   register.  After optimisation of the instrumentation, you get a
   test for the definedness of the base register for each memory
   reference, which is kinda pointless.  MC_(final_tidy) therefore
   looks for such repeated calls and removes all but the first. */

/* A struct for recording which (helper, guard) pairs we have already
   seen. */
typedef
   struct { void* entry; IRExpr* guard; }
   Pair;

/* Return True if e1 and e2 definitely denote the same value (used to
   compare guards).  Return False if unknown; False is the safe
   answer.  Since guest registers and guest memory do not have the
   SSA property we must return False if any Gets or Loads appear in
   the expression. */

static Bool sameIRValue ( IRExpr* e1, IRExpr* e2 )
{
   if (e1->tag != e2->tag)
      return False;
   switch (e1->tag) {
      case Iex_Const:
         return eqIRConst( e1->Iex.Const.con, e2->Iex.Const.con );
      case Iex_Binop:
         return e1->Iex.Binop.op == e2->Iex.Binop.op 
                && sameIRValue(e1->Iex.Binop.arg1, e2->Iex.Binop.arg1)
                && sameIRValue(e1->Iex.Binop.arg2, e2->Iex.Binop.arg2);
      case Iex_Unop:
         return e1->Iex.Unop.op == e2->Iex.Unop.op 
                && sameIRValue(e1->Iex.Unop.arg, e2->Iex.Unop.arg);
      case Iex_RdTmp:
         return e1->Iex.RdTmp.tmp == e2->Iex.RdTmp.tmp;
      case Iex_Mux0X:
         return sameIRValue( e1->Iex.Mux0X.cond, e2->Iex.Mux0X.cond )
                && sameIRValue( e1->Iex.Mux0X.expr0, e2->Iex.Mux0X.expr0 )
                && sameIRValue( e1->Iex.Mux0X.exprX, e2->Iex.Mux0X.exprX );
      case Iex_Qop:
      case Iex_Triop:
      case Iex_CCall:
         /* be lazy.  Could define equality for these, but they never
            appear to be used. */
         return False;
      case Iex_Get:
      case Iex_GetI:
      case Iex_Load:
         /* be conservative - these may not give the same value each
            time */
         return False;
      case Iex_Binder:
         /* should never see this */
         /* fallthrough */
      default:
         VG_(printf)("mc_translate.c: sameIRValue: unhandled: ");
         ppIRExpr(e1); 
         VG_(tool_panic)("memcheck:sameIRValue");
         return False;
   }
}

/* See if 'pairs' already has an entry for (entry, guard).  Return
   True if so.  If not, add an entry. */

static 
Bool check_or_add ( XArray* /*of Pair*/ pairs, IRExpr* guard, void* entry )
{
   Pair  p;
   Pair* pp;
   Int   i, n = VG_(sizeXA)( pairs );
   for (i = 0; i < n; i++) {
      pp = VG_(indexXA)( pairs, i );
      if (pp->entry == entry && sameIRValue(pp->guard, guard))
         return True;
   }
   p.guard = guard;
   p.entry = entry;
   VG_(addToXA)( pairs, &p );
   return False;
}

static Bool is_helperc_value_checkN_fail ( HChar* name )
{
   return
      0==VG_(strcmp)(name, "MC_(helperc_value_check0_fail_no_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check1_fail_no_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check4_fail_no_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check8_fail_no_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check0_fail_w_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check1_fail_w_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check4_fail_w_o)")
      || 0==VG_(strcmp)(name, "MC_(helperc_value_check8_fail_w_o)");
}

IRSB* MC_(final_tidy) ( IRSB* sb_in )
{
   Int i;
   IRStmt*   st;
   IRDirty*  di;
   IRExpr*   guard;
   IRCallee* cee;
   Bool      alreadyPresent;
   XArray*   pairs = VG_(newXA)( VG_(malloc), "mc.ft.1",
                                 VG_(free), sizeof(Pair) );
   /* Scan forwards through the statements.  Each time a call to one
      of the relevant helpers is seen, check if we have made a
      previous call to the same helper using the same guard
      expression, and if so, delete the call. */
   for (i = 0; i < sb_in->stmts_used; i++) {
      st = sb_in->stmts[i];
      tl_assert(st);
      if (st->tag != Ist_Dirty)
         continue;
      di = st->Ist.Dirty.details;
      guard = di->guard;
      if (!guard)
         continue;
      if (0) { ppIRExpr(guard); VG_(printf)("\n"); }
      cee = di->cee;
      if (!is_helperc_value_checkN_fail( cee->name )) 
         continue;
       /* Ok, we have a call to helperc_value_check0/1/4/8_fail with
          guard 'guard'.  Check if we have already seen a call to this
          function with the same guard.  If so, delete it.  If not,
          add it to the set of calls we do know about. */
      alreadyPresent = check_or_add( pairs, guard, cee->addr );
      if (alreadyPresent) {
         sb_in->stmts[i] = IRStmt_NoOp();
         if (0) VG_(printf)("XX\n");
      }
   }
   VG_(deleteXA)( pairs );
   return sb_in;
}


/*------------------------------------------------------------*/
/*--- Origin tracking stuff                                ---*/
/*------------------------------------------------------------*/

static IRTemp findShadowTmpB ( MCEnv* mce, IRTemp orig )
{
   tl_assert(orig < mce->n_originalTmps);
   if (mce->tmpMapB[orig] == IRTemp_INVALID) {
      mce->tmpMapB[orig] 
         = newIRTemp(mce->bb->tyenv, Ity_I32);
   }
   return mce->tmpMapB[orig];
}

static IRAtom* gen_maxU32 ( MCEnv* mce, IRAtom* b1, IRAtom* b2 )
{
   return assignNew( 'B', mce, Ity_I32, binop(Iop_Max32U, b1, b2) );
}

static IRAtom* gen_load_b ( MCEnv* mce, Int szB, 
                            IRAtom* baseaddr, Int offset )
{
   void*    hFun;
   HChar*   hName;
   IRTemp   bTmp;
   IRDirty* di;
   IRType   aTy   = typeOfIRExpr( mce->bb->tyenv, baseaddr );
   IROp     opAdd = aTy == Ity_I32 ? Iop_Add32 : Iop_Add64;
   IRAtom*  ea    = baseaddr;
   if (offset != 0) {
      IRAtom* off = aTy == Ity_I32 ? mkU32( offset )
                                   : mkU64( (Long)(Int)offset );
      ea = assignNew( 'B', mce, aTy, binop(opAdd, ea, off));
   }
   bTmp = newIRTemp(mce->bb->tyenv, mce->hWordTy);

   switch (szB) {
      case 1: hFun  = (void*)&MC_(helperc_b_load1);
              hName = "MC_(helperc_b_load1)";
              break;
      case 2: hFun  = (void*)&MC_(helperc_b_load2);
              hName = "MC_(helperc_b_load2)";
              break;
      case 4: hFun  = (void*)&MC_(helperc_b_load4);
              hName = "MC_(helperc_b_load4)";
              break;
      case 8: hFun  = (void*)&MC_(helperc_b_load8);
              hName = "MC_(helperc_b_load8)";
              break;
      case 16: hFun  = (void*)&MC_(helperc_b_load16);
               hName = "MC_(helperc_b_load16)";
               break;
      default:
         VG_(printf)("mc_translate.c: gen_load_b: unhandled szB == %d\n", szB);
         tl_assert(0);
   }
   di = unsafeIRDirty_1_N(
           bTmp, 1/*regparms*/, hName, VG_(fnptr_to_fnentry)( hFun ),
           mkIRExprVec_1( ea )
        );
   /* no need to mess with any annotations.  This call accesses
      neither guest state nor guest memory. */
   stmt( 'B', mce, IRStmt_Dirty(di) );
   if (mce->hWordTy == Ity_I64) {
      /* 64-bit host */
      IRTemp bTmp32 = newIRTemp(mce->bb->tyenv, Ity_I32);
      assign( 'B', mce, bTmp32, unop(Iop_64to32, mkexpr(bTmp)) );
      return mkexpr(bTmp32);
   } else {
      /* 32-bit host */
      return mkexpr(bTmp);
   }
}
static void gen_store_b ( MCEnv* mce, Int szB,
                          IRAtom* baseaddr, Int offset, IRAtom* dataB )
{
   void*    hFun;
   HChar*   hName;
   IRDirty* di;
   IRType   aTy   = typeOfIRExpr( mce->bb->tyenv, baseaddr );
   IROp     opAdd = aTy == Ity_I32 ? Iop_Add32 : Iop_Add64;
   IRAtom*  ea    = baseaddr;
   if (offset != 0) {
      IRAtom* off = aTy == Ity_I32 ? mkU32( offset )
                                   : mkU64( (Long)(Int)offset );
      ea = assignNew(  'B', mce, aTy, binop(opAdd, ea, off));
   }
   if (mce->hWordTy == Ity_I64)
      dataB = assignNew( 'B', mce, Ity_I64, unop(Iop_32Uto64, dataB));

   switch (szB) {
      case 1: hFun  = (void*)&MC_(helperc_b_store1);
              hName = "MC_(helperc_b_store1)";
              break;
      case 2: hFun  = (void*)&MC_(helperc_b_store2);
              hName = "MC_(helperc_b_store2)";
              break;
      case 4: hFun  = (void*)&MC_(helperc_b_store4);
              hName = "MC_(helperc_b_store4)";
              break;
      case 8: hFun  = (void*)&MC_(helperc_b_store8);
              hName = "MC_(helperc_b_store8)";
              break;
      case 16: hFun  = (void*)&MC_(helperc_b_store16);
               hName = "MC_(helperc_b_store16)";
               break;
      default:
         tl_assert(0);
   }
   di = unsafeIRDirty_0_N( 2/*regparms*/,
           hName, VG_(fnptr_to_fnentry)( hFun ),
           mkIRExprVec_2( ea, dataB )
        );
   /* no need to mess with any annotations.  This call accesses
      neither guest state nor guest memory. */
   stmt( 'B', mce, IRStmt_Dirty(di) );
}

static IRAtom* narrowTo32 ( MCEnv* mce, IRAtom* e ) {
   IRType eTy = typeOfIRExpr(mce->bb->tyenv, e);
   if (eTy == Ity_I64)
      return assignNew( 'B', mce, Ity_I32, unop(Iop_64to32, e) );
   if (eTy == Ity_I32)
      return e;
   tl_assert(0);
}

static IRAtom* zWidenFrom32 ( MCEnv* mce, IRType dstTy, IRAtom* e ) {
   IRType eTy = typeOfIRExpr(mce->bb->tyenv, e);
   tl_assert(eTy == Ity_I32);
   if (dstTy == Ity_I64)
      return assignNew( 'B', mce, Ity_I64, unop(Iop_32Uto64, e) );
   tl_assert(0);
}

static IRAtom* schemeE ( MCEnv* mce, IRExpr* e )
{
   tl_assert(MC_(clo_mc_level) == 3);

   switch (e->tag) {

      case Iex_GetI: {
         IRRegArray* descr_b;
         IRAtom      *t1, *t2, *t3, *t4;
         IRRegArray* descr      = e->Iex.GetI.descr;
         IRType equivIntTy 
            = MC_(get_otrack_reg_array_equiv_int_type)(descr);
         /* If this array is unshadowable for whatever reason, use the
            usual approximation. */
         if (equivIntTy == Ity_INVALID)
            return mkU32(0);
         tl_assert(sizeofIRType(equivIntTy) >= 4);
         tl_assert(sizeofIRType(equivIntTy) == sizeofIRType(descr->elemTy));
         descr_b = mkIRRegArray( descr->base + 2*mce->layout->total_sizeB,
                                 equivIntTy, descr->nElems );
         /* Do a shadow indexed get of the same size, giving t1.  Take
            the bottom 32 bits of it, giving t2.  Compute into t3 the
            origin for the index (almost certainly zero, but there's
            no harm in being completely general here, since iropt will
            remove any useless code), and fold it in, giving a final
            value t4. */
         t1 = assignNew( 'B', mce, equivIntTy, 
                          IRExpr_GetI( descr_b, e->Iex.GetI.ix, 
                                                e->Iex.GetI.bias ));
         t2 = narrowTo32( mce, t1 );
         t3 = schemeE( mce, e->Iex.GetI.ix );
         t4 = gen_maxU32( mce, t2, t3 );
         return t4;
      }
      case Iex_CCall: {
         Int i;
         IRAtom*  here;
         IRExpr** args = e->Iex.CCall.args;
         IRAtom*  curr = mkU32(0);
         for (i = 0; args[i]; i++) {
            tl_assert(i < 32);
            tl_assert(isOriginalAtom(mce, args[i]));
            /* Only take notice of this arg if the callee's
               mc-exclusion mask does not say it is to be excluded. */
            if (e->Iex.CCall.cee->mcx_mask & (1<<i)) {
               /* the arg is to be excluded from definedness checking.
                  Do nothing. */
               if (0) VG_(printf)("excluding %s(%d)\n",
                                  e->Iex.CCall.cee->name, i);
            } else {
               /* calculate the arg's definedness, and pessimistically
                  merge it in. */
               here = schemeE( mce, args[i] );
               curr = gen_maxU32( mce, curr, here );
            }
         }
         return curr;
      }
      case Iex_Load: {
         Int dszB;
         dszB = sizeofIRType(e->Iex.Load.ty);
         /* assert that the B value for the address is already
            available (somewhere) */
         tl_assert(isIRAtom(e->Iex.Load.addr));
         tl_assert(mce->hWordTy == Ity_I32 || mce->hWordTy == Ity_I64);
         return gen_load_b( mce, dszB, e->Iex.Load.addr, 0 );
      }
      case Iex_Mux0X: {
         IRAtom* b1 = schemeE( mce, e->Iex.Mux0X.cond );
         IRAtom* b2 = schemeE( mce, e->Iex.Mux0X.expr0 );
         IRAtom* b3 = schemeE( mce, e->Iex.Mux0X.exprX );
         return gen_maxU32( mce, b1, gen_maxU32( mce, b2, b3 ));
      }
      case Iex_Qop: {
         IRAtom* b1 = schemeE( mce, e->Iex.Qop.arg1 );
         IRAtom* b2 = schemeE( mce, e->Iex.Qop.arg2 );
         IRAtom* b3 = schemeE( mce, e->Iex.Qop.arg3 );
         IRAtom* b4 = schemeE( mce, e->Iex.Qop.arg4 );
         return gen_maxU32( mce, gen_maxU32( mce, b1, b2 ),
                                 gen_maxU32( mce, b3, b4 ) );
      }
      case Iex_Triop: {
         IRAtom* b1 = schemeE( mce, e->Iex.Triop.arg1 );
         IRAtom* b2 = schemeE( mce, e->Iex.Triop.arg2 );
         IRAtom* b3 = schemeE( mce, e->Iex.Triop.arg3 );
         return gen_maxU32( mce, b1, gen_maxU32( mce, b2, b3 ) );
      }
      case Iex_Binop: {
         IRAtom* b1 = schemeE( mce, e->Iex.Binop.arg1 );
         IRAtom* b2 = schemeE( mce, e->Iex.Binop.arg2 );
         return gen_maxU32( mce, b1, b2 );
      }
      case Iex_Unop: {
         IRAtom* b1 = schemeE( mce, e->Iex.Unop.arg );
         return b1;
      }
      case Iex_Const:
         return mkU32(0);
      case Iex_RdTmp:
         return mkexpr( findShadowTmpB( mce, e->Iex.RdTmp.tmp ));
      case Iex_Get: {
         Int b_offset = MC_(get_otrack_shadow_offset)( 
                           e->Iex.Get.offset,
                           sizeofIRType(e->Iex.Get.ty) 
                        );
         tl_assert(b_offset >= -1
                   && b_offset <= mce->layout->total_sizeB -4);
         if (b_offset >= 0) {
            /* FIXME: this isn't an atom! */
            return IRExpr_Get( b_offset + 2*mce->layout->total_sizeB,
                               Ity_I32 );
         }
         return mkU32(0);
      }
      default:
         VG_(printf)("mc_translate.c: schemeE: unhandled: ");
         ppIRExpr(e); 
         VG_(tool_panic)("memcheck:schemeE");
   }
}

static void do_origins_Dirty ( MCEnv* mce, IRDirty* d )
{
   // This is a hacked version of do_shadow_Dirty
   Int       i, n, toDo, gSz, gOff;
   IRAtom    *here, *curr;
   IRTemp    dst;

   /* First check the guard. */
   curr = schemeE( mce, d->guard );

   /* Now round up all inputs and maxU32 over them. */

   /* Inputs: unmasked args */
   for (i = 0; d->args[i]; i++) {
      if (d->cee->mcx_mask & (1<<i)) {
         /* ignore this arg */
      } else {
         here = schemeE( mce, d->args[i] );
         curr = gen_maxU32( mce, curr, here );
      }
   }

   /* Inputs: guest state that we read. */
   for (i = 0; i < d->nFxState; i++) {
      tl_assert(d->fxState[i].fx != Ifx_None);
      if (d->fxState[i].fx == Ifx_Write)
         continue;

      /* Ignore any sections marked as 'always defined'. */
      if (isAlwaysDefd(mce, d->fxState[i].offset, d->fxState[i].size )) {
         if (0)
         VG_(printf)("memcheck: Dirty gst: ignored off %d, sz %d\n",
                     d->fxState[i].offset, d->fxState[i].size );
         continue;
      }

      /* This state element is read or modified.  So we need to
         consider it.  If larger than 4 bytes, deal with it in 4-byte
         chunks. */
      gSz  = d->fxState[i].size;
      gOff = d->fxState[i].offset;
      tl_assert(gSz > 0);
      while (True) {
         Int b_offset;
         if (gSz == 0) break;
         n = gSz <= 4 ? gSz : 4;
         /* update 'curr' with maxU32 of the state slice 
            gOff .. gOff+n-1 */
         b_offset = MC_(get_otrack_shadow_offset)(gOff, 4);
         if (b_offset != -1) {
            here = assignNew( 'B',mce,
                               Ity_I32,
                               IRExpr_Get(b_offset + 2*mce->layout->total_sizeB,
                                          Ity_I32));
            curr = gen_maxU32( mce, curr, here );
         }
         gSz -= n;
         gOff += n;
      }

   }

   /* Inputs: memory */

   if (d->mFx != Ifx_None) {
      /* Because we may do multiple shadow loads/stores from the same
         base address, it's best to do a single test of its
         definedness right now.  Post-instrumentation optimisation
         should remove all but this test. */
      tl_assert(d->mAddr);
      here = schemeE( mce, d->mAddr );
      curr = gen_maxU32( mce, curr, here );
   }

   /* Deal with memory inputs (reads or modifies) */
   if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify) {
      toDo   = d->mSize;
      /* chew off 32-bit chunks.  We don't care about the endianness
         since it's all going to be condensed down to a single bit,
         but nevertheless choose an endianness which is hopefully
         native to the platform. */
      while (toDo >= 4) {
         here = gen_load_b( mce, 4, d->mAddr, d->mSize - toDo );
         curr = gen_maxU32( mce, curr, here );
         toDo -= 4;
      }
      /* handle possible 16-bit excess */
      while (toDo >= 2) {
         here = gen_load_b( mce, 2, d->mAddr, d->mSize - toDo );
         curr = gen_maxU32( mce, curr, here );
         toDo -= 2;
      }
      tl_assert(toDo == 0); /* also need to handle 1-byte excess */
   }

   /* Whew!  So curr is a 32-bit B-value which should give an origin
      of some use if any of the inputs to the helper are undefined.
      Now we need to re-distribute the results to all destinations. */

   /* Outputs: the destination temporary, if there is one. */
   if (d->tmp != IRTemp_INVALID) {
      dst   = findShadowTmpB(mce, d->tmp);
      assign( 'V', mce, dst, curr );
   }

   /* Outputs: guest state that we write or modify. */
   for (i = 0; i < d->nFxState; i++) {
      tl_assert(d->fxState[i].fx != Ifx_None);
      if (d->fxState[i].fx == Ifx_Read)
         continue;

      /* Ignore any sections marked as 'always defined'. */
      if (isAlwaysDefd(mce, d->fxState[i].offset, d->fxState[i].size ))
         continue;

      /* This state element is written or modified.  So we need to
         consider it.  If larger than 4 bytes, deal with it in 4-byte
         chunks. */
      gSz  = d->fxState[i].size;
      gOff = d->fxState[i].offset;
      tl_assert(gSz > 0);
      while (True) {
         Int b_offset;
         if (gSz == 0) break;
         n = gSz <= 4 ? gSz : 4;
         /* Write 'curr' to the state slice gOff .. gOff+n-1 */
         b_offset = MC_(get_otrack_shadow_offset)(gOff, 4);
         if (b_offset != -1) {
           stmt( 'B', mce, IRStmt_Put(b_offset + 2*mce->layout->total_sizeB,
                                      curr ));
         }
         gSz -= n;
         gOff += n;
      }
   }

   /* Outputs: memory that we write or modify.  Same comments about
      endianness as above apply. */
   if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify) {
      toDo   = d->mSize;
      /* chew off 32-bit chunks */
      while (toDo >= 4) {
         gen_store_b( mce, 4, d->mAddr, d->mSize - toDo, curr );
         toDo -= 4;
      }
      /* handle possible 16-bit excess */
      while (toDo >= 2) {
         gen_store_b( mce, 2, d->mAddr, d->mSize - toDo, curr );
         toDo -= 2;
      }
      tl_assert(toDo == 0); /* also need to handle 1-byte excess */
   }
}

static void schemeS ( MCEnv* mce, IRStmt* st )
{
   tl_assert(MC_(clo_mc_level) == 3);

   switch (st->tag) {

      case Ist_AbiHint:
         /* The value-check instrumenter handles this - by arranging
            to pass the address of the next instruction to
            MC_(helperc_MAKE_STACK_UNINIT).  This is all that needs to
            happen for origin tracking w.r.t. AbiHints.  So there is
            nothing to do here. */
         break;

      case Ist_PutI: {
         IRRegArray* descr_b;
         IRAtom      *t1, *t2, *t3, *t4;
         IRRegArray* descr = st->Ist.PutI.descr;
         IRType equivIntTy
            = MC_(get_otrack_reg_array_equiv_int_type)(descr);
         /* If this array is unshadowable for whatever reason,
            generate no code. */
         if (equivIntTy == Ity_INVALID)
            break;
         tl_assert(sizeofIRType(equivIntTy) >= 4);
         tl_assert(sizeofIRType(equivIntTy) == sizeofIRType(descr->elemTy));
         descr_b
            = mkIRRegArray( descr->base + 2*mce->layout->total_sizeB,
                            equivIntTy, descr->nElems );
         /* Compute a value to Put - the conjoinment of the origin for
            the data to be Put-ted (obviously) and of the index value
            (not so obviously). */
         t1 = schemeE( mce, st->Ist.PutI.data );
         t2 = schemeE( mce, st->Ist.PutI.ix );
         t3 = gen_maxU32( mce, t1, t2 );
         t4 = zWidenFrom32( mce, equivIntTy, t3 );
         stmt( 'B', mce, IRStmt_PutI( descr_b, st->Ist.PutI.ix,
                                      st->Ist.PutI.bias, t4 ));
         break;
      }
      case Ist_Dirty:
         do_origins_Dirty( mce, st->Ist.Dirty.details );
         break;
      case Ist_Store: {
         Int     dszB;
         IRAtom* dataB;
         /* assert that the B value for the address is already
            available (somewhere) */
         tl_assert(isIRAtom(st->Ist.Store.addr));
         dszB = sizeofIRType(
                   typeOfIRExpr(mce->bb->tyenv, st->Ist.Store.data ));
         dataB = schemeE( mce, st->Ist.Store.data );
         gen_store_b( mce, dszB, st->Ist.Store.addr, 0/*offset*/, dataB );
         break;
      }
      case Ist_Put: {
         Int b_offset
            = MC_(get_otrack_shadow_offset)(
                 st->Ist.Put.offset,
                 sizeofIRType(typeOfIRExpr(mce->bb->tyenv, st->Ist.Put.data))
              );
         if (b_offset >= 0) {
            /* FIXME: this isn't an atom! */
            stmt( 'B', mce, IRStmt_Put(b_offset + 2*mce->layout->total_sizeB, 
                                       schemeE( mce, st->Ist.Put.data )) );
         }
         break;
      }
      case Ist_WrTmp:
         assign( 'B', mce, findShadowTmpB(mce, st->Ist.WrTmp.tmp),
                           schemeE(mce, st->Ist.WrTmp.data) );
         break;
      case Ist_MBE:
      case Ist_NoOp:
      case Ist_Exit:
      case Ist_IMark:
         break;
      default:
         VG_(printf)("mc_translate.c: schemeS: unhandled: ");
         ppIRStmt(st); 
         VG_(tool_panic)("memcheck:schemeS");
   }
}


/*--------------------------------------------------------------------*/
/*--- end                                           mc_translate.c ---*/
/*--------------------------------------------------------------------*/
