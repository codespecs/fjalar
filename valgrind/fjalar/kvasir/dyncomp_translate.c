
/*--------------------------------------------------------------------*/
/*--- Instrument IR to perform tag operations for DynComp.         ---*/
/*--- (Analogous to mc_translate.c for MemCheck)                   ---*/
/*---                                          dyncomp_translate.c ---*/
/*--------------------------------------------------------------------*/

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool.

  Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
  Programming Languages and Software Engineering Group

  Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
  Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
  Copyright (C) 2000-2009 Julian Seward (jseward@acm.org),

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

#include "my_libc.h"

#include "mc_include.h"
#include "kvasir_main.h"
#include "dyncomp_translate.h"
#include "dyncomp_main.h"
#include "../fjalar_include.h"
#include "vex_common.h"

extern char dyncomp_profile_tags;
static
IRAtom* expr2tags_LDle_DC ( DCEnv* dce, IRType ty, IRAtom* addr, UInt bias );

/* Find the tmp currently shadowing the given original tmp.  If none
   so far exists, allocate one.  */
IRTemp findShadowTmp_DC ( DCEnv* dce, IRTemp orig )
{

  tl_assert(orig < dce->n_originalTmps);
   if (dce->tmpMap[orig] == IRTemp_INVALID) {
      dce->tmpMap[orig]
         = newTemp(dce->mce,
                     //shadowType_DC(dce->bb->tyenv->types[orig]));
                     Ity_Word,
                   DC); // PG - tags are always word-sized
   }

   return dce->tmpMap[orig];
}

/* (used for sanity checks only): is this an atom which looks
   like it's from original code? */
static Bool isOriginalAtom_DC ( DCEnv* dce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_RdTmp && a1->Iex.RdTmp.tmp < dce->n_originalTmps)
      return True;
   return False;
}

/* (used for sanity checks only): is this an atom which looks
   like it's from shadow code? */
static Bool isShadowAtom_DC ( DCEnv* dce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_RdTmp && a1->Iex.RdTmp.tmp >= dce->n_originalTmps)
      return True;
   return False;
}

static IRAtom* assignNew_DC ( DCEnv* dce, IRType ty, IRExpr* e ) {
   IRTemp t = newTemp(dce->mce, Ity_Word, DC);
   assign_DC('V', dce, t, e);
   return mkexpr(t);
}

// (comment added 2006)
// TODO: Is this the correct behavior for our purposes? - pgbovine
//       Not really - smcc
/* Set the annotations on a dirty helper to indicate that the stack
   pointer and instruction pointers might be read.  This is the
   behaviour of all 'emit-a-complaint' style functions we might
   call. */
static void setHelperAnns_DC ( DCEnv* dce, IRDirty* di ) {
   di->nFxState = 2;
   di->fxState[0].fx     = Ifx_Read;
   di->fxState[0].offset = dce->layout->offset_SP;
   di->fxState[0].size   = dce->layout->sizeof_SP;
   di->fxState[0].nRepeats  = 0;
   di->fxState[0].repeatLen = 0;
   di->fxState[1].fx     = Ifx_Read;
   di->fxState[1].offset = dce->layout->offset_IP;
   di->fxState[1].size   = dce->layout->sizeof_IP;
   di->fxState[1].nRepeats  = 0;
   di->fxState[1].repeatLen = 0;
}

// A PUT stores a value into the guest state
void do_shadow_PUT_DC ( DCEnv* dce,  Int offset,
                     IRAtom* atom, IRAtom* vatom )
{
   IRType ty;
   if (atom) {
      tl_assert(!vatom);
      tl_assert(isOriginalAtom_DC(dce, atom));
      vatom = expr2tags_DC( dce, atom );
   } else {
      tl_assert(vatom);
      tl_assert(isShadowAtom_DC(dce, vatom));
   }

   ty = typeOfIRExpr(dce->bb->tyenv, vatom);
   tl_assert(ty != Ity_I1);

   // Don't do a PUT of tags into SP or FP in order to avoid tons of
   // false mergings of relative address literals derived from
   // arithmetic with SP
   if (offset == dce->layout->offset_SP || offset == dce->layout->offset_FP) {
      return;
   }

   /* Do a plain shadow Put. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   //printf("PUT_DC offset: %d, %d, %d\n", offset, dce->layout->total_sizeB, ((4*offset)+(3*dce->layout->total_sizeB)));
   stmt_DC('V',  dce,
         IRStmt_Put( (4 * offset) + (3 * dce->layout->total_sizeB), vatom ) );
}

// A PUTI stores a value (dynamically indexed) into the guest state
// (for x86, this seems to be only used for floating point values)
void do_shadow_PUTI_DC ( DCEnv* dce, IRPutI *puti)
{
   IRAtom* vatom;
   IRType  ty;
   IRRegArray *new_descr;
   IRRegArray* descr = puti->descr;
   IRAtom*     ix    = puti->ix;
   Int         bias  = puti->bias;
   IRAtom*     atom  = puti->data;

   tl_assert(isOriginalAtom_DC(dce,atom));
   vatom = expr2tags_DC( dce, atom );
   //   tl_assert(sameKindedAtoms(atom, vatom));
   ty   = descr->elemTy;
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom_DC(dce,ix));
   /* Do a cloned version of the Put that refers to the tag shadow
      area. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   new_descr
      = mkIRRegArray( (4 * descr->base) + (3 * dce->layout->total_sizeB),
                   Ity_Word, descr->nElems); // Tags are word-sized

   stmt_DC( 'V', dce, IRStmt_PutI(mkIRPutI(new_descr, ix, bias, vatom)));
}

static
IRExpr* shadow_GET_DC ( DCEnv* dce, Int offset, IRType ty )
{
   tl_assert(ty != Ity_I1);
   /* return a cloned version of the Get that refers to the tag
      shadow area. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)

   // Return a special tag for a GET call into SP or FP,
   // in order to avoid tons of false mergings of relative address
   // literals derived from arithmetic with the stack pointer
   // (comment added 2006)
   /* XXX This won't do the right thing if your code uses %ebp for
      some purpose other than the frame pointer. Let's hope that
      doesn't happen too often in unoptimized code. The only better
      solution would be to track with an independent bit which values
      are ESP-derived, which would be a pain. -SMcC */
   if (offset == dce->layout->offset_SP || offset == dce->layout->offset_FP) {
      return IRExpr_Const(IRConst_UWord(WEAK_FRESH_TAG));
   }

   // The following assert seems to be a problem.  Older versions of the
   // GNU Multiple Precision Arithmetic Library (GMP) - which is included
   // within GNU libc - use lots of mm register operands for the x86-64.
   // Also, I don't understand why there is no similar assert for the
   // PUT case. I am going to comment it out for now. mlr 11/18/2015.
   // Note: this problem was discovered running Kvasir on the Jenkins
   // test system.  Jenkins is hosted on the machine tern which has
   // out of date software.  If the assert is needed, we will need to
   // update the libc on tern.

   // The floating-point stack on the x86 is located between offsets
   // 64 and 128 so we don't want somebody requesting a GET into this
   // region since our (4 * offset) trick won't work properly here.
   // This should (hopefully) never happen since floating-point
   // accesses are always done using GETI's.
   // tl_assert(!(((UInt)offset >= offsetof(VexGuestArchState, guest_FPREG)) &&
   //       ((UInt)offset <  offsetof(VexGuestArchState, guest_FPREG)
   //       + 8 * sizeof(ULong))));

   //printf("GET_DC offset: %d, %d, %d\n", offset, dce->layout->total_sizeB, ((4*offset)+(3*dce->layout->total_sizeB)));
   return IRExpr_Get( (4 * offset) + (3 * dce->layout->total_sizeB),
                      Ity_Word ); // Tags are word-sized
}

static
IRExpr* shadow_GETI_DC ( DCEnv* dce, IRRegArray* descr, IRAtom* ix, Int bias )
{
   IRType ty   = descr->elemTy;
   IRRegArray *new_descr;
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom_DC(dce,ix));
   /* return a cloned version of the Get that refers to the
      tag shadow area. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   new_descr
      = mkIRRegArray( (4 * descr->base) + (3 * dce->layout->total_sizeB),
                   Ity_Word, descr->nElems); // Tags are word-sized

   return IRExpr_GetI( new_descr, ix, bias );
}

// Handling of clean helper function calls in the target program's
// translated IR: Treat all arguments (exprvec) as 'interacting' with
// one another and merge all of their respective tags and return the
// value of one of the tags as the result of the helper call.  This is
// because helpers probably implement weird x86 instructions which are
// too difficult to handle purely in IR so these n-ary operations are
// probably interactions.  E.g. if the args are (a, b, c, d, e), then
// you should merge tag(a) with tag(b), tag(c), tag(d), and tag(e)
// then return tag(a)

// By some informal observation, it seems like '>' and '>='
// comparisons are translated into clean C calls.  The correct
// behavior is to merge the tags of all arguments but return a new tag
// of 0 so that the tags do not propagate to the results.  Without
// further testing on what other opeations are translated into IR as
// clean C calls, I will simply return a tag of 0 for now.
static
IRAtom* handleCCall_DC ( DCEnv* dce,
                         IRAtom** exprvec, IRCallee* cee )
{
  if (exprvec && exprvec[0]) {
      IRAtom* first = expr2tags_DC(dce, exprvec[0]);
      Int i;
      IRAtom* cur;
      IRDirty* di;
      IRTemp   datatag;

      for (i = 1; exprvec[i]; i++) {
         tl_assert(i < 32);
         tl_assert(isOriginalAtom_DC(dce, exprvec[i]));
         /* Only take notice of this arg if the callee's mc-exclusion
            mask does not say it is to be excluded. */
         if (cee->mcx_mask & (1<<i)) {
            /* the arg is to be excluded from definedness checking.  Do
               nothing. (I guess we do nothing also just like mkLazyN) */
            if (0) printf("excluding %s(%d)\n", cee->name, i);
         } else {
            /* merge the tags of first and current arguments */
            cur = expr2tags_DC(dce, exprvec[i]);

            // (comment added 2006)
            // TODO: Why is this dirty rather than clean? - pgbovine
            //       Because it has side effects? - smcc
            datatag = newTemp(dce->mce, Ity_Word, DC);
            di = unsafeIRDirty_1_N(datatag,
                                   2,
                                   "MC_(helperc_MERGE_TAGS_RETURN_0)",
                                   &MC_(helperc_MERGE_TAGS_RETURN_0),
                                   mkIRExprVec_2( first, cur ));

            setHelperAnns_DC( dce, di );
            stmt_DC('V', dce, IRStmt_Dirty(di));
         }
      }
      // Return the tag of the first argument, if there is one
      //      return first;

      // Or, always return 0
      return IRExpr_Const(IRConst_UWord(0));
   }
   else {
      return IRExpr_Const(IRConst_UWord(0));
   }
}

/*------------------------------------------------------------*/
/*--- Generate shadow values from all kinds of IRExprs.    ---*/
/*------------------------------------------------------------*/


UInt numConsts = 0;

// This is where we need to add calls to helper functions to
// merge tags because here is where the 'interactions' take place

// Yes, this code can be cleaned up a bit, but I'll leave it
// as one big switch statement for now in order to provide
// flexibility for future edits

static
IRAtom* expr2tags_Qop_DC ( DCEnv* dce,
                           IROp op,
                           IRAtom* atom1, IRAtom* atom2,
                           IRAtom* atom3, IRAtom* atom4 )
{
   IRAtom* vatom1 = expr2tags_DC( dce, atom1 );
   IRAtom* vatom2 = expr2tags_DC( dce, atom2 );
   IRAtom* vatom3 = expr2tags_DC( dce, atom3 );
   IRAtom* vatom4 = expr2tags_DC( dce, atom4 );


   if (dyncomp_profile_tags) {
      if ((atom1->tag == Iex_Const) ||
          (atom2->tag == Iex_Const) ||
          (atom3->tag == Iex_Const) ||
          (atom4->tag == Iex_Const)) {
         numConsts++;
      }
   }

   // Punt early!
   if (dyncomp_dataflow_only_mode ||
       dyncomp_dataflow_comparisons_mode) {
      return IRExpr_Const(IRConst_UWord(0));
   }

   tl_assert(isOriginalAtom_DC(dce,atom1));
   tl_assert(isOriginalAtom_DC(dce,atom2));
   tl_assert(isOriginalAtom_DC(dce,atom3));
   tl_assert(isOriginalAtom_DC(dce,atom4));
   tl_assert(isShadowAtom_DC(dce,vatom1));
   tl_assert(isShadowAtom_DC(dce,vatom2));
   tl_assert(isShadowAtom_DC(dce,vatom3));
   tl_assert(isShadowAtom_DC(dce,vatom4));

   switch (op) {

      case Iop_MAddF64:
      case Iop_MAddF64r32:                  // only used by ppc
      case Iop_MSubF64:                     // only used by arm64 mips ppc s390
      case Iop_MSubF64r32:                  // only used by ppc
      case Iop_MAddF32:
      case Iop_MSubF32:                     // only used by arm64 mips s390
      case Iop_MAddF128:                    // only used by ppc s390
      case Iop_MSubF128:                    // only used by ppc s390
      case Iop_NegMAddF128:                 // only used by ppc
      case Iop_NegMSubF128:                 // only used by ppc

         // from libvex_ir.h:
      /* :: IRRoundingMode(I32) x F64 x F64 x F64 -> F64
         or IRRoundingMode(I32) x F32 x F32 x F32 -> F32
            (computes arg2 * arg3 +/- arg4) */

         // If we are running in units mode, then we should merge the
         // tags of the 3rd and 4th operands:
         if (dyncomp_units_mode) {
            return mkIRExprCCall (Ity_Word,
                                  2 /*Int regparms*/,
                                  "MC_(helperc_MERGE_TAGS)",
                                  &MC_(helperc_MERGE_TAGS),
                                  mkIRExprVec_2( vatom3, vatom4 ));
         }
         // Ok, if we are running in the default mode, then we should
         // merge the tags of the 2nd, 3rd, and 4th operands:
         else {
            return mkIRExprCCall (Ity_Word,
                                  3 /*Int regparms*/,
                                  "MC_(helperc_MERGE_3_TAGS)",
                                  &MC_(helperc_MERGE_3_TAGS),
                                  mkIRExprVec_3( vatom2, vatom3, vatom4 ));
         }
         break;

      // Doesn't look like any interactions  (markro)
      case Iop_64x4toV256:
         break;

// Unimplemented
      case Iop_Rotx32:                      // only used by mips
      case Iop_Rotx64:                      // only used by mips

      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2tags_Qop");
   }

   VG_(tool_panic)("memcheck:expr2tags_Qop");
}

static
IRAtom* expr2tags_Triop_DC ( DCEnv* dce,
                             IROp op,
                             IRAtom* atom1, IRAtom* atom2, IRAtom* atom3 )
{
   IRAtom* vatom1 = expr2tags_DC( dce, atom1 );
   IRAtom* vatom2 = expr2tags_DC( dce, atom2 );
   IRAtom* vatom3 = expr2tags_DC( dce, atom3 );

   if (dyncomp_profile_tags) {
      if ((atom1->tag == Iex_Const) ||
          (atom2->tag == Iex_Const) ||
          (atom3->tag == Iex_Const)) {
         numConsts++;
      }
   }

   // Punt early!
   if (dyncomp_dataflow_only_mode ||
       dyncomp_dataflow_comparisons_mode) {
      return IRExpr_Const(IRConst_UWord(0));
   }

   tl_assert(isOriginalAtom_DC(dce,atom1));
   tl_assert(isOriginalAtom_DC(dce,atom2));
   tl_assert(isOriginalAtom_DC(dce,atom3));
   tl_assert(isShadowAtom_DC(dce,vatom1));
   tl_assert(isShadowAtom_DC(dce,vatom2));
   tl_assert(isShadowAtom_DC(dce,vatom3));

   //   tl_assert(sameKindedAtoms(atom1,vatom1));
   //   tl_assert(sameKindedAtoms(atom2,vatom2));
   //   tl_assert(sameKindedAtoms(atom3,vatom3));

   switch (op) {
      // The first arg. is the rounding mode, and the second and third
      // args. actually participate in the operation, so merge the
      // tags of the second and third args. as appropriate:
      // I32(rm) x F64 x F64 -> F64
      // (Other types as implied by opcodes.)

      case Iop_AddF16:                      // only used by arm64
      case Iop_SubF16:                      // only used by arm64
      case Iop_AddF32:                      // only used by arm mips s390 arm64
      case Iop_SubF32:                      // only used by arm mips s390 arm64
      case Iop_AddF64:
      case Iop_AddF64r32:                   // only used by ppc
      case Iop_SubF64:
      case Iop_SubF64r32:                   // only used by ppc
      case Iop_AddD64:                      // only used by ppc s390
      case Iop_SubD64:                      // only used by ppc s390
      case Iop_AddF128:                     // only used by ppc s390
      case Iop_SubF128:                     // only used by ppc s390
      case Iop_AddD128:                     // only used by ppc s390
      case Iop_SubD128:                     // only used by ppc s390
      case Iop_Add32Fx4:
      case Iop_Add16Fx8:                    // only used by arm64
      case Iop_Add32Fx8:
      case Iop_Add64Fx2:
      case Iop_Add64Fx4:
      case Iop_Sub32Fx4:
      case Iop_Sub16Fx8:                    // only used by arm64
      case Iop_Sub32Fx8:
      case Iop_Sub64Fx2:
      case Iop_Sub64Fx4:

         return mkIRExprCCall (Ity_Word,
                               2 /*Int regparms*/,
                               "MC_(helperc_MERGE_TAGS)",
                               &MC_(helperc_MERGE_TAGS),
                               // VERY IMPORTANT!!!  We want to merge the
                               // tags of the 2nd and 3rd operands!!!
                               // Because the first one is a rounding
                               // mode (I think)
                               /* I32(rm) x F64 x F64 -> F64 */
                               mkIRExprVec_2( vatom2, vatom3 ));

      case Iop_MulF32:                      // only used by arm mips s390 arm64
      case Iop_DivF32:                      // only used by arm mips s390 arm64
      case Iop_MulF64:
      case Iop_MulF64r32:                   // only used by ppc
      case Iop_DivF64:
      case Iop_DivF64r32:                   // only used by ppc
      case Iop_MulD64:                      // only used by ppc s390
      case Iop_DivD64:                      // only used by ppc s390
      case Iop_MulF128:                     // only used by ppc s390
      case Iop_DivF128:                     // only used by ppc s390
      case Iop_MulD128:                     // only used by ppc s390
      case Iop_DivD128:                     // only used by ppc s390
      case Iop_Div32Fx4:
      case Iop_Div32Fx8:
      case Iop_Div64Fx2:
      case Iop_Div64Fx4:
      case Iop_Mul32Fx4:
      case Iop_Mul32Fx8:
      case Iop_Mul64Fx2:
      case Iop_Mul64Fx4:

         if (!dyncomp_units_mode) {
            return mkIRExprCCall (Ity_Word,
                                  2 /*Int regparms*/,
                                  "MC_(helperc_MERGE_TAGS)",
                                  &MC_(helperc_MERGE_TAGS),
                                  // VERY IMPORTANT!!!  We want to merge the
                                  // tags of the 2nd and 3rd operands!!!
                                  // Because the first one is a rounding
                                  // mode (I think)
                                  /* I32(rm) x F64 x F64 -> F64 */
                                  mkIRExprVec_2( vatom2, vatom3 ));
         }
         // Else fall through ...
         break;

      // pgbovine - Hmmm, these don't look like interactions:
      case Iop_ScaleF64:
      case Iop_Yl2xF64:
      case Iop_Yl2xp1F64:
      case Iop_AtanF64:
      case Iop_PRemF64:
      case Iop_PRem1F64:
      case Iop_PRemC3210F64:
      case Iop_PRem1C3210F64:
         break;

// Unimplemented
      case Iop_QuantizeD64:                 // only used by ppc s390
      case Iop_QuantizeD128:                // only used by ppc s390
      case Iop_SignificanceRoundD64:        // only used by ppc s390
      case Iop_SignificanceRoundD128:       // only used by ppc s390
      case Iop_Slice64:                     // only used by arm
      case Iop_SliceV128:                   // only used by arm arm64
      case Iop_SetElem8x8:                  // only used by arm
      case Iop_SetElem8x16:                 // only used by s390
      case Iop_SetElem16x4:                 // only used by arm
      case Iop_SetElem16x8:                 // only used by s390
      case Iop_SetElem32x2:                 // only used by arm
      case Iop_SetElem32x4:                 // only used by s390
      case Iop_SetElem64x2:                 // only used by s390
      case Iop_Perm8x16x2:                  // only used by s390
      case Iop_F32x4_2toQ16x8:              // only used by mips
      case Iop_F64x2_2toQ32x4:              // only used by mips
      case Iop_Scale2_32Fx4:                // only used by mips
      case Iop_Scale2_64Fx2:                // only used by mips
      case Iop_2xMultU64Add128CarryOut:     // only used by ppc

      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2tags_Triop");
   }

   return IRExpr_Const(IRConst_UWord(0));
}

static
IRAtom* expr2tags_Binop_DC ( DCEnv* dce,
                              IROp op,
                              IRAtom* atom1, IRAtom* atom2 )
{
   IRAtom* vatom1 = expr2tags_DC( dce, atom1 );
   IRAtom* vatom2 = expr2tags_DC( dce, atom2 );

   void*        helper = 0;
   const HChar* hname = 0;

   if (dyncomp_profile_tags) {
      if ((atom1->tag == Iex_Const) ||
          (atom2->tag == Iex_Const)) {
         numConsts++;
      }
   }

   //   IRDirty* di;
   //   IRTemp   datatag;

   tl_assert(isOriginalAtom_DC(dce,atom1));
   tl_assert(isOriginalAtom_DC(dce,atom2));
   tl_assert(isShadowAtom_DC(dce,vatom1));
   tl_assert(isShadowAtom_DC(dce,vatom2));

   // pgbovine - vatom1 and vatom2 are tmps, atom1 and atom2 can be
   // consts, right?  I dunno.
   //   tl_assert(sameKindedAtoms(atom1,vatom1));
   //   tl_assert(sameKindedAtoms(atom2,vatom2));

   // Set the appropriate helper functions for binary
   // operations which are deemed as 'interactions'
   // (The conditions within this switch will have
   //  to be heavily refined as this tool matures)

   // These opcodes come from the definition of IROp in libvex_ir.h:
   switch (op) {

      // ---------------------------------
      // Merge the tags of both arguments:
      // ---------------------------------

      // Arithmetic operations and bitwise AND/OR/XOR's
      // definitely qualify as interactions:

      // Integers:
   case Iop_Add8:
   case Iop_Add16:
   case Iop_Add32:
   case Iop_Add64:
   case Iop_Sub8:
   case Iop_Sub16:
   case Iop_Sub32:
   case Iop_Sub64:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* Signless mul.  MullS/MullU is elsewhere. */
   case Iop_Mul8:
   case Iop_Mul16:                       // unused
   case Iop_Mul32:
   case Iop_Mul64:                       // only used by mips ppc arm64
   case Iop_Or1:
   case Iop_Or8:
   case Iop_Or16:
   case Iop_Or32:
   case Iop_Or64:
   case Iop_And1:
   case Iop_And8:
   case Iop_And16:
   case Iop_And32:
   case Iop_And64:
   case Iop_Xor8:
   case Iop_Xor16:                       // unused
   case Iop_Xor32:
   case Iop_Xor64:
      /* Widening multiplies */
   case Iop_MullS8:
   case Iop_MullS16:
   case Iop_MullS32:
   case Iop_MullS64:
   case Iop_MullU8:
   case Iop_MullU16:
   case Iop_MullU32:
   case Iop_MullU64:
      /* Division */
      // (comment added 2005)
      /* TODO: clarify semantics wrt rounding, negative values, whatever */
   case Iop_DivS32:                      // only used by arm mips ppc arm64
   case Iop_DivS32E:                     // only used by ppc
   case Iop_DivS64:                      // only used by mips ppc arm64
   case Iop_DivS64E:                     // only used by ppc
   case Iop_DivU32:                      // only used by arm mips ppc arm64
   case Iop_DivU32E:                     // only used by ppc
   case Iop_DivU64:                      // only used by mips ppc arm64
   case Iop_DivU64E:                     // only used by ppc
   case Iop_DivU128:                     // only used by ppc
   case Iop_DivS128:                     // only used by ppc
   case Iop_DivU128E:                    // only used by ppc
   case Iop_DivS128E:                    // only used by ppc
   case Iop_ModU128:                     // only used by ppc
   case Iop_ModS128:                     // only used by ppc


   case Iop_DivModU64to32: // :: I64,I32 -> I64
                           // of which lo half is div and hi half is mod
   case Iop_DivModS64to32: // ditto, signed

   case Iop_DivModU128to64: // :: V128,I64 -> V128
                            // of which lo half is div and hi half is mod
   case Iop_DivModS128to64: // ditto, signed

   case Iop_DivModS64to64: // :: I64,I64 -> I128   // only used by mips s390
                           // of which lo half is div and hi half is mod
   case Iop_DivModU64to64: // :: I64,I64 -> I128   // only used by mips s390
                           // of which lo half is div and hi half is mod
   case Iop_DivModS32to32: // :: I32,I32 -> I64    // only used by mips
                           // of which lo half is div and hi half is mod
   case Iop_DivModU32to32: // :: I32,I32 -> I64    // only used by mips
                           // of which lo half is div and hi half is mod

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* ------------------ 64-bit SIMD Integer. ------------------ */

      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x8:
   case Iop_Add16x2:                     // only used by arm
   case Iop_Add16x4:
   case Iop_Add32x2:
   case Iop_Add32Fx2:                    // only used by arm
   case Iop_Add8x4:                      // only used by arm
   case Iop_HAdd8Sx4:                    // only used by arm
   case Iop_HAdd8Ux4:                    // only used by arm mips
   case Iop_HAdd16Sx2:                   // only used by arm
   case Iop_HAdd16Ux2:                   // only used by arm
   case Iop_QAdd8Ux8:
   case Iop_QAdd16Ux4:
   case Iop_QAdd8Sx8:
   case Iop_QAdd16Sx4:
   case Iop_QAdd8Ux4:                    // only used by arm
   case Iop_QAdd16Ux2:                   // only used by arm
   case Iop_QAdd8Sx4:                    // only used by arm
   case Iop_QAdd16Sx2:                   // only used by arm
   case Iop_QAdd32Sx2:                   // only used by arm
   case Iop_QAdd32Ux2:                   // only used by arm
   case Iop_QAdd64Sx1:                   // only used by arm
   case Iop_QAdd64Ux1:                   // only used by arm

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x8:
   case Iop_Sub16x2:                     // only used by arm
   case Iop_Sub16x4:
   case Iop_Sub32x2:
   case Iop_Sub32Fx2:                    // only used by arm
   case Iop_Sub8x4:                      // only used by arm
   case Iop_HSub8Sx4:                    // only used by arm
   case Iop_HSub8Ux4:                    // only used by arm mips
   case Iop_HSub16Sx2:                   // only used by arm mips
   case Iop_HSub16Ux2:                   // only used by arm
   case Iop_QSub8Ux8:
   case Iop_QSub16Ux4:
   case Iop_QSub8Sx8:
   case Iop_QSub16Sx4:
   case Iop_QSub16Sx2:                   // only used by arm
   case Iop_QSub16Ux2:                   // only used by arm
   case Iop_QSub8Sx4:                    // only used by arm
   case Iop_QSub8Ux4:                    // only used by arm mips
   case Iop_QSub32Sx2:                   // only used by arm
   case Iop_QSub32Ux2:                   // only used by arm
   case Iop_QSub64Sx1:                   // only used by arm
   case Iop_QSub64Ux1:                   // only used by arm

      /* AVERAGING: note: (arg1 + arg2 + 1) >>u 1 */
   case Iop_Avg8Ux8:
   case Iop_Avg8Ux16:
   case Iop_Avg8Ux32:
   case Iop_Avg8Sx16:                    // only used by ppc mips s390
   case Iop_Avg16Ux4:
   case Iop_Avg16Ux8:
   case Iop_Avg16Ux16:
   case Iop_Avg16Sx8:                    // only used by ppc mips s390
   case Iop_Avg32Sx4:                    // only used by ppc mips s390
   case Iop_Avg32Ux4:                    // only used by ppc mips s390
   case Iop_Avg64Sx2:                    // only used by s390
   case Iop_Avg64Ux2:                    // only used by s390

      /* MIN/MAX */
   case Iop_Max8Sx8:                     // only used by arm
   case Iop_Max16Sx4:
   case Iop_Max32Sx2:                    // only used by arm
   case Iop_Max32Fx2:                    // only used by arm
   case Iop_Max8Ux8:
   case Iop_Max16Ux4:                    // only used by arm
   case Iop_Max32Ux2:                    // only used by arm
   case Iop_Min8Sx8:                     // only used by arm
   case Iop_Min16Sx4:
   case Iop_Min32Sx2:                    // only used by arm
   case Iop_Min32Fx2:                    // only used by arm
   case Iop_Min8Ux8:
   case Iop_Min16Ux4:                    // only used by arm
   case Iop_Min32Ux2:                    // only used by arm

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* MULTIPLICATION (normal / high half of signed/unsigned) */
   case Iop_Mul8x8:                      // only used by arm
   case Iop_Mul16x4:
   case Iop_Mul32x2:
   case Iop_Mul32Fx2:                    // only used by arm
   case Iop_Mull8Ux8:                    // only used by arm arm64
   case Iop_Mull16Ux4:                   // only used by arm arm64
   case Iop_Mull32Ux2:                   // only used by arm arm64
   case Iop_Mull8Sx8:                    // only used by arm arm64
   case Iop_Mull16Sx4:                   // only used by arm arm64
   case Iop_Mull32Sx2:                   // only used by arm arm64
   case Iop_MullEven8Sx16:               // only used by ppc s390
   case Iop_MullEven8Ux16:               // only used by ppc s390
   case Iop_MullEven16Sx8:               // only used by ppc s390
   case Iop_MullEven16Ux8:               // only used by ppc s390
   case Iop_MulHi16Ux4:
   case Iop_MulHi16Sx4:
   case Iop_QDMulHi16Sx4:                // only used by arm
   case Iop_QDMulHi32Sx2:                // only used by arm
   case Iop_QRDMulHi16Sx4:               // only used by arm
   case Iop_QRDMulHi32Sx2:               // only used by arm
   case Iop_QDMull16Sx4:                 // only used by arm arm64
   case Iop_QDMull32Sx2:                 // only used by arm arm64
   case Iop_PolynomialMul8x8:            // only used by arm
   case Iop_PolynomialMull8x8:           // only used by arm arm64

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;


      /* ------------------ 128-bit SIMD FP. ------------------ */

      /* --- 32x4 vector FP --- */

   case Iop_Max32Fx4:
   case Iop_Min32Fx4:

   case Iop_Max32Fx8:
   case Iop_Min32Fx8:

      /* --- 32x4 lowest-lane-only scalar FP --- */

   case Iop_Add32F0x4:
   case Iop_Sub32F0x4:
   case Iop_Max32F0x4:
   case Iop_Min32F0x4:

      /* --- 64x2 vector FP --- */

   case Iop_Max64Fx2:
   case Iop_Min64Fx2:
   case Iop_Max64Fx4:
   case Iop_Min64Fx4:

      /* --- 64x2 lowest-lane-only scalar FP --- */

   case Iop_Add64F0x2:
   case Iop_Sub64F0x2:
   case Iop_Max64F0x2:
   case Iop_Min64F0x2:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* --- 32x4 lowest-lane-only scalar FP --- */
   case Iop_Mul32F0x4:
   case Iop_Div32F0x4:
      /* --- 64x2 lowest-lane-only scalar FP --- */
   case Iop_Mul64F0x2:
   case Iop_Div64F0x2:

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* ------------------ 128-bit SIMD Integer. ------------------ */
      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x16:
   case Iop_Add16x8:
   case Iop_Add32x4:
   case Iop_Add64x2:
   case Iop_Add128x1:                    // only used by s390
   case Iop_QAdd8Ux16:
   case Iop_QAdd16Ux8:
   case Iop_QAdd8Sx16:
   case Iop_QAdd16Sx8:
   case Iop_QAdd32Sx4:                   // only used by arm mips ppc arm64
   case Iop_QAdd32Ux4:                   // only used by arm mips ppc arm64
   case Iop_QAdd64Sx2:                   // only used by arm mips arm64
   case Iop_QAdd64Ux2:                   // only used by arm mips arm64

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x16:
   case Iop_Sub16x8:
   case Iop_Sub32x4:
   case Iop_Sub64x2:
   case Iop_Sub128x1:
   case Iop_QSub8Ux16:
   case Iop_QSub16Ux8:
   case Iop_QSub8Sx16:
   case Iop_QSub16Sx8:
   case Iop_QSub32Sx4:                   // only used by arm mips ppc arm64
   case Iop_QSub32Ux4:                   // only used by arm mips ppc arm64
   case Iop_QSub64Sx2:                   // only used by arm mips arm64
   case Iop_QSub64Ux2:                   // only used by arm mips arm64

      /* MIN/MAX */
   case Iop_Max8Sx16:
   case Iop_Max8Ux16:
   case Iop_Max16Sx8:
   case Iop_Max16Ux8:
   case Iop_Max32Sx4:
   case Iop_Max32Ux4:
   case Iop_Min8Sx16:
   case Iop_Min8Ux16:
   case Iop_Min16Sx8:
   case Iop_Min16Ux8:
   case Iop_Min32Sx4:
   case Iop_Min32Ux4:

      /* ------------------ 256-bit SIMD Integer. ------------------ */

   case Iop_V128HLtoV256:

      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x32:
   case Iop_Add16x16:
   case Iop_Add32x8:
   case Iop_Add64x4:
   case Iop_QAdd8Ux32:
   case Iop_QAdd16Ux16:
   case Iop_QAdd8Sx32:
   case Iop_QAdd16Sx16:

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x32:
   case Iop_Sub16x16:
   case Iop_Sub32x8:
   case Iop_Sub64x4:
   case Iop_QSub8Ux32:
   case Iop_QSub16Ux16:
   case Iop_QSub8Sx32:
   case Iop_QSub16Sx16:

      /* MIN/MAX */
   case Iop_Max8Sx32:
   case Iop_Max16Sx16:
   case Iop_Max32Sx8:
   case Iop_Max8Ux32:
   case Iop_Max16Ux16:
   case Iop_Max32Ux8:
   case Iop_Min8Sx32:
   case Iop_Min16Sx16:
   case Iop_Min32Sx8:
   case Iop_Min8Ux32:
   case Iop_Min16Ux16:
   case Iop_Min32Ux8:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* ------------------ 128-bit SIMD Integer. ------------------ */
      /* BITWISE OPS */
   case Iop_AndV128:
   case Iop_OrV128:
   case Iop_XorV128:
   case Iop_AndV256:
   case Iop_OrV256:
   case Iop_XorV256:

      /* MULTIPLICATION (normal / high half of signed/unsigned) */
   case Iop_Mul8x16:                     // only used by arm mips s390 arm64
   case Iop_Mul16x8:
   case Iop_Mul32x4:
   case Iop_MulHi16Sx8:
   case Iop_MulHi16Ux8:
   case Iop_PolynomialMul8x16:           // only used by arm arm64
   case Iop_QDMulHi16Sx8:                // only used by arm mips arm64
   case Iop_QDMulHi32Sx4:                // only used by arm mips arm64
   case Iop_QRDMulHi16Sx8:               // only used by arm mips arm64
   case Iop_QRDMulHi32Sx4:               // only used by arm mips arm64

      /* ------------------ 256-bit SIMD Integer. ------------------ */
   case Iop_Mul16x16:
   case Iop_Mul32x8:
   case Iop_MulHi16Sx16:
   case Iop_MulHi16Ux16:

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      // Conversions where we concatenate two arguments together to form a
      // larger one seem to qualify as interactions:

      /* 8 <-> 16 bit conversions */
   case Iop_8HLto16:    // :: (I8,I8) -> I16
      /* 16 <-> 32 bit conversions */
   case Iop_16HLto32:   // :: (I16,I16) -> I32
      /* 32 <-> 64 bit conversions */
   case Iop_32HLto64:   // :: (I32,I32) -> I64
      /* 64 <-> 128 bit conversions */
   case Iop_64HLto128:  // :: (I64,I64) -> I128

      // 128-bit SIMD FP
   case Iop_64HLtoV128:   // :: (I64,I64) -> V128

      // Weird 64-bit SIMD narrowing and interleave seem like interactions,
      // although this is a bit shadiy
      /* NARROWING -- narrow 2xI64 into 1xI64, hi half from left arg */
   case Iop_QNarrowBin16Sto8Ux8:
   case Iop_QNarrowBin16Sto8Ux16:
   case Iop_QNarrowBin16Sto8Sx8:
   case Iop_QNarrowBin16Sto8Sx16:
   case Iop_QNarrowBin16Uto8Ux16:        // only used by ppc s390
   case Iop_QNarrowBin32Uto16Ux8:        // only used by ppc s390
   case Iop_QNarrowBin32Sto16Sx4:
   case Iop_QNarrowBin32Sto16Sx8:
   case Iop_QNarrowBin32Sto16Ux8:

   case Iop_NarrowBin16to8x8:
   case Iop_NarrowBin32to16x4:

      /* INTERLEAVING -- interleave lanes from low or high halves of
         operands.  Most-significant result lane is from the left
         arg. */
   case Iop_CatEvenLanes8x8:             // only used by arm
   case Iop_CatEvenLanes16x4:
   case Iop_CatOddLanes8x8:              // only used by arm
   case Iop_CatOddLanes16x4:
   case Iop_InterleaveEvenLanes8x8:      // only used by arm
   case Iop_InterleaveEvenLanes16x4:     // only used by arm
   case Iop_InterleaveHI8x8:
   case Iop_InterleaveHI16x4:
   case Iop_InterleaveHI32x2:
   case Iop_InterleaveLO8x8:
   case Iop_InterleaveLO16x4:
   case Iop_InterleaveLO32x2:
   case Iop_InterleaveOddLanes8x8:       // only used by arm
   case Iop_InterleaveOddLanes16x4:      // only used by arm

      // Ditto for 128-bit SIMD integer narrowing and interleaving

   case Iop_CatEvenLanes8x16:            // only used by arm arm64
   case Iop_CatEvenLanes16x8:            // only used by arm arm64
   case Iop_CatEvenLanes32x4:            // only used by arm ppc arm64
   case Iop_CatOddLanes8x16:             // only used by arm arm64
   case Iop_CatOddLanes16x8:             // only used by arm arm64
   case Iop_CatOddLanes32x4:             // only used by arm ppc arm64
   case Iop_InterleaveEvenLanes8x16:     // only used by arm mips s390
   case Iop_InterleaveEvenLanes16x8:     // only used by arm mips
   case Iop_InterleaveEvenLanes32x4:     // only used by arm mips
   case Iop_InterleaveOddLanes8x16:      // only used by arm mips s390
   case Iop_InterleaveOddLanes16x8:      // only used by arm mips
   case Iop_InterleaveOddLanes32x4:      // only used by arm mips

      /* NARROWING -- narrow 2xV128 into 1xV128, hi half from left arg */
   case Iop_NarrowBin16to8x16:
   case Iop_NarrowBin32to16x8:

      /* INTERLEAVING -- interleave lanes from low or high halves of
         operands.  Most-significant result lane is from the left
         arg. */
   case Iop_InterleaveHI8x16:
   case Iop_InterleaveHI16x8:
   case Iop_InterleaveHI32x4:
   case Iop_InterleaveHI64x2:
   case Iop_InterleaveLO8x16:
   case Iop_InterleaveLO16x8:
   case Iop_InterleaveLO32x4:
   case Iop_InterleaveLO64x2:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      // Comparisons qualify as interactions:, but they are special
      // because we do not want to pass along the tag to the result.

      //    e.g. x = (a < b)

      // We merge the tags of 'a' and 'b' but don't pass the tag of either one
      // to 'x'.  Instead, 'x' gets a tag of 0.  After all, 'x' is really just a
      // boolean '0' or '1' without any interesting semantic meaning.

      // The only reason why you would want to pass along the tag to the result
      // is so that you can have correct behavior on nested expressions like
      // (a + ((b - c) * d)), but you never really nest comparisons, right?

      // You don't do ((a < b) > c) or anything like that since the result of a
      // comparison is a 0 or 1 which really can't be compared with other stuff.

      /* Integer comparisons. */
   case Iop_CmpEQ8:
   case Iop_CmpEQ16:
   case Iop_CmpEQ32:
   case Iop_CmpEQ64:
   case Iop_CmpLE32S:
   case Iop_CmpLE32U:
   case Iop_CmpLE64S:
   case Iop_CmpLE64U:
   case Iop_CmpLT32S:
   case Iop_CmpLT32U:
   case Iop_CmpLT64S:
   case Iop_CmpLT64U:
   case Iop_CmpNE8:
   case Iop_CmpNE16:
   case Iop_CmpNE32:
   case Iop_CmpNE64:
   case Iop_CmpORD32S:                   // only used by ppc
   case Iop_CmpORD32U:                   // only used by ppc
   case Iop_CmpORD64S:                   // only used by ppc
   case Iop_CmpORD64U:                   // only used by ppc
   case Iop_ExpCmpNE8:                   // unused?
   case Iop_ExpCmpNE16:                  // unused
   case Iop_ExpCmpNE32:
   case Iop_ExpCmpNE64:

     // New CAS operations. They're semantically identical to normal comparisons
     // They're used by memcheck to differentiate the compares done by a CAS and
     // a normal compare.
   case Iop_CasCmpEQ8:                   // unused
   case Iop_CasCmpEQ16:                  // unused
   case Iop_CasCmpEQ32:
   case Iop_CasCmpEQ64:
   case Iop_CasCmpNE8:
   case Iop_CasCmpNE16:                  // unused
   case Iop_CasCmpNE32:                  // unused
   case Iop_CasCmpNE64:                  // unused

      // Floating-point comparison
   case Iop_CmpD64:                      // only used by ppc s390
   case Iop_CmpD128:                     // only used by ppc s390
   case Iop_CmpF16:                      // only used by arm64
   case Iop_CmpF32:                      // only used by mips s390 arm64
   case Iop_CmpF64:
   case Iop_CmpF128:                     // only used by s390
   case Iop_CmpExpD64:                   // only used by s390
   case Iop_CmpExpD128:                  // only used by s390

   case Iop_MaxNumF32:                   // only used by arm mips
   case Iop_MinNumF32:                   // only used by arm mips
   case Iop_MaxNumF64:                   // only used by arm mips
   case Iop_MinNumF64:                   // only used by arm mips

      // 64-bit SIMD integer comparisons
      /* MISC (vector integer cmp != 0) */

      /* COMPARISON */
   case Iop_CmpEQ8x8:
   case Iop_CmpEQ16x4:
   case Iop_CmpEQ32Fx2:                  // only used by arm
   case Iop_CmpEQ32x2:
   case Iop_CmpGE32Fx2:                  // only used by arm
   case Iop_CmpGT8Sx8:
   case Iop_CmpGT8Ux8:                   // only used by arm
   case Iop_CmpGT16Sx4:
   case Iop_CmpGT16Ux4:                  // only used by arm
   case Iop_CmpGT32Fx2:                  // only used by arm
   case Iop_CmpGT32Sx2:
   case Iop_CmpGT32Ux2:                  // only used by arm

      // 128-bit SIMD FP
   case Iop_CmpEQ16Fx8:                  // only used by arm64
   case Iop_CmpEQ32F0x4:
   case Iop_CmpEQ32Fx4:
   case Iop_CmpEQ64F0x2:
   case Iop_CmpEQ64Fx2:
   case Iop_CmpEQ64x2:
   case Iop_CmpGE32Fx4:                  // only used by arm ppc
   case Iop_CmpGT32Fx4:                  // only used by arm ppc
   case Iop_CmpGT64Sx2:
   case Iop_CmpLE16Fx8:                  // only used by arm64
   case Iop_CmpLE32F0x4:
   case Iop_CmpLE32Fx4:
   case Iop_CmpLE64F0x2:
   case Iop_CmpLE64Fx2:
   case Iop_CmpLT16Fx8:                  // only used by arm64
   case Iop_CmpLT32F0x4:
   case Iop_CmpLT32Fx4:
   case Iop_CmpLT64F0x2:
   case Iop_CmpLT64Fx2:
   case Iop_CmpUN32F0x4:
   case Iop_CmpUN32Fx4:
   case Iop_CmpUN64F0x2:
   case Iop_CmpUN64Fx2:

      /* ------------------ 128-bit SIMD Integer. ------------------ */
      /* MISC (vector integer cmp != 0) */
      /* COMPARISON */
   case Iop_CmpEQ8x16:
   case Iop_CmpEQ16x8:
   case Iop_CmpEQ32x4:
   case Iop_CmpGT8Sx16:
   case Iop_CmpGT16Sx8:
   case Iop_CmpGT32Sx4:
   case Iop_CmpGT8Ux16:                  // only used by arm mips ppc s390 arm64
   case Iop_CmpGT16Ux8:                  // only used by arm mips ppc s390 arm64
   case Iop_CmpGT32Ux4:                  // only used by arm mips ppc s390 arm64

      /* ------------------ 256-bit SIMD Integer. ------------------ */
      /* COMPARISON */
   case Iop_CmpEQ8x32:
   case Iop_CmpEQ16x16:
   case Iop_CmpEQ32x8:
   case Iop_CmpEQ64x4:
   case Iop_CmpGT8Sx32:
   case Iop_CmpGT16Sx16:
   case Iop_CmpGT32Sx8:
   case Iop_CmpGT64Sx4:

      helper = &MC_(helperc_MERGE_TAGS_RETURN_0);
      hname = "MC_(helperc_MERGE_TAGS_RETURN_0)";
      break;

      /* ------------------ 128-bit SIMD Integer. ------------------ */

      // -----------------------------------
      // Return the tag of the 1st argument:
      // -----------------------------------

      // Shifts are special.  In z = x << y,
      // we want the comparability sets to be {x, z} {y}
      // because z is formed from x, but the shift amount
      // y is really a different abstract type than x and z.
      // Thus, I think the correct behavior is to simply
      // return vatom1 (which is the tag of x, in this case)
      // without merging the tags of vatom1 and vatom2

      // Integer shifts:
   case Iop_Shl8:
   case Iop_Shl16:
   case Iop_Shl32:
   case Iop_Shl64:
   case Iop_Shr8:
   case Iop_Shr16:
   case Iop_Shr32:
   case Iop_Shr64:
   case Iop_Sar8:
   case Iop_Sar16:
   case Iop_Sar32:
   case Iop_Sar64:

      // 64-bit SIMD integer shifts:
      /* VECTOR x SCALAR SHIFT (shift amt :: Ity_I8) */
   case Iop_Sal8x8:                      // only used by arm
   case Iop_Sal16x4:                     // only used by arm
   case Iop_Sal32x2:                     // only used by arm
   case Iop_Sal64x1:                     // only used by arm
   case Iop_Sar8x8:                      // only used by arm
   case Iop_Sar16x4:                     // only used by arm
   case Iop_Sar32x2:                     // only used by arm
   case Iop_Shl8x8:                      // only used by arm
   case Iop_Shl16x4:                     // only used by arm
   case Iop_Shl32x2:                     // only used by arm
   case Iop_Shr8x8:                      // only used by arm
   case Iop_Shr16x4:                     // only used by arm
   case Iop_Shr32x2:                     // only used by arm
   case Iop_SarN8x8:                     // only used by arm
   case Iop_SarN16x4:
   case Iop_SarN32x2:
   case Iop_ShlN8x8:
   case Iop_ShlN16x4:
   case Iop_ShlN32x2:
   case Iop_ShrN8x8:                     // only used by arm
   case Iop_ShrN16x4:
   case Iop_ShrN32x2:

   case Iop_Perm8x8:                     // only used by arm
   case Iop_PermOrZero8x8:

      /* ------------------ 256-bit SIMD Integer. ------------------ */
   case Iop_SarN16x16:
   case Iop_SarN32x8:
   case Iop_ShlN16x16:
   case Iop_ShlN32x8:
   case Iop_ShlN64x4:
   case Iop_ShrN16x16:
   case Iop_ShrN32x8:
   case Iop_ShrN64x4:

      /* ------------------ 128-bit SIMD Integer. ------------------ */
      /* VECTOR x SCALAR SHIFT (shift amt :: Ity_I8) */
   case Iop_Rol8x16:                     // only used by ppc s390
   case Iop_Rol16x8:                     // only used by ppc s390
   case Iop_Rol32x4:                     // only used by ppc s390
   case Iop_Sal8x16:                     // only used by arm
   case Iop_Sal16x8:                     // only used by arm
   case Iop_Sal32x4:                     // only used by arm
   case Iop_Sal64x2:                     // only used by arm
   case Iop_Sar8x16:                     // only used by arm mips ppc s390
   case Iop_Sar16x8:                     // only used by arm mips ppc s390
   case Iop_Sar32x4:                     // only used by arm mips ppc s390
   case Iop_Sar64x2:                     // only used by arm mips ppc s390
   case Iop_Shl8x16:                     // only used by arm mips ppc s390 arm64
   case Iop_Shl16x8:                     // only used by arm mips ppc s390 arm64
   case Iop_Shl32x4:                     // only used by arm mips ppc s390 arm64
   case Iop_Shl64x2:                     // only used by arm mips ppc s390 arm64
   case Iop_Shr8x16:                     // only used by arm ppc
   case Iop_Shr16x8:                     // only used by arm ppc
   case Iop_Shr32x4:                     // only used by arm ppc
   case Iop_Shr64x2:                     // only used by arm ppc
   case Iop_SarN8x16:
   case Iop_SarN16x8:
   case Iop_SarN32x4:
   case Iop_SarN64x2:
   case Iop_ShlN8x16:                    // only used by arm ppc arm64
   case Iop_ShlN16x8:
   case Iop_ShlN32x4:
   case Iop_ShlN64x2:
   case Iop_ShrN8x16:                    // only used by arm arm64
   case Iop_ShrN16x8:
   case Iop_ShrN32x4:
   case Iop_ShrN64x2:

   case Iop_ShrD64:                      // only used by ppc s390
   case Iop_ShlD64:                      // only used by ppc s390
   case Iop_ShrD128:                     // only used by ppc s390
   case Iop_ShlD128:                     // only used by ppc s390
   case Iop_ShrV128:                     // only used by mips ppc s390 arm64
   case Iop_ShlV128:                     // only used by mips ppc s390 arm64
   case Iop_I128StoBCD128:               // only used by ppc
   case Iop_BCDAdd:                      // only used by ppc
   case Iop_BCDSub:                      // only used by ppc

   case Iop_QSal8x16:                    // only used by arm
   case Iop_QSal16x8:                    // only used by arm
   case Iop_QSal32x4:                    // only used by arm
   case Iop_QSal64x2:                    // only used by arm
   case Iop_QShl8x16:                    // only used by arm
   case Iop_QShl16x8:                    // only used by arm
   case Iop_QShl32x4:                    // only used by arm
   case Iop_QShl64x2:                    // only used by arm

      // From the looks of the spec., we want to return the tag
      // of the first argument
   case Iop_SetV128lo32:  // :: (V128,I32) -> V128
   case Iop_SetV128lo64:

   case Iop_Perm32x4:
   case Iop_Perm32x8:

      if (!dyncomp_dataflow_comparisons_mode) {
         return vatom1;
      }
      break;


      // -----------------------------------
      // Return the tag of the 2nd argument:
      // -----------------------------------

      // Floating-point to integer conversions are special.  For
      // these, we need to pass along the tag of the data argument
      // (the second one) and ignore the tag of the rounding mode
      // argument (the first one).  This doesn't qualify as an
      // interaction, but we need to still pass along some tag or else
      // we will just end up with a 0 tag, which is bad.

      /* --- Int to/from FP conversions. --- */
      /* For the most part, these take a first argument :: Ity_I32
         (as IRRoundingMode) which is an indication of the rounding
         mode to use, as per the following encoding:
            00b  to nearest (the default)
            01b  to -infinity
            10b  to +infinity
            11b  to zero
         This just happens to be the Intel encoding.  For reference only,
         the PPC encoding is:
            00b  to nearest (the default)
            01b  to zero
            10b  to +infinity
            11b  to -infinity
         Any PPC -> IR front end will have to translate these PPC
         encodings to the standard encodings.

         If one of these conversions gets an out-of-range condition,
         or a NaN, as an argument, the result is host-defined.  On x86
         the "integer indefinite" value 0x80..00 is produced.
         On PPC it is either 0x80..00 or 0x7F..FF depending on the sign
         of the argument.

         Rounding is required whenever the destination type cannot
         represent exactly all values of the source type.
      */
   case Iop_F128toI128S: /* IRRoundingMode(I32) x F128 -> I128 */   // only used by ppc
   case Iop_F128toI32S:  /* IRRoundingMode(I32) x F128 -> I32  */   // only used by s390
   case Iop_F128toI32U:  /* IRRoundingMode(I32) x F128 -> I32  */   // only used by s390
   case Iop_F128toI64S:  /* IRRoundingMode(I32) x F128 -> I64  */   // only used by s390
   case Iop_F128toI64U:  /* IRRoundingMode(I32) x F128 -> I64  */   // only used by s390
   case Iop_F32toD128:   /* IRRoundingMode(I32) x F32 -> D128  */   // only used by s390
   case Iop_F32toD32:    /* IRRoundingMode(I32) x F32 -> D32   */   // only used by s390
   case Iop_F32toD64:    /* IRRoundingMode(I32) x F32 -> D64   */   // only used by s390
   case Iop_F32toF16:    /* IRRoundingMode(I32) x F32 -> F16   */   // only used by arm64
   case Iop_F32toF16x4:  /* IRRoundingMode(I32) x V128 -> I64  */
   case Iop_F32toF16x8:  /* IRRoundingMode(I32) x V256 -> V128 */
   case Iop_F32toI32S:   /* IRRoundingMode(I32) x F32 -> I32   */
   case Iop_F32toI32Sx4: /* IRRoundingMode(I32) x V128 -> V128 */
   case Iop_F32toI32Sx8: /* IRRoundingMode(I32) x V256 -> V256 */
   case Iop_F32toI32U:   /* IRRoundingMode(I32) x F32 -> I32   */
   case Iop_F32toI64S:   /* IRRoundingMode(I32) x F32 -> I64   */
   case Iop_F32toI64U:   /* IRRoundingMode(I32) x F32 -> I64   */
   case Iop_F64toD128:   /* IRRoundingMode(I32) x F64 -> D128  */
   case Iop_F64toD32:    /* IRRoundingMode(I32) x F64 -> D32   */
   case Iop_F64toD64:    /* IRRoundingMode(I32) x F64 -> D64   */
   case Iop_F64toF16:    /* IRRoundingMode(I32) x F64 -> F16   */
   case Iop_F64toF32:    /* IRRoundingMode(I32) x F64 -> F32   */
   case Iop_F64toI16S:   /* IRRoundingMode(I32) x F64 -> I16   */
   case Iop_F64toI32S:   /* IRRoundingMode(I32) x F64 -> I32   */
   case Iop_F64toI32U:   /* IRRoundingMode(I32) x F64 -> I32   */
   case Iop_F64toI64S:   /* IRRoundingMode(I32) x F64 -> I64   */
   case Iop_F64toI64U:   /* IRRoundingMode(I32) x F64 -> I64   */
   case Iop_I32StoF32:   /* IRRoundingMode(I32) x I32 -> F32   */
   case Iop_I32StoF32x4: /* IRRoundingMode(I32) x V128 -> V128 */
   case Iop_I32StoF32x8: /* IRRoundingMode(I32) x V256 -> V256 */
   case Iop_I32UtoF32:   /* IRRoundingMode(I32) x I32 -> F32   */
   case Iop_I64StoF32:   /* IRRoundingMode(I32) x I64 -> F32   */
   case Iop_I64StoF64:   /* IRRoundingMode(I32) x I64 -> F64   */
   case Iop_I64UtoF32:   /* IRRoundingMode(I32) x I64 -> F32   */
   case Iop_I64UtoF64:   /* IRRoundingMode(I32) x I64 -> F64   */

   case Iop_SqrtF16:
   case Iop_SqrtF32:     /* IRRoundingMode(I32) x F32 -> F32   */
   case Iop_SqrtF64:     /* IRRoundingMode(I32) x F64 -> F64   */
   case Iop_SqrtF128:    /* IRRoundingMode(I32) x F128 -> F128 */
   case Iop_Sqrt16Fx8:
   case Iop_Sqrt32Fx4:   /* IRRoundingMode(I32) x V128 -> V128 */
   case Iop_Sqrt64Fx2:   /* IRRoundingMode(I32) x V128 -> V128 */
   case Iop_SinF64:      /* IRRoundingMode(I32) x F64 -> F64   */
   case Iop_CosF64:      /* IRRoundingMode(I32) x F64 -> F64   */
   case Iop_TanF64:      /* IRRoundingMode(I32) x F64 -> F64   */
   case Iop_2xm1F64:     /* IRRoundingMode(I32) x F64 -> F64   */

   case Iop_RoundD64toInt:  /* IRRoundingMode(I32) x D64 -> D64   */
   case Iop_RoundD128toInt: /* IRRoundingMode(I32) x D128 -> D128 */
   case Iop_RoundF128toInt: /* IRRoundingMode(I32) x F128 -> F128 */
   case Iop_RoundF32toInt:  /* IRRoundingMode(I32) x F32 -> I32   */
   case Iop_RoundF64toInt:  /* IRRoundingMode(I32) x F64 -> I64   */
   case Iop_RoundF64toF32:  /* IRRoundingMode(I32) x F64 -> F32   */
   case Iop_I128UtoF128:      /* I128 -> F128 */
   case Iop_I128StoF128:      /* I128 -> F128 */
   case Iop_I128StoD128:

      if (!dyncomp_dataflow_comparisons_mode) {
         return vatom2;
      }
      break;

// Unimplemented
   case Iop_CipherLV128:                 // only used by ppc
   case Iop_CipherV128:                  // only used by ppc
   case Iop_CmpGT64Ux2:                  // only used by ppc
   case Iop_D128toD64:                   // only used by ppc s390
   case Iop_D128toF128:                  // only used by s390
   case Iop_D128toF32:                   // only used by s390
   case Iop_D128toF64:                   // only used by s390
   case Iop_D128toI32S:                  // only used by s390
   case Iop_D128toI32U:                  // only used by s390
   case Iop_D128toI64S:                  // only used by ppc s390
   case Iop_D128toI64U:                  // only used by s390
   case Iop_D128toI128S:                 // only used by ppc
   case Iop_D32toF128:                   // only used by s390
   case Iop_D32toF32:                    // only used by s390
   case Iop_D32toF64:                    // only used by s390
   case Iop_D64HLtoD128:                 // only used by ppc s390
   case Iop_D64toD32:                    // only used by ppc s390
   case Iop_D64toF128:                   // only used by s390
   case Iop_D64toF32:                    // only used by s390
   case Iop_D64toF64:                    // only used by s390
   case Iop_D64toI32S:                   // only used by s390
   case Iop_D64toI32U:                   // only used by s390
   case Iop_D64toI64S:                   // only used by ppc s390
   case Iop_D64toI64U:                   // only used by s390
   case Iop_F128toD128:                  // only used by s390
   case Iop_F128toD32:                   // only used by s390
   case Iop_F128toD64:                   // only used by s390
   case Iop_F128toF32:                   // only used by s390
   case Iop_F128toF64:                   // only used by s390
   case Iop_RndF128:                     // only used by ppc
   case Iop_F32ToFixed32Sx2_RZ:          // only used by arm
   case Iop_F32ToFixed32Sx4_RZ:          // only used by arm
   case Iop_F32ToFixed32Ux2_RZ:          // only used by arm
   case Iop_F32ToFixed32Ux4_RZ:          // only used by arm
   case Iop_F64HLtoF128:                 // only used by s390
   case Iop_Fixed32SToF32x2_RN:          // only used by arm
   case Iop_Fixed32SToF32x4_RN:          // only used by arm
   case Iop_Fixed32UToF32x2_RN:          // only used by arm
   case Iop_Fixed32UToF32x4_RN:          // only used by arm
   case Iop_GetElem16x4:                 // only used by arm
   case Iop_GetElem16x8:                 // only used by arm
   case Iop_GetElem32x2:                 // only used by arm
   case Iop_GetElem32x4:                 // only used by arm
   case Iop_GetElem64x2:                 // unused
   case Iop_GetElem8x16:                 // only used by arm
   case Iop_GetElem8x8:                  // only used by arm
   case Iop_I64StoD64:                   // only used by ppc s390
   case Iop_I64UtoD64:                   // only used by s390
   case Iop_InsertExpD128:               // only used by ppc s390
   case Iop_InsertExpD64:                // only used by ppc s390
   case Iop_Max32U:                      // only used by memcheck
   case Iop_Max64Sx2:                    // only used by ppc
   case Iop_Max64Ux2:                    // only used by ppc
   case Iop_Min64Sx2:                    // only used by ppc
   case Iop_Min64Ux2:                    // only used by ppc
   case Iop_MulHi32Sx4:                  // unused
   case Iop_MulHi32Ux4:                  // unused
   case Iop_MullEven32Sx4:               // only used by ppc
   case Iop_MullEven32Ux4:               // only used by ppc
   case Iop_NarrowBin64to32x4:           // only used by ppc
   case Iop_NCipherLV128:                // only used by ppc
   case Iop_NCipherV128:                 // only used by ppc
   case Iop_MulI128by10E:                // only used by ppc
   case Iop_MulI128by10ECarry:           // only used by ppc
   case Iop_PackEvenLanes16x8:           // only used by mips
   case Iop_PackEvenLanes32x4:           // only used by mips
   case Iop_PackEvenLanes8x16:           // only used by mips
   case Iop_PackOddLanes16x8:            // only used by mips
   case Iop_PackOddLanes32x4:            // only used by mips
   case Iop_PackOddLanes8x16:            // only used by mips
   case Iop_Perm8x16:                    // only used by ppc arm64
   case Iop_PermOrZero8x16:
   case Iop_PolynomialMulAdd16x8:        // only used by ppc
   case Iop_PolynomialMulAdd32x4:        // only used by ppc
   case Iop_PolynomialMulAdd64x2:        // only used by ppc
   case Iop_PolynomialMulAdd8x16:        // only used by ppc
   case Iop_PwExtUSMulQAdd8x16:
   case Iop_PwAdd16x4:                   // only used by arm
   case Iop_PwAdd16x8:                   // only used by arm
   case Iop_PwAdd32Fx2:                  // only used by arm
   case Iop_PwAdd32x2:                   // only used by arm
   case Iop_PwAdd32x4:                   // only used by arm
   case Iop_PwAdd8x16:                   // only used by arm
   case Iop_PwAdd8x8:                    // only used by arm
   case Iop_PwMax16Sx4:                  // only used by arm
   case Iop_PwMax16Ux4:                  // only used by arm
   case Iop_PwMax32Fx2:                  // only used by arm
   case Iop_PwMax32Fx4:                  // unused
   case Iop_PwMax32Sx2:                  // only used by arm
   case Iop_PwMax32Ux2:                  // only used by arm
   case Iop_PwMax8Sx8:                   // only used by arm
   case Iop_PwMax8Ux8:                   // only used by arm
   case Iop_PwMin16Sx4:                  // only used by arm
   case Iop_PwMin16Ux4:                  // only used by arm
   case Iop_PwMin32Fx2:                  // only used by arm
   case Iop_PwMin32Fx4:                  // unused
   case Iop_PwMin32Sx2:                  // only used by arm
   case Iop_PwMin32Ux2:                  // only used by arm
   case Iop_PwMin8Sx8:                   // only used by arm
   case Iop_PwMin8Ux8:                   // only used by arm
   case Iop_QAdd32S:                     // only used by arm
   case Iop_QNarrowBin64Sto32Sx4:        // only used by ppc s390
   case Iop_QNarrowBin64Uto32Ux4:        // only used by ppc s390
   case Iop_QSal16x4:                    // only used by arm
   case Iop_QSal32x2:                    // only used by arm
   case Iop_QSal64x1:                    // only used by arm
   case Iop_QSal8x8:                     // only used by arm
   case Iop_QShl16x4:                    // only used by arm
   case Iop_QShl32x2:                    // only used by arm
   case Iop_QShl64x1:                    // only used by arm
   case Iop_QShl8x8:                     // only used by arm
   case Iop_QSub32S:                     // only used by arm
   case Iop_Rol64x2:                     // only used by ppc s390
   case Iop_Sad8Ux4:                     // only used by arm
   case Iop_SarV128:                     // only used by s390
   case Iop_SHA256:                      // only used by ppc
   case Iop_SHA512:                      // only used by ppc
   case Iop_RecipStep32Fx2:              // only used by arm arm64
   case Iop_RecipStep32Fx4:              // only used by arm arm64
   case Iop_RecipStep64Fx2:              // only used by arm64
   case Iop_RSqrtStep32Fx2:              // only used by arm arm64
   case Iop_RSqrtStep32Fx4:              // only used by arm arm64
   case Iop_RSqrtStep64Fx2:              // only used by arm64

      // Hopefully we will never get here if we've had had cases which
      // handle every possible IR binary op. type (right?)
   default:
      ppIROp(op);
      VG_(tool_panic)("dyncomp:expr2tags_Binop_DC");
   }

   // In this mode, NOTHING is an interaction:
   if (dyncomp_dataflow_only_mode) {
      helper = 0;
      hname = 0;
   }

   if (helper) {
      // Heuristic:

      // At least as observed in one trial, the dirty call
      // version had MANY more calls of MC_(helperc_MERGE_TAGS)
      // than the clean version, many of which were nonsensical
      // merges of tag 0 with a valid tag but nonetheless with
      // some valid merges as well.
      // However, in 'z = x + y' of SuperSimpleTest,
      // that interaction was correctly captured by the clean call.

      // The standard way to make a dirty helper call (I think):
      // Tags are always word-sized
      //      datatag = newIRTemp(dce->bb->tyenv, Ity_Word);
      //      di = unsafeIRDirty_1_N(datatag,
      //                             2,
      //                             hname,
      //                             helper,
      //                             mkIRExprVec_2( vatom1, vatom2 ));

      //      setHelperAnns_DC( dce, di );
      //      stmt( dce->bb, IRStmt_Dirty(di) );
      //      return mkexpr(datatag);

      // If either argument is a constant and helper is equal to
      // &MC_(helperc_MERGE_TAGS), then return the tag of the other
      // argument.  For &MC_(helperc_MERGE_TAGS_RETURN_0), simply
      // return 0:

      // (comment added 2006)
      // TODO: This doesn't happen THAT often, so there must be a
      // better way to tell whether we can make this optimization
      // without simply checking whether the atoms are consts

      if (atom1->tag == Iex_Const) {
         if (helper == &MC_(helperc_MERGE_TAGS)) {
            return vatom2;
         }
         else if (helper == &MC_(helperc_MERGE_TAGS_RETURN_0)) {
            return IRExpr_Const(IRConst_UWord(0));
         }
      }
      else if (atom2->tag == Iex_Const) {
         if (helper == &MC_(helperc_MERGE_TAGS)) {
            return vatom1;
         }
         else if (helper == &MC_(helperc_MERGE_TAGS_RETURN_0)) {
            return IRExpr_Const(IRConst_UWord(0));
         }
      }

      // Let's try a clean call.  It seems to be correct
      // because of the fact that merging the same 2 things more than
      // once (in close proximity) doesn't hurt
      // DO NOT use clean call unless it has NO side effects and
      // is (nearly) purely functional like an IRExpr
      // (from the point-of-view of IR, at least)
      return mkIRExprCCall (Ity_Word,
                            2 /*Int regparms*/,
                            hname,
                            helper,
                            mkIRExprVec_2( vatom1, vatom2 ));

   }
   // Hmmm, is this the desired behavior for a non-interaction?
   // I think so ...
   // vatom1 and vatom2 contain the tags for the two operands.
   // If they don't really interact, we want to return simply 0
   // (no tag) so that when this gets propagated up the chain,
   // it doesn't try to merge either operand tag with anything else.
   //
   // e.g. Assume @ is a binary operator which is NOT interaction:
   //     (a @ b) + c
   // 'c' didn't really interact with either 'a' or 'b'.
   // Is this correct?
   else {
      return IRExpr_Const(IRConst_UWord(0));
   }
}

static
IRExpr* expr2tags_Unop_DC ( DCEnv* dce, IRAtom* atom )
{
   IRAtom* vatom = expr2tags_DC( dce, atom );
   tl_assert(isOriginalAtom_DC(dce,atom));

   // Do nothing with unary ops.  Just evaluate the
   // sub-expression and return it:
   // pgbovine: Actually, when you widen stuff, don't you want to
   //       create new tags for the new bytes and merge them?
   //       But you can't do that because you only have the word-sized
   //       tag and NOT the memory locations it came from
   //       ... I guess we don't care since during binary ops.,
   //       we only consider the tag of the first bytes of each
   //       operand anyways.
   //
   // For documentation purposes, here is a list of all the unary ops.
   // Iop_128HIto64
   // Iop_128to64
   // Iop_16HIto8
   // Iop_16Sto32
   // Iop_16Sto64
   // Iop_16to8
   // Iop_16Uto32
   // Iop_16Uto64
   // Iop_1Sto8:                       // only used by ppc
   // Iop_1Sto16:                      // unused
   // Iop_1Sto32:                      // only used by mips ppc
   // Iop_1Sto64:                      // only used by mips ppc
   // Iop_1Uto32
   // Iop_1Uto64
   // Iop_1Uto8
   // Iop_32HIto16
   // Iop_32Sto64
   // Iop_32to1
   // Iop_32to16
   // Iop_32to8
   // Iop_32Uto64
   // Iop_32UtoV128
   // Iop_64HIto32
   // Iop_64to1
   // Iop_64to16
   // Iop_64to32
   // Iop_64to8
   // Iop_64UtoV128
   // Iop_1Sto16
   // Iop_8Sto16
   // Iop_8Sto32
   // Iop_8Sto64
   // Iop_8Uto16
   // Iop_8Uto32
   // Iop_8Uto64
   // Iop_Abs16Fx8:
   // Iop_Neg16Fx8:
   // Iop_Abs16x4:                     // only used by arm
   // Iop_Abs16x8:                     // only used by arm arm64
   // Iop_Abs32Fx2:                    // only used by arm
   // Iop_Abs32Fx4:                    // only used by arm arm64
   // Iop_Abs32x2:                     // only used by arm
   // Iop_Abs32x4:                     // only used by arm arm64
   // Iop_Abs64Fx2:                    // only used by arm64
   // Iop_Abs64x2:                     // only used by arm64
   // Iop_Abs8x16:                     // only used by arm arm64
   // Iop_Abs8x8:                      // only used by arm
   // Iop_AbsF128:                     // only used by s390
   // Iop_AbsF32:                      // only used by arm mips ppc s390 arm64
   // Iop_AbsF64:
   // Iop_AbsF16:
   // Iop_BCDtoDPB:                    // only used by ppc
   // Iop_BCD128toI128S:               // only used by ppc
   // Iop_CipherSV128:                 // only used by ppc
   // Iop_Cls16x4:                     // only used by arm
   // Iop_Cls16x8:                     // only used by arm arm64
   // Iop_Cls32x2:                     // only used by arm
   // Iop_Cls32x4:                     // only used by arm arm64
   // Iop_Cls8x16:                     // only used by arm arm64
   // Iop_Cls8x8:                      // only used by arm
   // Iop_Clz32
   // Iop_Clz64
   // Iop_ClzNat32                     // only used by ppc
   // Iop_ClzNat64                     // only used by ppc
   // Iop_Clz16x4:                     // only used by arm
   // Iop_Clz16x8:                     // only used by arm ppc arm64 mips s390
   // Iop_Clz32x2:                     // only used by arm
   // Iop_Clz32x4:                     // only used by arm ppc arm64 mips s390
   // Iop_Clz64x2:                     // only used by ppc mips s390
   // Iop_Clz8x16:                     // only used by arm ppc arm64 mips s390
   // Iop_Clz8x8:                      // only used by arm
   // Iop_CmpNEZ128x1:                 // unused
   // Iop_CmpNEZ16:                    // unused
   // Iop_CmpNEZ16x16:                 // unused
   // Iop_CmpNEZ16x2:                  // unused
   // Iop_CmpNEZ16x4:                  // only used by arm
   // Iop_CmpNEZ16x8:                  // only used by arm
   // Iop_CmpNEZ32:                    // unused
   // Iop_CmpNEZ32x2:                  // only used by arm
   // Iop_CmpNEZ32x4:                  // only used by arm
   // Iop_CmpNEZ32x8:                  // unused
   // Iop_CmpNEZ64:                    // unused
   // Iop_CmpNEZ64x2:                  // only used by arm
   // Iop_CmpNEZ64x4:                  // unused
   // Iop_CmpNEZ8:                     // unused
   // Iop_CmpNEZ8x16:                  // only used by arm
   // Iop_CmpNEZ8x32:                  // unused
   // Iop_CmpNEZ8x4:                   // unused
   // Iop_CmpNEZ8x8:                   // only used by arm
   // Iop_CmpwNEZ32:                   // unused
   // Iop_CmpwNEZ64:                   // only used by arm
   // Iop_Cnt8x16:                     // only used by arm arm64
   // Iop_Cnt8x8:                      // only used by arm
   // Iop_Ctz16x8:
   // Iop_Ctz8x16:
   // Iop_Ctz32:
   // Iop_CtzNat32:
   // Iop_Ctz32x4:
   // Iop_Ctz64:
   // Iop_CtzNat64:
   // Iop_Ctz64x2:
   // Iop_D128HItoD64:                 // only used by ppc s390
   // Iop_D128LOtoD64:                 // only used by ppc s390
   // Iop_D32toD64:                    // only used by ppc s390
   // Iop_D64toD128:                   // only used by ppc s390
   // Iop_DPBtoBCD:                    // only used by ppc
   // Iop_Dup16x4:                     // only used by arm
   // Iop_Dup16x8:                     // only used by arm ppc
   // Iop_Dup32x2:                     // only used by arm
   // Iop_Dup32x4:                     // only used by arm ppc
   // Iop_Dup8x16:                     // only used by arm ppc
   // Iop_Dup8x8:                      // only used by arm
   // Iop_ExtractExpD128:              // only used by ppc s390
   // Iop_ExtractExpD64:               // only used by ppc s390
   // Iop_ExtractSigD128:              // only used by s390
   // Iop_ExtractSigD64:               // only used by s390
   // Iop_F128HItoF64:                 // only used by s390
   // Iop_F128LOtoF64:                 // only used by s390
   // Iop_F16toF32:                    // only used by arm64
   // Iop_F16toF32x4:
   // Iop_F16toF32x8:
   // Iop_F16toF64:                    // only used by arm64
   // Iop_F16toF64x2:                  // only used by ppc
   // Iop_F32toF16x4_DEP:              // only used by arm mips ppc
   // Iop_F32toF64:
   // Iop_F32toF128:                   // only used by s390
   // Iop_F32toI32Sx2_RZ:              // only used by arm mips
   // Iop_F32toI32Sx4_RZ:              // only used by arm mips
   // Iop_F32toI32Ux2_RZ:              // only used by arm mips
   // Iop_F32toI32Ux4_RZ:              // only used by arm mips
   // Iop_F64toF128:                   // only used by s390
   // Iop_GetMSBs8x16
   // Iop_GetMSBs8x8
   // Iop_I32StoD128:                  // only used by s390
   // Iop_I32StoD64:                   // only used by s390
   // Iop_I32StoF128:                  // only used by s390
   // Iop_I32StoF64
   // Iop_I32StoF32x4_DEP:
   // Iop_I32StoF32x2_DEP:
   // Iop_I32UtoD128:                  // only used by s390
   // Iop_I32UtoD64:                   // only used by s390
   // Iop_I32UtoF128:                  // only used by s390
   // Iop_I32UtoF64:                   // only used by arm s390 arm64
   // Iop_I32UtoF32x4_DEP:
   // Iop_I32UtoF32x2_DEP:
   // Iop_I64StoD128:                  // only used by ppc s390
   // Iop_I64StoF128:                  // only used by s390
   // Iop_I64UtoD128:                  // only used by s390
   // Iop_I64UtoF128:                  // only used by s390
   // Iop_Left16:                      // unused
   // Iop_Left32:                      // unused
   // Iop_Left64:                      // unused
   // Iop_Left8:                       // unused
   // Iop_Log2_32Fx4:                  // used only by mips
   // Iop_Exp2_32Fx4:                  // ??????
   // Iop_Log2_64Fx2:                  // used only by mips
   // Iop_MulHi8Sx16:                  // used only by s390
   // Iop_MulHi8Ux16:                  // used only by s390
   // Iop_MulI128by10:
   // Iop_MulI128by10Carry:
   // Iop_NarrowUn16to8x8:             // only used by arm arm64
   // Iop_NarrowUn32to16x4:            // only used by arm arm64
   // Iop_NarrowUn64to32x2:            // only used by arm arm64
   // Iop_Neg32Fx2:                    // only used by arm
   // Iop_Neg32Fx4:                    // only used by arm arm64
   // Iop_Neg64Fx2:                    // only used by arm64
   // Iop_NegF128:                     // only used by s390
   // Iop_NegF16:
   // Iop_NegF32:
   // Iop_NegF64:
   // Iop_Not1:                        // only used by arm mips ppc s390
   // Iop_Not8:
   // Iop_Not16:                       // only used by mips
   // Iop_Not32:
   // Iop_Not64:
   // Iop_NotV128:
   // Iop_NotV256:
   // Iop_PopCount32:                  // only used by ppc
   // Iop_PopCount64:                  // only used by ppc
   // Iop_PwAddL16Sx4:                 // only used by arm
   // Iop_PwAddL16Sx8:                 // only used by arm
   // Iop_PwAddL16Ux4:                 // only used by arm
   // Iop_PwAddL16Ux8:                 // only used by arm s390
   // Iop_PwAddL32Sx2:                 // only used by arm
   // Iop_PwAddL32Sx4:                 // only used by arm
   // Iop_PwAddL32Ux2:                 // only used by arm s390
   // Iop_PwAddL32Ux4:                 // only used by arm s390
   // Iop_PwAddL64Ux2:                 // only used by s390
   // Iop_PwAddL8Sx16:                 // only used by arm
   // Iop_PwAddL8Sx8:                  // only used by arm
   // Iop_PwAddL8Ux8:                  // only used by arm
   // Iop_PwAddL8Ux16:                 // only used by arm s390
   // Iop_PwBitMtxXpose64x2:           // only used by ppc
   // Iop_QF32toI32Sx4_RZ:             // only used by ppc
   // Iop_QF32toI32Ux4_RZ:             // only used by ppc
   // Iop_QNarrowUn16Sto8Sx8:          // only used by arm arm64
   // Iop_QNarrowUn16Sto8Ux8:          // only used by arm arm64
   // Iop_QNarrowUn16Uto8Ux8:          // only used by arm arm64
   // Iop_QNarrowUn32Sto16Sx4:         // only used by arm arm64
   // Iop_QNarrowUn32Sto16Ux4:         // only used by arm arm64
   // Iop_QNarrowUn32Uto16Ux4:         // only used by arm arm64
   // Iop_QNarrowUn64Sto32Sx2:         // only used by arm arm64
   // Iop_QNarrowUn64Sto32Ux2:         // only used by arm arm64
   // Iop_QNarrowUn64Uto32Ux2:         // only used by arm arm64
   // Iop_RecipEst32F0x4:              //
   // Iop_RecipEst32Fx2:               // only used by arm
   // Iop_RecipEst32Fx4:               //
   // Iop_RecipEst32Fx8:               //
   // Iop_RecipEst32Ux2:               // only used by arm
   // Iop_RecipEst32Ux4:               // only used by arm arm64
   // Iop_ReinterpF64asI64
   // Iop_ReinterpI32asF32
   // Iop_ReinterpI64asF64
   // Iop_ReinterpD64asI64:            // only used by ppc s390
   // Iop_ReinterpF32asI32:            // only used by arm mips ppc arm64
   // Iop_ReinterpI64asD64:            // only used by ppc
   // Iop_Reverse16sIn32_x2:           // only used by arm
   // Iop_Reverse16sIn32_x4:           // only used by arm arm64
   // Iop_Reverse16sIn64_x1:           // only used by arm
   // Iop_Reverse16sIn64_x2:           // only used by arm arm64
   // Iop_Reverse1sIn8_x16:            // only used by arm64
   // Iop_Reverse32sIn64_x1:           // only used by arm
   // Iop_Reverse32sIn64_x2:           // only used by arm arm64
   // Iop_Reverse8sIn16_x4:            // only used by arm
   // Iop_Reverse8sIn16_x8:            // only used by arm arm64 mips
   // Iop_Reverse8sIn32_x1:            // only used by ppc
   // Iop_Reverse8sIn32_x2:            // only used by arm
   // Iop_Reverse8sIn32_x4:            // only used by arm arm64 mips
   // Iop_Reverse8sIn64_x1:            // only used by arm ppc
   // Iop_Reverse8sIn64_x2:            // only used by arm arm64 mips
   // Iop_RoundF32x4_RM:               // only used by ppc
   // Iop_RoundF32x4_RN:               // only used by ppc
   // Iop_RoundF32x4_RP:               // only used by ppc
   // Iop_RoundF32x4_RZ:               // only used by ppc
   // Iop_RoundF64toF64_NEAREST:       // unused
   // Iop_RoundF64toF64_NegINF:        // unused
   // Iop_RoundF64toF64_PosINF:        // unused
   // Iop_RoundF64toF64_ZERO:          // unused
   // Iop_RSqrtEst32F0x4:              //
   // Iop_RSqrtEst32Fx2:               // only used by arm
   // Iop_RSqrtEst32Fx4:               //
   // Iop_RSqrtEst32Fx8:               //
   // Iop_RSqrtEst32Ux2:               // only used by arm
   // Iop_RSqrtEst32Ux4:               // only used by arm arm64
   // Iop_RSqrtEst5GoodF64:            // only used by ppc
   // Iop_RSqrtEst64Fx2:               // only used by arm64
   // Iop_Sqrt32F0x4
   // Iop_Sqrt32Fx8
   // Iop_Sqrt64F0x2
   // Iop_Sqrt64Fx4
   // Iop_TruncF64asF32:               // only used by ppc
   // Iop_TruncF128toI64S:
   // Iop_TruncF128toI32S:
   // Iop_TruncF128toI64U:
   // Iop_TruncF128toI32U:
   // Iop_TruncF128toI128S:
   // Iop_TruncF128toI128U:
   // Iop_ReinterpV128asI128:
   // Iop_ReinterpI128asF128:
   // Iop_ReinterpF128asI128:
   // Iop_V128HIto64
   // Iop_V128to32
   // Iop_V128to64
   // Iop_V256to64_0
   // Iop_V256to64_1
   // Iop_V256to64_2
   // Iop_V256to64_3
   // Iop_V256toV128_0
   // Iop_V256toV128_1
   // Iop_Widen16Sto32x4:              // only used by arm
   // Iop_Widen16Uto32x4:              // only used by arm
   // Iop_Widen32Sto64x2:              // only used by arm
   // Iop_Widen32Uto64x2:              // only used by arm
   // Iop_Widen8Sto16x8:               // only used by arm
   // Iop_Widen8Uto16x8:               // only used by arm

   return vatom;
}

/*
 * The following opcodes are not implemented as they are not used
 * by our supported guests: amd64 and x86.
 *
   case Iop_QAddExtSUsatUU16x8:          // only used by arm64
   case Iop_QAddExtSUsatUU32x4:          // only used by arm64
   case Iop_QAddExtSUsatUU64x2:          // only used by arm64
   case Iop_QAddExtSUsatUU8x16:          // only used by arm64
   case Iop_QAddExtUSsatSS16x8:          // only used by arm64
   case Iop_QAddExtUSsatSS32x4:          // only used by arm64
   case Iop_QAddExtUSsatSS64x2:          // only used by arm64
   case Iop_QAddExtUSsatSS8x16:          // only used by arm64
   case Iop_QandQRSarNnarrow16Sto8Sx8:   // only used by arm64
   case Iop_QandQRSarNnarrow16Sto8Ux8:   // only used by arm64
   case Iop_QandQRSarNnarrow32Sto16Sx4:  // only used by arm64
   case Iop_QandQRSarNnarrow32Sto16Ux4:  // only used by arm64
   case Iop_QandQRSarNnarrow64Sto32Sx2:  // only used by arm64
   case Iop_QandQRSarNnarrow64Sto32Ux2:  // only used by arm64
   case Iop_QandQRShrNnarrow16Uto8Ux8:   // only used by arm64
   case Iop_QandQRShrNnarrow32Uto16Ux4:  // only used by arm64
   case Iop_QandQRShrNnarrow64Uto32Ux2:  // only used by arm64
   case Iop_QandQSarNnarrow16Sto8Sx8:    // only used by arm64
   case Iop_QandQSarNnarrow16Sto8Ux8:    // only used by arm64
   case Iop_QandQSarNnarrow32Sto16Sx4:   // only used by arm64
   case Iop_QandQSarNnarrow32Sto16Ux4:   // only used by arm64
   case Iop_QandQSarNnarrow64Sto32Sx2:   // only used by arm64
   case Iop_QandQSarNnarrow64Sto32Ux2:   // only used by arm64
   case Iop_QandQShrNnarrow16Uto8Ux8:    // only used by arm64
   case Iop_QandQShrNnarrow32Uto16Ux4:   // only used by arm64
   case Iop_QandQShrNnarrow64Uto32Ux2:   // only used by arm64
   case Iop_QandSQRsh16x8:               // only used by arm64
   case Iop_QandSQRsh32x4:               // only used by arm64
   case Iop_QandSQRsh64x2:               // only used by arm64
   case Iop_QandSQRsh8x16:               // only used by arm64
   case Iop_QandSQsh16x8:                // only used by arm64
   case Iop_QandSQsh32x4:                // only used by arm64
   case Iop_QandSQsh64x2:                // only used by arm64
   case Iop_QandSQsh8x16:                // only used by arm64
   case Iop_QandUQRsh16x8:               // only used by arm64
   case Iop_QandUQRsh32x4:               // only used by arm64
   case Iop_QandUQRsh64x2:               // only used by arm64
   case Iop_QandUQRsh8x16:               // only used by arm64
   case Iop_QandUQsh16x8:                // only used by arm64
   case Iop_QandUQsh32x4:                // only used by arm64
   case Iop_QandUQsh64x2:                // only used by arm64
   case Iop_QandUQsh8x16:                // only used by arm64

   case Iop_QShlNsatSS16x4:              // only used by arm
   case Iop_QShlNsatSS16x8:              // only used by arm arm64
   case Iop_QShlNsatSS32x2:              // only used by arm
   case Iop_QShlNsatSS32x4:              // only used by arm arm64
   case Iop_QShlNsatSS64x1:              // only used by arm
   case Iop_QShlNsatSS64x2:              // only used by arm arm64
   case Iop_QShlNsatSS8x16:              // only used by arm arm64
   case Iop_QShlNsatSS8x8:               // only used by arm
   case Iop_QShlNsatSU16x4:              // only used by arm
   case Iop_QShlNsatSU16x8:              // only used by arm arm64
   case Iop_QShlNsatSU32x2:              // only used by arm
   case Iop_QShlNsatSU32x4:              // only used by arm arm64
   case Iop_QShlNsatSU64x1:              // only used by arm
   case Iop_QShlNsatSU64x2:              // only used by arm arm64
   case Iop_QShlNsatSU8x16:              // only used by arm arm64
   case Iop_QShlNsatSU8x8:               // only used by arm
   case Iop_QShlNsatUU16x4:              // only used by arm
   case Iop_QShlNsatUU16x8:              // only used by arm arm64
   case Iop_QShlNsatUU32x2:              // only used by arm
   case Iop_QShlNsatUU32x4:              // only used by arm arm64
   case Iop_QShlNsatUU64x1:              // only used by arm
   case Iop_QShlNsatUU64x2:              // only used by arm arm64
   case Iop_QShlNsatUU8x16:              // only used by arm arm64
   case Iop_QShlNsatUU8x8:               // only used by arm

   case Iop_Rsh16Sx8:                    // only used by arm64
   case Iop_Rsh16Ux8:                    // only used by arm64
   case Iop_Rsh32Sx4:                    // only used by arm64
   case Iop_Rsh32Ux4:                    // only used by arm64
   case Iop_Rsh64Sx2:                    // only used by arm64
   case Iop_Rsh64Ux2:                    // only used by arm64
   case Iop_Rsh8Sx16:                    // only used by arm64
   case Iop_Rsh8Ux16:                    // only used by arm64

   case Iop_F64toF16x2_DEP:
   case Iop_RecipEst64Fx2:              // only used by arm64
   case Iop_RecpExpF32:                 // only used by arm64
   case Iop_RecpExpF64:                 // only used by arm64

   case Iop_Sh16Sx8:                     // only used by arm64
   case Iop_Sh16Ux8:                     // only used by arm64
   case Iop_Sh32Sx4:                     // only used by arm64
   case Iop_Sh32Ux4:                     // only used by arm64
   case Iop_Sh64Sx2:                     // only used by arm64
   case Iop_Sh64Ux2:                     // only used by arm64
   case Iop_Sh8Sx16:                     // only used by arm64
   case Iop_Sh8Ux16:                     // only used by arm64

   case Iop_VDup16x4:                    // only used by arm
   case Iop_VDup16x8:                    // only used by arm
   case Iop_VDup32x2:                    // only used by arm
   case Iop_VDup32x4:                    // only used by arm
   case Iop_VDup8x8:                     // only used by arm
   case Iop_VDup8x16:                    // only used by arm

   case Iop_ZeroHI112ofV128:             // only used by arm64
   case Iop_ZeroHI120ofV128:             // only used by arm64
   case Iop_ZeroHI64ofV128:              // only used by arm64
   case Iop_ZeroHI96ofV128:              // only used by arm64
   case Iop_ReinterpI128asV128:
 */

/* Worker function; do not call directly. */
static
IRAtom* expr2tags_LDle_WRK_DC ( DCEnv* dce, IRType ty, IRAtom* addr, UInt bias )
{
   void*    helper;
   const HChar* hname;
   IRDirty* di;
   IRTemp   datatag;
   IRAtom*  addrAct;

   tl_assert(isOriginalAtom_DC(dce,addr));

   /* Now cook up a call to the relevant helper function, to read the
      tag for the given address. */
   ty = shadowTypeV(ty);
   switch (ty) {
      case Ity_I64: helper = &MC_(helperc_LOAD_TAG_8);
                    hname = "MC_(helperc_LOAD_TAG_8)";
                    break;
      case Ity_I32: helper = &MC_(helperc_LOAD_TAG_4);
                    hname = "MC_(helperc_LOAD_TAG_4)";
                    break;
      case Ity_I16: helper = &MC_(helperc_LOAD_TAG_2);
                    hname = "MC_(helperc_LOAD_TAG_2)";
                    break;
      case Ity_I8:  helper = &MC_(helperc_LOAD_TAG_1);
                    hname = "MC_(helperc_LOAD_TAG_1)";
                    break;
      default:      ppIRType(ty);
                    VG_(tool_panic)("dyncomp:do_shadow_LDle_DC");
   }

   /* Generate the actual address into addrAct. */
   if (bias == 0) {
      addrAct = addr;
   } else {
      IROp    mkAdd;
      IRAtom* eBias;
      IRType  tyAddr  = dce->hWordTy;
      tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );
      mkAdd   = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
      eBias   = tyAddr==Ity_I32 ? mkU32(bias) : mkU64(bias);
      addrAct = assignNew_DC(dce, tyAddr, binop(mkAdd, addr, eBias) );
   }

   /* We need to have a place to park the tag we're just about to
      read. */
   //   datatag = newIRTemp(dce->bb->tyenv, tyS);
   datatag = newTemp(dce->mce, Ity_Word, DC); // PG - tags are word-sized
   di = unsafeIRDirty_1_N( datatag,
                           1/*regparms*/, hname, helper,
                           mkIRExprVec_1( addrAct ));
   setHelperAnns_DC( dce, di );
   stmt_DC('V',  dce, IRStmt_Dirty(di) );

   return mkexpr(datatag);
}

static
IRAtom* expr2tags_LDle_DC ( DCEnv* dce, IRType ty, IRAtom* addr, UInt bias )
{
   IRAtom *v64hi, *v64lo;
   //   IRDirty* di;
   //   IRTemp   datatag;
   IRAtom   *vaddr;
   IRTemp   addrTag;
   IRDirty  *diAddr;

   /* Compute the tag for the effective address, and throw the result
      away, but anchor it to a dirty call so that Valgrind doesn't
      optimize the merges away. */
   tl_assert(addr);
   tl_assert(isOriginalAtom_DC(dce, addr));
   vaddr = expr2tags_DC(dce, addr);
   tl_assert(isShadowAtom_DC(dce, vaddr));
   addrTag = newTemp(dce->mce, Ity_Word, DC);
   diAddr = unsafeIRDirty_1_N(addrTag, 1, "MC_(helperc_TAG_NOP)",
			      &MC_(helperc_TAG_NOP), mkIRExprVec_1(vaddr));
   setHelperAnns_DC(dce, diAddr);
   stmt_DC('V', dce, IRStmt_Dirty(diAddr));

   switch (shadowTypeV(ty)) {
      case Ity_I8:
      case Ity_I16:
      case Ity_I32:
      case Ity_I64:
         return expr2tags_LDle_WRK_DC(dce, ty, addr, bias);
      case Ity_V128:
         v64lo = expr2tags_LDle_WRK_DC(dce, Ity_I64, addr, bias);
         v64hi = expr2tags_LDle_WRK_DC(dce, Ity_I64, addr, bias+8);

         // Merge the tags of the results of the
         // lower and upper 64-bit loads:

         // Dirty call version:
         //         datatag = newIRTemp(dce->bb->tyenv, Ity_Word);
         //         di = unsafeIRDirty_1_N(datatag,
         //                                2,
         //                                "MC_(helperc_MERGE_TAGS)",
         //                                &MC_(helperc_MERGE_TAGS),
         //                                mkIRExprVec_2( v64lo, v64hi ));

         //         setHelperAnns_DC( dce, di );
         //         stmt( dce->bb, IRStmt_Dirty(di) );
         //         return mkexpr(datatag);

         // (comment added 2005)
         // pgbovine TODO: Is this merge tags really necessary or too
         // premature?  We should aim to do all of the merging on the
         // language level if somebody really reads this as a 128-bit
         // value instead of forcing all of these bytes to be merged
         // on the memory level

         // On second thought, let's just go ahead and do it for now:

         // Clean call version:
         return mkIRExprCCall (Ity_Word,
                               2 /*Int regparms*/,
                               "MC_(helperc_MERGE_TAGS)",
                               &MC_(helperc_MERGE_TAGS),
                               mkIRExprVec_2( v64lo, v64hi ));


      default:
         VG_(tool_panic)("expr2tags_LDle_DC");
   }
}

static
IRAtom* expr2tags_ITE_DC ( DCEnv* dce,
                           IRAtom* cond, IRAtom* iftrue, IRAtom* iffalse )
{
   IRAtom *vbitsC, *vbits0, *vbits1;
   IRDirty* di;
   IRTemp   datatag;

   tl_assert(isOriginalAtom_DC(dce, cond));
   tl_assert(isOriginalAtom_DC(dce, iftrue));
   tl_assert(isOriginalAtom_DC(dce, iffalse));

   // Generate a temp. 'datatag', which is the result of a NOP dirty
   // call on vbitsC, in order to 'anchor' any possible tag merge
   // clean helper calls in the expression which produced 'cond'.
   // This prevents the IR optimizer from deleting all of these
   // interactions from the parallel tag IR tree (or so we hope)
   vbitsC = expr2tags_DC(dce, cond);
   datatag = newTemp(dce->mce, Ity_Word, DC);
   di = unsafeIRDirty_1_N(datatag,
                          1,
                          "MC_(helperc_TAG_NOP)",
                          &MC_(helperc_TAG_NOP),
                          mkIRExprVec_1( vbitsC ));

   setHelperAnns_DC( dce, di );
   stmt_DC('V', dce, IRStmt_Dirty(di) );

   // Do the real work of generating tag IR trees for expr0 and exprX
   // and then making a parallel Mux which contains these two trees
   // with the ORIGINAL condition 'cond'
   vbits1 = expr2tags_DC(dce, iftrue);
   vbits0 = expr2tags_DC(dce, iffalse);
   // UNDONE: need to figure out why this assert is causing problems.
   // markro 10/5/15
   //tl_assert(sameKindedAtoms(vbits0, vbits1));// Both should be word-sized tags

   return assignNew_DC(dce, Ity_Word, IRExpr_ITE(cond, vbits1, vbits0));
}

// (Very similar to expr2tags_ITE_DC)
// Generate and return temp 'datatag', which is the result of a NOP
// dirty call on the tag of 'guard', in order to 'anchor' any possible
// tag merge clean helper calls in the expression which produced
// 'guard'.  This prevents the IR optimizer from deleting all of these
// interactions from the parallel tag IR tree (or so we hope)
IRAtom* do_shadow_cond_exit_DC (DCEnv* dce, IRExpr* guard)
{
   IRAtom *guardtag;
   IRDirty* di;
   IRTemp   datatag;

   guardtag = expr2tags_DC(dce, guard);
   datatag = newTemp(dce->mce, Ity_Word, DC);
   di = unsafeIRDirty_1_N(datatag,
                          1,
                          "MC_(helperc_TAG_NOP)",
                          &MC_(helperc_TAG_NOP),
                          mkIRExprVec_1( guardtag ));

   setHelperAnns_DC( dce, di );
   stmt_DC('V', dce, IRStmt_Dirty(di) );

   return mkexpr(datatag);
}

/* --------- This is the main expression-handling function. --------- */

IRExpr* expr2tags_DC ( DCEnv* dce, IRExpr* e )
{
   //   ppIRExpr(e);
   //   printf("\n");

   switch (e->tag) {

      case Iex_Get:
         return shadow_GET_DC( dce, e->Iex.Get.offset, e->Iex.Get.ty );

      case Iex_GetI:
         return shadow_GETI_DC( dce, e->Iex.GetI.descr,
                                e->Iex.GetI.ix, e->Iex.GetI.bias );

      case Iex_RdTmp:
         return IRExpr_RdTmp( findShadowTmp_DC(dce, e->Iex.RdTmp.tmp) );

      case Iex_Const:

         // Approximate literals implementation - create a special reserved
         // WEAKE_FRESH_TAG tag one tag for each static instance of a
         // program literal:
         if (dyncomp_approximate_literals) {
	    return IRExpr_Const(IRConst_UWord(WEAK_FRESH_TAG));
         }
         else {
	    static Int static_fresh_count = 0;

            //            printf("******PREV CONST******\n");

            // Create one new tag for each dynamic instance of a program
            // literal - this provides perfect context sensitivity, but
            // at the expense of memory and time overheads:

	    /* Being a clean call means that the creation of the tag
	       can be optimized away if it's not used, which is
	       semantically OK and desirable for performance. It would
	       also means that if there are multiple tags created
	       together, they can be optimized into one, which is
	       theoretically not OK. This hasn't come up in an example
	       yet, but avoid it by passing a unique integer to each
	       call; this is also convenient during debugging. */
	    return assignNew_DC
	       (dce, Ity_Word,
		mkIRExprCCall(Ity_Word,
			      1 /*Int regparms*/,
			      "MC_(helperc_CREATE_TAG)",
			      &MC_(helperc_CREATE_TAG),
			      mkIRExprVec_1(IRExpr_Const
					    (IRConst_UWord
					     (static_fresh_count++)))));

            /* Old, slower dirty call variant:
	    IRDirty* di;
	    IRTemp   datatag;
            datatag = newIRxoTemp(dce->bb->tyenv, Ity_Word);
            di = unsafeIRDirty_1_N( datatag,
                                    0*regparms*,
                                    "MC_(helperc_CREATE_TAG)",
                                    &MC_(helperc_CREATE_TAG),
                                    mkIRExprVec_0());
            setHelperAnns_DC( dce, di );
            stmt( dce->bb, IRStmt_Dirty(di) );

            return mkexpr(datatag);*/
         }

      case Iex_Qop:
         return expr2tags_Qop_DC(
                   dce,
                   e->Iex.Qop.details->op,
                   e->Iex.Qop.details->arg1,
                   e->Iex.Qop.details->arg2,
                   e->Iex.Qop.details->arg3,
                   e->Iex.Qop.details->arg4
                );

      case Iex_Triop:
         return expr2tags_Triop_DC(
                   dce,
                   e->Iex.Triop.details->op,
                   e->Iex.Triop.details->arg1,
                   e->Iex.Triop.details->arg2,
                   e->Iex.Triop.details->arg3
                );

      case Iex_Binop:
         return expr2tags_Binop_DC(
                   dce,
                   e->Iex.Binop.op,
                   e->Iex.Binop.arg1, e->Iex.Binop.arg2
                );

      case Iex_Unop:
         return expr2tags_Unop_DC( dce, e->Iex.Unop.arg );

      case Iex_Load:
         return expr2tags_LDle_DC( dce, e->Iex.Load.ty,
                                      e->Iex.Load.addr, 0/*addr bias*/ );

      case Iex_CCall:
         return handleCCall_DC( dce,
                                e->Iex.CCall.args,
                                e->Iex.CCall.cee );

      case Iex_ITE:
         return expr2tags_ITE_DC( dce, e->Iex.ITE.cond, e->Iex.ITE.iftrue,
                                    e->Iex.ITE.iffalse);

      default:
         printf("\n");
         ppIRExpr(e);
         printf("\n");
         VG_(tool_panic)("dyncomp: expr2tags_DC");
   }
}

/* PG says we might need to resync this with Memcheck's
   do_shadow_Store().  The only problem I know about is fixing an
   endianness assumption in the 128-bit case. -SMcC */
void do_shadow_STle_DC ( DCEnv* dce,
                      IRAtom* addr,
                      IRAtom* data )
{
   IROp     mkAdd;
   IRType   ty, tyAddr;
   IRDirty  *di, *diLo64, *diHi64, *diAddr;
   IRAtom   *addrHi64;
   IRAtom   *vdata;
   IRAtom   *vaddr;
   IRTemp   addrTag;
   void*    helper = NULL;
   const HChar* hname = NULL;
   Int      pcOffset = -1;

   tyAddr = dce->hWordTy;
   mkAdd  = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
   tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );

   di = diLo64 = diHi64 = NULL;
   addrHi64 = NULL;

   tl_assert(data);
   //   tl_assert(isOriginalAtom_DC(dce, data));
   if (data->tag == Iex_Const &&
       (tyAddr == Ity_I32 && data->Iex.Const.con->tag == Ico_U32)) {
      pcOffset = data->Iex.Const.con->Ico.U32 - dce->origAddr;
   } else if (data->tag == Iex_Const &&
	      (tyAddr == Ity_I64 && data->Iex.Const.con->tag == Ico_U64)) {
      pcOffset = data->Iex.Const.con->Ico.U64 - dce->origAddr;
   }
   if (pcOffset > 0 && pcOffset < 20) {
      /* We're storing what looks like the address of the sequentially
	 next instruction, so we're probably pushing the PC on the
	 stack in a call. Normally it wouldn't matter what tag this
	 value had, since the value is only used later in a jump, but
	 for PIC x86 code a return address is also used to initialize
	 the GOT pointer, and we don't want that to have a tag that
	 falsely links all the globals accessed via it. */
      vdata = IRExpr_Const(IRConst_UWord(0));
   } else {
      vdata = expr2tags_DC( dce, data );
   }
   tl_assert(isShadowAtom_DC(dce,vdata));

   /* Compute the tag for the effective address, and throw the result
      away, but anchor it to a dirty call so that Valgrind doesn't
      optimize the merges away. */
   tl_assert(addr);
   tl_assert(isOriginalAtom_DC(dce, addr));
   vaddr = expr2tags_DC(dce, addr);
   tl_assert(isShadowAtom_DC(dce, vaddr));
   addrTag = newTemp(dce->mce, Ity_Word, DC);
   diAddr = unsafeIRDirty_1_N(addrTag, 1, "MC_(helperc_TAG_NOP)",
			      &MC_(helperc_TAG_NOP), mkIRExprVec_1(vaddr));
   setHelperAnns_DC(dce, diAddr);
   stmt_DC('V', dce, IRStmt_Dirty(diAddr));

   // Get the byte size of the REAL data (and not our tag vdata, which
   // is ALWAYS word-sized).  This is very different from Memcheck's
   // V-bits, which is always guaranteed to be the same byte size as 'data'
   // Also, we must use shadowType to translate all type sizes
   // to integral sizes
   ty = shadowTypeV(typeOfIRExpr(dce->bb->tyenv, data));

   /* Now decide which helper function to call to write the data tag
      into shadow memory. */
   switch (ty) {
      case Ity_V128: /* we'll use the helper twice */
      case Ity_I64: helper = &MC_(helperc_STORE_TAG_8);
                    hname = "MC_(helperc_STORE_TAG_8)";
                    break;
      case Ity_I32: helper = &MC_(helperc_STORE_TAG_4);
                    hname = "MC_(helperc_STORE_TAG_4)";
                    break;
      case Ity_I16: helper = &MC_(helperc_STORE_TAG_2);
                    hname = "MC_(helperc_STORE_TAG_2)";
                    break;
      case Ity_I8:  helper = &MC_(helperc_STORE_TAG_1);
                    hname = "MC_(helperc_STORE_TAG_1)";
                    break;
      default:      VG_(tool_panic)("dyncomp:do_shadow_STle_DC");
   }

   if (ty == Ity_V128) {
      IRAtom *eight = tyAddr==Ity_I32 ? mkU32(8) : mkU64(8);
      // (comment added 2006)
      /* XXX this branch assumes little-endianness, and would need to
	 be fixed for a PPC port. */

      /* V128-bit case */
      /* See comment in next clause re 64-bit regparms */
      diLo64    = unsafeIRDirty_0_N(
                     1/*regparms*/, hname, helper,
                     mkIRExprVec_2( addr, vdata ));

      addrHi64  = assignNew_DC(dce, tyAddr, binop(mkAdd, addr, eight) );
      diHi64    = unsafeIRDirty_0_N(
                     1/*regparms*/, hname, helper,
                     mkIRExprVec_2( addrHi64, vdata ));

      setHelperAnns_DC( dce, diLo64 );
      setHelperAnns_DC( dce, diHi64 );
      stmt_DC('V',  dce, IRStmt_Dirty(diLo64) );
      stmt_DC('V',  dce, IRStmt_Dirty(diHi64) );

   } else {
      /* 8/16/32/64-bit cases */

      // For some reason, we still need to make a special case for
      // 64-bit things ... I dunno why, though ???
      if (ty == Ity_I64) {
         /* We can't do this with regparm 2 on 32-bit platforms, since
            the back ends aren't clever enough to handle 64-bit
            regparm args.  Therefore be different. */
         di = unsafeIRDirty_0_N(
                                1/*regparms*/, hname, helper,
                                mkIRExprVec_2( addr, vdata ));
      } else {
         di = unsafeIRDirty_0_N(
                                2/*regparms*/, hname, helper,
                                mkIRExprVec_2( addr, vdata ));
      }

      setHelperAnns_DC( dce, di );
      stmt_DC('V',  dce, IRStmt_Dirty(di) );
   }

}

// Handle dirty calls really stupidly by simply creating a fresh tag
// as the result of the dirty call.  This ignores all the stuff that
// goes on inside of the dirty call, but that should be okay.
void do_shadow_Dirty_DC ( DCEnv* dce, IRDirty* d ) {
   if (d->tmp != IRTemp_INVALID) {
      IRDirty* di = unsafeIRDirty_1_N(findShadowTmp_DC(dce, d->tmp),
                                      0/*regparms*/,
                                      "MC_(helperc_CREATE_TAG)",
                                      &MC_(helperc_CREATE_TAG),
                                      mkIRExprVec_0());
      setHelperAnns_DC( dce, di );
      stmt_DC('V',  dce, IRStmt_Dirty(di) );
   }
}

static void do_shadow_CAS_single_DC ( DCEnv* dce, IRCAS* cas ) {
   IRAtom *vdataLo = NULL, *bdataLo = NULL;
   IRAtom *vexpdLo = NULL, *bexpdLo = NULL;
   IRAtom *voldLo  = NULL, *boldLo  = NULL;
   IRAtom *expd_eq_old = NULL;
   IRAtom *orig;
   IROp   opCasCmpEQ;
   Int    elemSzB;
   IRType elemTy;
   IRType ty;
   /* Variables for the instrumented dirty call */
   IRDirty  *di;
   void*        helper = NULL;
   const HChar* hname = NULL;

   /* Silence unused variables. (These are kept around as opposed to
      being removed to keep dyncomp_translate.c analogues of
      mc_translate.c functions as similar as possible */
   (void)expd_eq_old; (void)boldLo; (void)bdataLo; (void)bexpdLo;
   (void)opCasCmpEQ; (void)elemSzB;

   /* single CAS */
   tl_assert(cas->oldHi == IRTemp_INVALID);
   tl_assert(cas->expdHi == NULL);
   tl_assert(cas->dataHi == NULL);

   elemTy = typeOfIRExpr(dce->bb->tyenv, cas->expdLo);

   switch (elemTy) {
      case Ity_I8:  elemSzB = 1; opCasCmpEQ = Iop_CasCmpEQ8;  break;
      case Ity_I16: elemSzB = 2; opCasCmpEQ = Iop_CasCmpEQ16; break;
      case Ity_I32: elemSzB = 4; opCasCmpEQ = Iop_CasCmpEQ32; break;
      case Ity_I64: elemSzB = 8; opCasCmpEQ = Iop_CasCmpEQ64; break;
   default: tl_assert(0); /* IR defn disallows any other types */
   }

   /* 1. fetch data# (the proposed new value) */
   tl_assert(isOriginalAtom_DC(dce, cas->dataLo));

   ty = shadowTypeV(typeOfIRExpr(dce->bb->tyenv, cas->dataLo));

   vdataLo
      = assignNew_DC(dce, ty, expr2tags_DC(dce, cas->dataLo));

   tl_assert(isShadowAtom_DC(dce, vdataLo));

   /* 2. fetch expected# (what we expect to see at the address) */
   tl_assert(isOriginalAtom_DC(dce, cas->expdLo));

   vexpdLo
      = assignNew_DC(dce, ty, expr2tags_DC(dce, cas->expdLo));

   tl_assert(isShadowAtom_DC(dce, vexpdLo));

   /* 3. check definedness of address */
   /* 4. fetch old# from shadow memory; this also checks
         addressibility of the address */

   voldLo
     = assignNew_DC(dce, elemTy,
                    expr2tags_LDle_DC(dce,elemTy, cas->addr, 0/*Addr bias*/));

   orig = mkexpr(cas->oldLo);

   tl_assert(isOriginalAtom_DC(dce, orig));
   tl_assert(isShadowAtom_DC(dce, voldLo));

   switch(orig->tag) {
      case Iex_Const:
         tl_assert(voldLo->tag == Iex_Const);
         break;
      case Iex_RdTmp:
         tl_assert(voldLo->tag == Iex_RdTmp);
         assign_DC('V', dce, findShadowTmp_DC(dce, orig->Iex.RdTmp.tmp),
                   voldLo);

         break;
      default:
         tl_assert(0);
   }

   //tl_assert(orig < dce->n_originalTmps);
   // if (dce->tmpMap[orig] == IRTemp_INVALID)

   // bind_shadow_tmp_to_orig('V', mce, mkexpr(cas->oldLo), voldLo);

   /* 5. the CAS itself */
   //   stmt( 'C', mce, IRStmt_CAS(cas) );
   // Memcheck does the above for us

   /* 6. compute "expected == old" */
   /* See COMMENT_ON_CasCmpEQ in this file background/rationale. */
   /* Note that 'C' is kinda faking it; it is indeed a non-shadow
      tree, but it's not copied from the input block. */
/*    assignNew('C', mce, Ity_I1, */
/*              binop(opCasCmpEQ, cas->expdLo, mkexpr(cas->oldLo))); */

   /* 7. if "expected == old"
            store data# to shadow memory */
   //   do_shadow_STle_DC( dce, cas->addr,  vdataLo/*vdata*/);

   switch (ty) {
      case Ity_I64: helper = &MC_(helperc_STORE_TAG_8);
                    hname = "MC_(helperc_STORE_TAG_8)";
                    break;
      case Ity_I32: helper = &MC_(helperc_STORE_TAG_4);
                    hname = "MC_(helperc_STORE_TAG_4)";
                    break;
      case Ity_I16: helper = &MC_(helperc_STORE_TAG_2);
                    hname = "MC_(helperc_STORE_TAG_2)";
                    break;
      case Ity_I8:  helper = &MC_(helperc_STORE_TAG_1);
                    hname = "MC_(helperc_STORE_TAG_1)";
                    break;
      default:      VG_(tool_panic)("dyncomp:do_shadow_STle_DC");
   }

   if (ty == Ity_I64) {
     /* We can't do this with regparm 2 on 32-bit platforms, since
        the back ends aren't clever enough to handle 64-bit
        regparm args.  Therefore be different. */
     di = unsafeIRDirty_0_N(
                            1/*regparms*/, hname, helper,
                            mkIRExprVec_2( cas->addr, vdataLo ));
   } else {
     di = unsafeIRDirty_0_N(
                            2/*regparms*/, hname, helper,
                            mkIRExprVec_2( cas->addr, vdataLo ));
   }

   setHelperAnns_DC( dce, di );
   stmt_DC('V',  dce, IRStmt_Dirty(di) );

}

static void do_shadow_CAS_double_DC ( DCEnv* dce, IRCAS* cas )
{
   IRAtom *vdataHi = NULL, *bdataHi = NULL;
   IRAtom *vdataLo = NULL, *bdataLo = NULL;
   IRAtom *vexpdHi = NULL, *bexpdHi = NULL;
   IRAtom *vexpdLo = NULL, *bexpdLo = NULL;
   IRAtom *voldHi  = NULL, *boldHi  = NULL;
   IRAtom *voldLo  = NULL, *boldLo  = NULL;
   IRAtom *xHi = NULL, *xLo = NULL, *xHL = NULL;
   IRAtom *expd_eq_old = NULL, *zero = NULL;
   IRAtom *origLo;
   IRAtom *origHi;
   IROp   opCasCmpEQ, opOr, opXor;
   Int    elemSzB, memOffsLo, memOffsHi;
   IRType elemTy;
   IRType ty;
   IRDirty  *di;
   /* Variables for the instrumented dirty call */
   void*        helper = NULL;
   const HChar* hname = NULL;

   /* Silence unused variables. (These are kept around as opposed to
      being removed to keep dyncomp_translate.c analogues of
      mc_translate.c functions as similar as possible */
   (void)expd_eq_old;(void)boldLo;(void)boldHi;
   (void)bexpdLo;(void)bexpdHi;(void)bdataLo;(void)bdataHi;
   (void)xHL;(void)xHi;(void)xLo;
   (void)zero;(void)opCasCmpEQ;(void)opOr;(void)opXor;


   /* double CAS */
   tl_assert(cas->oldHi != IRTemp_INVALID);
   tl_assert(cas->expdHi != NULL);
   tl_assert(cas->dataHi != NULL);

   elemTy = typeOfIRExpr(dce->bb->tyenv, cas->expdLo);
   switch (elemTy) {
      case Ity_I8:
         opCasCmpEQ = Iop_CasCmpEQ8; opOr = Iop_Or8; opXor = Iop_Xor8;
         elemSzB = 1; zero = mkU8(0);
         break;
      case Ity_I16:
         opCasCmpEQ = Iop_CasCmpEQ16; opOr = Iop_Or16; opXor = Iop_Xor16;
         elemSzB = 2; zero = mkU16(0);
         break;
      case Ity_I32:
         opCasCmpEQ = Iop_CasCmpEQ32; opOr = Iop_Or32; opXor = Iop_Xor32;
         elemSzB = 4; zero = mkU32(0);
         break;
      case Ity_I64:
         opCasCmpEQ = Iop_CasCmpEQ64; opOr = Iop_Or64; opXor = Iop_Xor64;
         elemSzB = 8; zero = mkU64(0);
         break;
      default:
         tl_assert(0); /* IR defn disallows any other types */
   }

   /* 1. fetch data# (the proposed new value) */
   tl_assert(isOriginalAtom_DC(dce, cas->dataHi));
   tl_assert(isOriginalAtom_DC(dce, cas->dataLo));

   vdataHi
      = assignNew_DC(dce, elemTy, expr2tags_DC(dce, cas->dataHi));
   vdataLo
      = assignNew_DC(dce, elemTy, expr2tags_DC(dce, cas->dataLo));

   ty = shadowTypeV(typeOfIRExpr(dce->bb->tyenv, cas->dataLo));


   tl_assert(isShadowAtom_DC(dce, vdataHi));
   tl_assert(isShadowAtom_DC(dce, vdataLo));

   /* 2. fetch expected# (what we expect to see at the address) */
   tl_assert(isOriginalAtom_DC(dce, cas->expdHi));
   tl_assert(isOriginalAtom_DC(dce, cas->expdLo));

   vexpdHi
      = assignNew_DC(dce, elemTy, expr2tags_DC(dce, cas->expdHi));
   vexpdLo
      = assignNew_DC(dce, elemTy, expr2tags_DC(dce, cas->expdLo));
   tl_assert(isShadowAtom_DC(dce, vexpdHi));
   tl_assert(isShadowAtom_DC(dce, vexpdLo));

   /* 3. check definedness of address */
   /* 4. fetch old# from shadow memory; this also checks
         addressibility of the address */
   if (cas->end == Iend_LE) {
      memOffsLo = 0;
      memOffsHi = elemSzB;
   } else {
      tl_assert(cas->end == Iend_BE);
      memOffsLo = elemSzB;
      memOffsHi = 0;
   }
   voldHi
      = assignNew_DC(
           dce, elemTy,
           expr2tags_LDle_DC(dce, elemTy, cas->addr, memOffsHi/*Addr bias*/ ));
   voldLo
      = assignNew_DC(
           dce, elemTy,
           expr2tags_LDle_DC(dce, elemTy, cas->addr, memOffsLo/*Addr bias*/));

   origLo = mkexpr(cas->oldLo);
   origHi = mkexpr(cas->oldHi);


   switch(origLo->tag) {
      case Iex_Const:
         tl_assert(voldLo->tag == Iex_Const);
         break;
      case Iex_RdTmp:
         tl_assert(voldLo->tag == Iex_RdTmp);
         assign_DC('V', dce, findShadowTmp_DC(dce, origLo->Iex.RdTmp.tmp),
                   voldLo);
         assign_DC('V', dce, findShadowTmp_DC(dce, origHi->Iex.RdTmp.tmp),
                   voldHi);

         break;
      default:
         tl_assert(0);
   }

   /* 5. the CAS itself */
   /* 6. compute "expected == old" */
   /* See COMMENT_ON_CasCmpEQ in this file background/rationale. */
   /* Note that 'C' is kinda faking it; it is indeed a non-shadow
      tree, but it's not copied from the input block. */
   /*
      xHi = oldHi ^ expdHi;
      xLo = oldLo ^ expdLo;
      xHL = xHi | xLo;
      expd_eq_old = xHL == 0;
   */
/*    xHi = assignNew('C', mce, elemTy, */
/*                    binop(opXor, cas->expdHi, mkexpr(cas->oldHi))); */
/*    xLo = assignNew('C', mce, elemTy, */
/*                    binop(opXor, cas->expdLo, mkexpr(cas->oldLo))); */
/*    xHL = assignNew('C', mce, elemTy, */
/*                    binop(opOr, xHi, xLo)); */
/*    expd_eq_old */
/*       = assignNew('C', mce, Ity_I1, */
/*                   binop(opCasCmpEQ, xHL, zero)); */

   /* 7. if "expected == old"
            store data# to shadow memory */


   switch (ty) {
      case Ity_I64: helper = &MC_(helperc_STORE_TAG_8);
                    hname = "MC_(helperc_STORE_TAG_8)";
                    break;
      case Ity_I32: helper = &MC_(helperc_STORE_TAG_4);
                    hname = "MC_(helperc_STORE_TAG_4)";
                    break;
      case Ity_I16: helper = &MC_(helperc_STORE_TAG_2);
                    hname = "MC_(helperc_STORE_TAG_2)";
                    break;
      case Ity_I8:  helper = &MC_(helperc_STORE_TAG_1);
                    hname = "MC_(helperc_STORE_TAG_1)";
                    break;
      default:      VG_(tool_panic)("dyncomp:do_shadow_STle_DC");
   }

   if (ty == Ity_I64) {
     /* We can't do this with regparm 2 on 32-bit platforms, since
        the back ends aren't clever enough to handle 64-bit
        regparm args.  Therefore be different. */
     di = unsafeIRDirty_0_N(
                            1/*regparms*/, hname, helper,
                            mkIRExprVec_2( cas->addr + memOffsLo, vdataLo ));
     setHelperAnns_DC( dce, di );
     stmt_DC('V',  dce, IRStmt_Dirty(di) );

     di = unsafeIRDirty_0_N(
                            1/*regparms*/, hname, helper,
                            mkIRExprVec_2( cas->addr + memOffsHi, vdataHi ));

     setHelperAnns_DC( dce, di );
     stmt_DC('V',  dce, IRStmt_Dirty(di) );
   } else {
     di = unsafeIRDirty_0_N(
                            2/*regparms*/, hname, helper,
                            mkIRExprVec_2( cas->addr + memOffsLo, vdataLo ));
     setHelperAnns_DC( dce, di );
     stmt_DC('V',  dce, IRStmt_Dirty(di) );

     di = unsafeIRDirty_0_N(
                            2/*regparms*/, hname, helper,
                            mkIRExprVec_2( cas->addr + memOffsHi, vdataHi ));

     setHelperAnns_DC( dce, di );
     stmt_DC('V',  dce, IRStmt_Dirty(di) );
   }
}

// Handling for CAS instructions. Nick'd from memcheck.
// NOTE: This is copied and modified from mc_translate.c:
// do_shadow_CAS()
void do_shadow_CAS_DC ( DCEnv* dce, IRCAS* cas) {

  if (cas->oldHi == IRTemp_INVALID) {
    do_shadow_CAS_single_DC( dce, cas );
  } else {
    do_shadow_CAS_double_DC( dce, cas );
  }

}
