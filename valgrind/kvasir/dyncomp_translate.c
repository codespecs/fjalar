
/*--------------------------------------------------------------------*/
/*--- Instrument IR to perform tag operations for DynComp.         ---*/
/*--- (Analogous to mc_translate.c for MemCheck)                   ---*/
/*---                                          dyncomp_translate.c ---*/
/*--------------------------------------------------------------------*/

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

  Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

#include "mc_include.h"
#include "mc_translate.h"
#include "dyncomp_translate.h"
#include "kvasir_runtime.h"
#include "kvasir_main.h"

/* Find the tmp currently shadowing the given original tmp.  If none
   so far exists, allocate one.  */
IRTemp findShadowTmp_DC ( DCEnv* dce, IRTemp orig )
{
   tl_assert(orig < dce->n_originalTmps);
   if (dce->tmpMap[orig] == IRTemp_INVALID) {
      dce->tmpMap[orig]
         = newIRTemp(dce->bb->tyenv,
                     //shadowType_DC(dce->bb->tyenv->types[orig]));
                     Ity_I32); // PG - tags are always 32 bits
   }
   return dce->tmpMap[orig];
}

/* (used for sanity checks only): is this an atom which looks
   like it's from original code? */
static Bool isOriginalAtom_DC ( DCEnv* dce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_Tmp && a1->Iex.Tmp.tmp < dce->n_originalTmps)
      return True;
   return False;
}

/* (used for sanity checks only): is this an atom which looks
   like it's from shadow code? */
static Bool isShadowAtom_DC ( DCEnv* dce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_Tmp && a1->Iex.Tmp.tmp >= dce->n_originalTmps)
      return True;
   return False;
}

static IRAtom* assignNew_DC ( DCEnv* dce, IRType ty, IRExpr* e ) {
   IRTemp t = newIRTemp(dce->bb->tyenv, ty);
   assign(dce->bb, t, e);
   return mkexpr(t);
}

// TODO: Is this the correct behavior for our purposes?
/* Set the annotations on a dirty helper to indicate that the stack
   pointer and instruction pointers might be read.  This is the
   behaviour of all 'emit-a-complaint' style functions we might
   call. */
static void setHelperAnns_DC ( DCEnv* dce, IRDirty* di ) {
   di->nFxState = 2;
   di->fxState[0].fx     = Ifx_Read;
   di->fxState[0].offset = dce->layout->offset_SP;
   di->fxState[0].size   = dce->layout->sizeof_SP;
   di->fxState[1].fx     = Ifx_Read;
   di->fxState[1].offset = dce->layout->offset_IP;
   di->fxState[1].size   = dce->layout->sizeof_IP;
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

   /* Do a plain shadow Put. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   stmt( dce->bb,
         IRStmt_Put( (4 * offset) + (2 * dce->layout->total_sizeB), vatom ) );
}

// A PUTI stores a value (dynamically indexed) into the guest state
// (for x86, this seems to be only used for floating point values)
void do_shadow_PUTI_DC ( DCEnv* dce,
                      IRArray* descr, IRAtom* ix, Int bias, IRAtom* atom )
{
   IRAtom* vatom;
   IRType  ty;

   tl_assert(isOriginalAtom_DC(dce,atom));
   vatom = expr2tags_DC( dce, atom );
   tl_assert(sameKindedAtoms(atom, vatom));
   ty   = descr->elemTy;
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom_DC(dce,ix));
   /* Do a cloned version of the Put that refers to the tag shadow
      area. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   IRArray* new_descr
      = mkIRArray( (4 * descr->base) + (2 * dce->layout->total_sizeB),
                   Ity_I32, descr->nElems); // Tags are 32 bits

   stmt( dce->bb, IRStmt_PutI( new_descr, ix, bias, vatom ));
}

static
IRExpr* shadow_GET_DC ( DCEnv* dce, Int offset, IRType ty )
{
   tl_assert(ty != Ity_I1);
   /* return a cloned version of the Get that refers to the tag
      shadow area. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   return IRExpr_Get( (4 * offset) + (2 * dce->layout->total_sizeB),
                      Ity_I32 ); // Tags are 32 bits
}

static
IRExpr* shadow_GETI_DC ( DCEnv* dce, IRArray* descr, IRAtom* ix, Int bias )
{
   IRType ty   = descr->elemTy;
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom_DC(dce,ix));
   /* return a cloned version of the Get that refers to the
      tag shadow area. */
   // PG - Remember the new layout in ThreadArchState
   //      which requires (4 * offset) + (2 * base size)
   IRArray* new_descr
      = mkIRArray( (4 * descr->base) + (2 * dce->layout->total_sizeB),
                   Ity_I32, descr->nElems); // Tags are 32 bits

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
static
IRAtom* handleCCall_DC ( DCEnv* dce,
                         IRAtom** exprvec, IRType finalVtype, IRCallee* cee )
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
            if (0) VG_(printf)("excluding %s(%d)\n", cee->name, i);
         } else {
            /* merge the tags of first and current arguments */
            cur = expr2tags_DC(dce, exprvec[i]);

            datatag = newIRTemp(dce->bb->tyenv, Ity_I32);
            di = unsafeIRDirty_1_N(datatag,
                                   2,
                                   "MC_(helperc_MERGE_TAGS)",
                                   &MC_(helperc_MERGE_TAGS),
                                   mkIRExprVec_2( first, cur ));

            setHelperAnns_DC( dce, di );
            stmt(dce->bb, IRStmt_Dirty(di));
         }
      }
      // Return the tag of the first argument, if there is one
      return first;
   }
   else {
      return IRExpr_Const(IRConst_U32(0));
   }
}


/*------------------------------------------------------------*/
/*--- Generate shadow values from all kinds of IRExprs.    ---*/
/*------------------------------------------------------------*/

// This is where we need to add calls to helper functions to
// merge tags because here is where the 'interactions' take place

// Yes, this code can be cleaned up a bit, but I'll leave it
// as one big switch statement for now in order to provide
// flexibility for future edits
static
IRAtom* expr2tags_Binop_DC ( DCEnv* dce,
                              IROp op,
                              IRAtom* atom1, IRAtom* atom2 )
{
   IRAtom* vatom1 = expr2tags_DC( dce, atom1 );
   IRAtom* vatom2 = expr2tags_DC( dce, atom2 );

   void*    helper = 0;
   Char*    hname = 0;
   //   IRDirty* di;
   //   IRTemp   datatag;

   tl_assert(isOriginalAtom_DC(dce,atom1));
   tl_assert(isOriginalAtom_DC(dce,atom2));
   tl_assert(isShadowAtom_DC(dce,vatom1));
   tl_assert(isShadowAtom_DC(dce,vatom2));
   tl_assert(sameKindedAtoms(atom1,vatom1));
   tl_assert(sameKindedAtoms(atom2,vatom2));

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
   case Iop_Add8:  case Iop_Add16:  case Iop_Add32:  case Iop_Add64:
   case Iop_Sub8:  case Iop_Sub16:  case Iop_Sub32:  case Iop_Sub64:
      /* Signless mul.  MullS/MullU is elsewhere. */
   case Iop_Mul8:  case Iop_Mul16:  case Iop_Mul32:  case Iop_Mul64:
   case Iop_Or8:   case Iop_Or16:   case Iop_Or32:   case Iop_Or64:
   case Iop_And8:  case Iop_And16:  case Iop_And32:  case Iop_And64:
   case Iop_Xor8:  case Iop_Xor16:  case Iop_Xor32:  case Iop_Xor64:
      /* Widening multiplies */
   case Iop_MullS8: case Iop_MullS16: case Iop_MullS32: case Iop_MullS64:
   case Iop_MullU8: case Iop_MullU16: case Iop_MullU32: case Iop_MullU64:
      /* Division */
      /* TODO: clarify semantics wrt rounding, negative values, whatever */
   case Iop_DivU32:   // :: I32,I32 -> I32 (simple div, no mod)
   case Iop_DivS32:   // ditto, signed

   case Iop_DivModU64to32: // :: I64,I32 -> I64
      // of which lo half is div and hi half is mod
   case Iop_DivModS64to32: // ditto, signed

   case Iop_DivModU128to64: // :: V128,I64 -> V128
      // of which lo half is div and hi half is mod
   case Iop_DivModS128to64: // ditto, signed

      /* ------ Floating point.  We try and be IEEE754 compliant. ------ */

      /* Binary operations mandated by IEEE754. */
   case Iop_AddF64: case Iop_SubF64: case Iop_MulF64: case Iop_DivF64: /* Iop_RemF64, */

      /* Binary ops supported by IA32 but not mandated by 754. */
   case Iop_AtanF64:       /* FPATAN,  arctan(arg1/arg2)       */
   case Iop_Yl2xF64:       /* FYL2X,   arg1 * log2(arg2)       */
   case Iop_Yl2xp1F64:     /* FYL2XP1, arg1 * log2(arg2+1.0)   */
   case Iop_PRemF64:       /* FPREM,   non-IEEE remainder(arg1/arg2)    */
   case Iop_PRem1F64:      /* FPREM1,  IEEE remainder(arg1/arg2)    */
   case Iop_ScaleF64:      /* FSCALE,  arg1 * (2^RoundTowardsZero(arg2)) */
      /* Note that on x86 guest, PRem1{C3210} has the same behaviour
         as the IEEE mandated RemF64, except it is limited in the
         range of its operand.  Hence the partialness. */

      /* ------------------ 64-bit SIMD Integer. ------------------ */

      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x8:   case Iop_Add16x4:   case Iop_Add32x2:
   case Iop_QAdd8Ux8: case Iop_QAdd16Ux4:
   case Iop_QAdd8Sx8: case Iop_QAdd16Sx4:

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x8:   case Iop_Sub16x4:   case Iop_Sub32x2:
   case Iop_QSub8Ux8: case Iop_QSub16Ux4:
   case Iop_QSub8Sx8: case Iop_QSub16Sx4:

      /* MULTIPLICATION (normal / high half of signed/unsigned) */
   case Iop_Mul16x4:
   case Iop_MulHi16Ux4:
   case Iop_MulHi16Sx4:

      /* AVERAGING: note: (arg1 + arg2 + 1) >>u 1 */
   case Iop_Avg8Ux8:
   case Iop_Avg16Ux4:

      /* MIN/MAX */
   case Iop_Max16Sx4:
   case Iop_Max8Ux8:
   case Iop_Min16Sx4:
   case Iop_Min8Ux8:

      /* ------------------ 128-bit SIMD FP. ------------------ */

      /* --- 32x4 vector FP --- */

   case Iop_Add32Fx4: case Iop_Sub32Fx4: case Iop_Mul32Fx4: case Iop_Div32Fx4:
   case Iop_Max32Fx4: case Iop_Min32Fx4:

      /* --- 32x4 lowest-lane-only scalar FP --- */

   case Iop_Add32F0x4: case Iop_Sub32F0x4: case Iop_Mul32F0x4: case Iop_Div32F0x4:
   case Iop_Max32F0x4: case Iop_Min32F0x4:

      /* --- 64x2 vector FP --- */

   case Iop_Add64Fx2: case Iop_Sub64Fx2: case Iop_Mul64Fx2: case Iop_Div64Fx2:
   case Iop_Max64Fx2: case Iop_Min64Fx2:

      /* --- 64x2 lowest-lane-only scalar FP --- */

   case Iop_Add64F0x2: case Iop_Sub64F0x2: case Iop_Mul64F0x2: case Iop_Div64F0x2:
   case Iop_Max64F0x2: case Iop_Min64F0x2:

      /* ------------------ 128-bit SIMD Integer. ------------------ */

      /* BITWISE OPS */
   case Iop_AndV128: case Iop_OrV128: case Iop_XorV128:

      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x16:   case Iop_Add16x8:   case Iop_Add32x4:  case Iop_Add64x2:
   case Iop_QAdd8Ux16: case Iop_QAdd16Ux8:
   case Iop_QAdd8Sx16: case Iop_QAdd16Sx8:

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x16:   case Iop_Sub16x8:   case Iop_Sub32x4:  case Iop_Sub64x2:
   case Iop_QSub8Ux16: case Iop_QSub16Ux8:
   case Iop_QSub8Sx16: case Iop_QSub16Sx8:

      /* MULTIPLICATION (normal / high half of signed/unsigned) */
   case Iop_Mul16x8:
   case Iop_MulHi16Ux8:
   case Iop_MulHi16Sx8:

      /* AVERAGING: note: (arg1 + arg2 + 1) >>u 1 */
   case Iop_Avg8Ux16:
   case Iop_Avg16Ux8:

      /* MIN/MAX */
   case Iop_Max16Sx8:
   case Iop_Max8Ux16:
   case Iop_Min16Sx8:
   case Iop_Min8Ux16:


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
   case Iop_QNarrow16Ux4:
   case Iop_QNarrow16Sx4:
   case Iop_QNarrow32Sx2:

      /* INTERLEAVING -- interleave lanes from low or high halves of
         operands.  Most-significant result lane is from the left
         arg. */
   case Iop_InterleaveHI8x8: case Iop_InterleaveHI16x4: case Iop_InterleaveHI32x2:
   case Iop_InterleaveLO8x8: case Iop_InterleaveLO16x4: case Iop_InterleaveLO32x2:

      // Ditto for 128-bit SIMD integer narrowing and interleaving

      /* NARROWING -- narrow 2xV128 into 1xV128, hi half from left arg */
   case Iop_QNarrow16Ux8:
   case Iop_QNarrow16Sx8:
   case Iop_QNarrow32Sx4:

      /* INTERLEAVING -- interleave lanes from low or high halves of
         operands.  Most-significant result lane is from the left
         arg. */
   case Iop_InterleaveHI8x16: case Iop_InterleaveHI16x8:
   case Iop_InterleaveHI32x4: case Iop_InterleaveHI64x2:
   case Iop_InterleaveLO8x16: case Iop_InterleaveLO16x8:
   case Iop_InterleaveLO32x4: case Iop_InterleaveLO64x2:


      // Comparisons ALSO qualify as interactions

      /* Integer comparisons. */
   case Iop_CmpEQ8:  case Iop_CmpEQ16:  case Iop_CmpEQ32:  case Iop_CmpEQ64:
   case Iop_CmpNE8:  case Iop_CmpNE16:  case Iop_CmpNE32:  case Iop_CmpNE64:
   case Iop_CmpLT32S:
   case Iop_CmpLE32S:
   case Iop_CmpLT32U:
   case Iop_CmpLE32U:

      // Floating-point comparison
   case Iop_CmpF64:

      // 64-bit SIMD integer comparisons
      /* MISC (vector integer cmp != 0) */
   case Iop_CmpNEZ8x8: case Iop_CmpNEZ16x4: case Iop_CmpNEZ32x2:

      /* COMPARISON */
   case Iop_CmpEQ8x8:  case Iop_CmpEQ16x4:  case Iop_CmpEQ32x2:
   case Iop_CmpGT8Sx8: case Iop_CmpGT16Sx4: case Iop_CmpGT32Sx2:

      // 128-bit SIMD FP
   case Iop_CmpEQ32Fx4: case Iop_CmpLT32Fx4: case Iop_CmpLE32Fx4: case Iop_CmpUN32Fx4:
   case Iop_CmpEQ32F0x4: case Iop_CmpLT32F0x4: case Iop_CmpLE32F0x4: case Iop_CmpUN32F0x4:
   case Iop_CmpEQ64Fx2: case Iop_CmpLT64Fx2: case Iop_CmpLE64Fx2: case Iop_CmpUN64Fx2:
   case Iop_CmpEQ64F0x2: case Iop_CmpLT64F0x2: case Iop_CmpLE64F0x2: case Iop_CmpUN64F0x2:

      /* ------------------ 128-bit SIMD Integer. ------------------ */

      /* MISC (vector integer cmp != 0) */
   case Iop_CmpNEZ8x16: case Iop_CmpNEZ16x8: case Iop_CmpNEZ32x4: case Iop_CmpNEZ64x2:

      /* COMPARISON */
   case Iop_CmpEQ8x16:  case Iop_CmpEQ16x8:  case Iop_CmpEQ32x4:
   case Iop_CmpGT8Sx16: case Iop_CmpGT16Sx8: case Iop_CmpGT32Sx4:

      // Random bogus stuff do not qualify as interactions

   case Iop_PRemC3210F64:  /* C3210 flags resulting from FPREM, :: I32 */
   case Iop_PRem1C3210F64: /* C3210 flags resulting from FPREM1, :: I32 */

      helper = &MC_(helperc_MERGE_TAGS);
      hname = "MC_(helperc_MERGE_TAGS)";
      break;


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
   case Iop_Shl8:  case Iop_Shl16:  case Iop_Shl32:  case Iop_Shl64:
   case Iop_Shr8:  case Iop_Shr16:  case Iop_Shr32:  case Iop_Shr64:
   case Iop_Sar8:  case Iop_Sar16:  case Iop_Sar32:  case Iop_Sar64:

      // 64-bit SIMD integer shifts:

      /* VECTOR x SCALAR SHIFT (shift amt :: Ity_I8) */
   case Iop_ShlN16x4: case Iop_ShlN32x2:
   case Iop_ShrN16x4: case Iop_ShrN32x2:
   case Iop_SarN16x4: case Iop_SarN32x2:

      /* ------------------ 128-bit SIMD Integer. ------------------ */

      /* VECTOR x SCALAR SHIFT (shift amt :: Ity_I8) */
   case Iop_ShlN16x8: case Iop_ShlN32x4: case Iop_ShlN64x2:
   case Iop_ShrN16x8: case Iop_ShrN32x4: case Iop_ShrN64x2:
   case Iop_SarN16x8: case Iop_SarN32x4:

      // From the looks of the spec., we want to return the tag
      // of the first argument
   case Iop_SetV128lo32:  // :: (V128,I32) -> V128

      return vatom1;
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
   case Iop_F64toI16:  /* IRRoundingMode(I32) x F64 -> I16 */
   case Iop_F64toI32:  /* IRRoundingMode(I32) x F64 -> I32 */
   case Iop_F64toI64:  /* IRRoundingMode(I32) x F64 -> I64 */
   case Iop_I64toF64:  /* IRRoundingMode(I32) x I64 -> F64 */
   case Iop_F64toF32:  /* IRRoundingMode(I32) x F64 -> F32 */
      /* F64 -> F64, also takes an I32 first argument encoding the
         rounding mode. */
   case Iop_RoundF64:

      return vatom2;
      break;

      // Hopefully we will never get here if we've had had cases which
      // handle every possible IR binary op. type (right?)
   default:
      ppIROp(op);
      VG_(tool_panic)("dyncomp:expr2tags_Binop_DC");
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
      // Tags are always 32 bits
      //      datatag = newIRTemp(dce->bb->tyenv, Ity_I32);
      //      di = unsafeIRDirty_1_N(datatag,
      //                             2,
      //                             hname,
      //                             helper,
      //                             mkIRExprVec_2( vatom1, vatom2 ));

      //      setHelperAnns_DC( dce, di );
      //      stmt( dce->bb, IRStmt_Dirty(di) );
      //      return mkexpr(datatag);

      // Let's try a clean call.  It seems to be correct
      // because of the fact that merging the same 2 things more than
      // once (in close proximity) doesn't hurt
      // DO NOT use clean call unless it has NO side effects and
      // is purely functional like an IRExpr
      return mkIRExprCCall (Ity_I32,
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
      return IRExpr_Const(IRConst_U32(0));
   }
}


static
IRExpr* expr2tags_Unop_DC ( DCEnv* dce, IROp op, IRAtom* atom )
{
   IRAtom* vatom = expr2tags_DC( dce, atom );
   tl_assert(isOriginalAtom_DC(dce,atom));

   // Do nothing with unary ops.  Just evaluate the
   // sub-expression and return it:
   // TODO: Actually, when you widen stuff, don't you want to
   //       create new tags for the new bytes and merge them?
   //       But you can't do that because you only have the 32-bit
   //       tag and NOT the memory locations it came from
   //       ... I guess we don't care since during binary ops.,
   //       we only consider the tag of the first bytes of each
   //       operand anyways.
   return vatom;
}


/* Worker function; do not call directly. */
static
IRAtom* expr2tags_LDle_WRK_DC ( DCEnv* dce, IRType ty, IRAtom* addr, UInt bias )
{
   void*    helper;
   Char*    hname;
   IRDirty* di;
   IRTemp   datatag;
   IRAtom*  addrAct;

   tl_assert(isOriginalAtom_DC(dce,addr));

   /* Now cook up a call to the relevant helper function, to read the
      tag for the given address. */
   ty = shadowType(ty);
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
   datatag = newIRTemp(dce->bb->tyenv, Ity_I32); // PG - tags are always 32 bits
   di = unsafeIRDirty_1_N( datatag,
                           1/*regparms*/, hname, helper,
                           mkIRExprVec_1( addrAct ));
   setHelperAnns_DC( dce, di );
   stmt( dce->bb, IRStmt_Dirty(di) );

   return mkexpr(datatag);
}


static
IRAtom* expr2tags_LDle_DC ( DCEnv* dce, IRType ty, IRAtom* addr, UInt bias )
{
   IRAtom *v64hi, *v64lo;
   //   IRDirty* di;
   //   IRTemp   datatag;

   switch (shadowType(ty)) {
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
         //         datatag = newIRTemp(dce->bb->tyenv, Ity_I32);
         //         di = unsafeIRDirty_1_N(datatag,
         //                                2,
         //                                "MC_(helperc_MERGE_TAGS)",
         //                                &MC_(helperc_MERGE_TAGS),
         //                                mkIRExprVec_2( v64lo, v64hi ));

         //         setHelperAnns_DC( dce, di );
         //         stmt( dce->bb, IRStmt_Dirty(di) );
         //         return mkexpr(datatag);

         // Clean call version:
         return mkIRExprCCall (Ity_I32,
                               2 /*Int regparms*/,
                               "MC_(helperc_MERGE_TAGS)",
                               &MC_(helperc_MERGE_TAGS),
                               mkIRExprVec_2( v64lo, v64hi ));
      default:
         VG_(tool_panic)("expr2tags_LDle_DC");
   }
}

static
IRAtom* expr2tags_Mux0X_DC ( DCEnv* dce,
                           IRAtom* cond, IRAtom* expr0, IRAtom* exprX )
{
   IRAtom *vbitsC, *vbits0, *vbitsX;
   IRDirty* di;
   IRTemp   datatag;

   tl_assert(isOriginalAtom_DC(dce, cond));
   tl_assert(isOriginalAtom_DC(dce, expr0));
   tl_assert(isOriginalAtom_DC(dce, exprX));

   // Generate a temp. 'datatag', which is the result of a NOP dirty
   // call on vbitsC, in order to 'anchor' any possible tag merge
   // clean helper calls in the expression which produced 'cond'.
   // This prevents the IR optimizer from deleting all of these
   // interactions from the parallel tag IR tree (or so we hope)
   vbitsC = expr2tags_DC(dce, cond);
   datatag = newIRTemp(dce->bb->tyenv, Ity_I32);
   di = unsafeIRDirty_1_N(datatag,
                          1,
                          "MC_(helperc_TAG_NOP)",
                          &MC_(helperc_TAG_NOP),
                          mkIRExprVec_1( vbitsC ));

   setHelperAnns_DC( dce, di );
   stmt( dce->bb, IRStmt_Dirty(di) );

   // Do the real work of generating tag IR trees for expr0 and exprX
   // and then making a parallel Mux which contains these two trees
   // with the ORIGINAL condition 'cond'
   vbits0 = expr2tags_DC(dce, expr0);
   vbitsX = expr2tags_DC(dce, exprX);
   tl_assert(sameKindedAtoms(vbits0, vbitsX)); // Both should be 32-bit tags

   return assignNew_DC(dce, Ity_I32, IRExpr_Mux0X(cond, vbits0, vbitsX));
}


// (Very similar to expr2tags_Mux0X_DC)
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
   datatag = newIRTemp(dce->bb->tyenv, Ity_I32);
   di = unsafeIRDirty_1_N(datatag,
                          1,
                          "MC_(helperc_TAG_NOP)",
                          &MC_(helperc_TAG_NOP),
                          mkIRExprVec_1( guardtag ));

   setHelperAnns_DC( dce, di );
   stmt( dce->bb, IRStmt_Dirty(di) );

   return mkexpr(datatag);
}


/* --------- This is the main expression-handling function. --------- */

IRExpr* expr2tags_DC ( DCEnv* dce, IRExpr* e )
{
   IRDirty* di;
   IRTemp   datatag;

   switch (e->tag) {

      case Iex_Get:
         return shadow_GET_DC( dce, e->Iex.Get.offset, e->Iex.Get.ty );

      case Iex_GetI:
         return shadow_GETI_DC( dce, e->Iex.GetI.descr,
                                e->Iex.GetI.ix, e->Iex.GetI.bias );

      case Iex_Tmp:
         return IRExpr_Tmp( findShadowTmp_DC(dce, e->Iex.Tmp.tmp) );

      case Iex_Const:
         // When you create a constant, assign it a new tag

         // Try it with a dirty call:
         datatag = newIRTemp(dce->bb->tyenv, Ity_I32);
         di = unsafeIRDirty_1_N( datatag,
                                 0/*regparms*/,
                                 "MC_(helperc_CREATE_TAG)",
                                 &MC_(helperc_CREATE_TAG),
                                 mkIRExprVec_0());
         setHelperAnns_DC( dce, di );
         stmt( dce->bb, IRStmt_Dirty(di) );

         return mkexpr(datatag);

      case Iex_Binop:
         return expr2tags_Binop_DC(
                   dce,
                   e->Iex.Binop.op,
                   e->Iex.Binop.arg1, e->Iex.Binop.arg2
                );

      case Iex_Unop:
         return expr2tags_Unop_DC( dce, e->Iex.Unop.op, e->Iex.Unop.arg );

      case Iex_LDle:
         return expr2tags_LDle_DC( dce, e->Iex.LDle.ty,
                                      e->Iex.LDle.addr, 0/*addr bias*/ );

      case Iex_CCall:
         return handleCCall_DC( dce,
                                e->Iex.CCall.args,
                                e->Iex.CCall.retty,
                                e->Iex.CCall.cee );

      case Iex_Mux0X:
         return expr2tags_Mux0X_DC( dce, e->Iex.Mux0X.cond, e->Iex.Mux0X.expr0,
                                    e->Iex.Mux0X.exprX);

      default:
         VG_(printf)("\n");
         ppIRExpr(e);
         VG_(printf)("\n");
         VG_(tool_panic)("dyncomp: expr2tags_DC");
   }
}

void do_shadow_STle_DC ( DCEnv* dce,
                      IRAtom* addr, UInt bias,
                      IRAtom* data, IRAtom* vdata )
{
   IROp     mkAdd;
   IRType   ty, tyAddr;
   IRDirty  *di, *diLo64, *diHi64;
   IRAtom   *addrAct, *addrLo64, *addrHi64;
   IRAtom   *vdataLo64, *vdataHi64;
   IRAtom   *eBias, *eBias0, *eBias8;
   void*    helper = NULL;
   Char*    hname = NULL;

   tyAddr = dce->hWordTy;
   mkAdd  = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
   tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );

   di = diLo64 = diHi64 = NULL;
   eBias = eBias0 = eBias8 = NULL;
   addrAct = addrLo64 = addrHi64 = NULL;
   vdataLo64 = vdataHi64 = NULL;

   if (data) {
      tl_assert(!vdata);
      tl_assert(isOriginalAtom_DC(dce, data));
      tl_assert(bias == 0);
      vdata = expr2tags_DC( dce, data );
   } else {
      tl_assert(vdata);
   }

   tl_assert(isOriginalAtom_DC(dce,addr));
   tl_assert(isShadowAtom_DC(dce,vdata));

   ty = typeOfIRExpr(dce->bb->tyenv, vdata);

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

      /* V128-bit case */
      /* See comment in next clause re 64-bit regparms */
      eBias0    = tyAddr==Ity_I32 ? mkU32(bias)   : mkU64(bias);
      addrLo64  = assignNew_DC(dce, tyAddr, binop(mkAdd, addr, eBias0) );
      vdataLo64 = assignNew_DC(dce, Ity_I64, unop(Iop_V128to64, vdata));
      diLo64    = unsafeIRDirty_0_N(
                     1/*regparms*/, hname, helper,
                     mkIRExprVec_2( addrLo64, vdataLo64 ));

      eBias8    = tyAddr==Ity_I32 ? mkU32(bias+8) : mkU64(bias+8);
      addrHi64  = assignNew_DC(dce, tyAddr, binop(mkAdd, addr, eBias8) );
      vdataHi64 = assignNew_DC(dce, Ity_I64, unop(Iop_V128HIto64, vdata));
      diHi64    = unsafeIRDirty_0_N(
                     1/*regparms*/, hname, helper,
                     mkIRExprVec_2( addrHi64, vdataHi64 ));

      setHelperAnns_DC( dce, diLo64 );
      setHelperAnns_DC( dce, diHi64 );
      stmt( dce->bb, IRStmt_Dirty(diLo64) );
      stmt( dce->bb, IRStmt_Dirty(diHi64) );

   } else {

      /* 8/16/32/64-bit cases */
      /* Generate the actual address into addrAct. */
      if (bias == 0) {
         addrAct = addr;
      } else {
         eBias   = tyAddr==Ity_I32 ? mkU32(bias) : mkU64(bias);
         addrAct = assignNew_DC(dce, tyAddr, binop(mkAdd, addr, eBias) );
      }

      // All of this zwidenToHostWord_DC stuff doesn't matter for tags
      // since all tags are 32-bits
      di = unsafeIRDirty_0_N(2/*regparms*/, hname, helper,
                             mkIRExprVec_2( addrAct, vdata ));

      //      if (ty == Ity_I64) {
      //         /* We can't do this with regparm 2 on 32-bit platforms, since
      //            the back ends aren't clever enough to handle 64-bit
      //            regparm args.  Therefore be different. */
      //         di = unsafeIRDirty_0_N(
      //                 1/*regparms*/, hname, helper,
      //                 mkIRExprVec_2( addrAct, vdata ));
      //      } else {
      //         di = unsafeIRDirty_0_N(
      //                 2/*regparms*/, hname, helper,
      //                 mkIRExprVec_2( addrAct,
      //                                zwidenToHostWord_DC( dce, vdata )));
      //      }
      setHelperAnns_DC( dce, di );
      stmt( dce->bb, IRStmt_Dirty(di) );
   }

}
