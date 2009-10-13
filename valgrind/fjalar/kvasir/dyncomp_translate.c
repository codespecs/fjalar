
/*--------------------------------------------------------------------*/
/*--- Instrument IR to perform tag operations for DynComp.         ---*/
/*--- (Analogous to mc_translate.c for MemCheck)                   ---*/
/*---                                          dyncomp_translate.c ---*/
/*--------------------------------------------------------------------*/

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2009 Julian
  Seward, jseward@acm.org)

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

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
#include "dyncomp_translate.h"
#include "dyncomp_main.h"
#include "../fjalar_include.h"
#include "kvasir_main.h"
#include "vex_common.h"

#include "my_libc.h"

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
   di->fxState[1].fx     = Ifx_Read;
   di->fxState[1].offset = dce->layout->offset_IP;
   di->fxState[1].size   = dce->layout->sizeof_IP;
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
   void*    helper = NULL;
   Char*    hname = NULL;

   /* Silence unused variables. (These are kept around as opposed to
      being removed to keep dyncomp_translate.c analogues of
      mc_translate.c functions as similar as possible */
   (void)expd_eq_old; (void)boldLo; (void)bdataLo; (void)bexpdLo;

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
   // if (dce->tmpMap[orig] == IRTemp_INVALID) {

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
   void*    helper = NULL;
   Char*    hname = NULL;

   /* Silence unused variables. (These are kept around as opposed to
      being removed to keep dyncomp_translate.c analogues of
      mc_translate.c functions as similar as possible */
   (void)expd_eq_old;(void)boldLo;(void)boldHi;
   (void)bexpdLo;(void)bexpdHi;(void)bdataLo;(void)bdataHi;
   (void)xHL;(void)xHi;(void)xLo;


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
void do_shadow_CAS_DC( DCEnv* dce, IRCAS* cas) {

  if (cas->oldHi == IRTemp_INVALID) {
    do_shadow_CAS_single_DC( dce, cas );
  } else {
    do_shadow_CAS_double_DC( dce, cas );
  }

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
   stmt_DC('V',  dce,
         IRStmt_Put( (4 * offset) + (3 * dce->layout->total_sizeB), vatom ) );
}

// A PUTI stores a value (dynamically indexed) into the guest state
// (for x86, this seems to be only used for floating point values)
void do_shadow_PUTI_DC ( DCEnv* dce,
                      IRRegArray* descr, IRAtom* ix, Int bias, IRAtom* atom )
{
   IRAtom* vatom;
   IRType  ty;
   IRRegArray *new_descr;

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

   stmt_DC( 'V', dce, IRStmt_PutI( new_descr, ix, bias, vatom ));
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
   /* XXX This won't do the right thing if your code uses %ebp for
      some purpose other than the frame pointer. Let's hope that
      doesn't happen too often in unoptimized code. The only better
      solution would be to track with an independent bit which values
      are ESP-derived, which would be a pain. -SMcC */
   if (offset == dce->layout->offset_SP || offset == dce->layout->offset_FP) {
      return IRExpr_Const(IRConst_UWord(WEAK_FRESH_TAG));
   }

   // The floating-point stack on the x86 is located between offsets
   // 64 and 128 so we don't want somebody requesting a GET into this
   // region since our (4 * offset) trick won't work properly here.
   // This should (hopefully) never happen since floating-point
   // accesses are always done using GETI's.
   tl_assert(!(((UInt)offset >= offsetof(VexGuestArchState, guest_FPREG)) &&
	       ((UInt)offset <  offsetof(VexGuestArchState, guest_FPREG)
		+ 8 * sizeof(ULong))));

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
            if (0) VG_(printf)("excluding %s(%d)\n", cee->name, i);
         } else {
            /* merge the tags of first and current arguments */
            cur = expr2tags_DC(dce, exprvec[i]);

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
      case Iop_MAddF64r32:
      case Iop_MSubF64:
      case Iop_MSubF64r32:

         // from libvex_ir.h:
      /* :: IRRoundingMode(I32) x F64 x F64 x F64 -> F64
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
      /* I32(rm) x F64 x F64 -> F64 */

      case Iop_AddF64:
      case Iop_AddF64r32:
      case Iop_SubF64:
      case Iop_SubF64r32:

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

      case Iop_MulF64:
      case Iop_MulF64r32:
      case Iop_DivF64:
      case Iop_DivF64r32:

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

      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2tags_Triop");
   }

   return IRExpr_Const(IRConst_UWord(0));
}


// pgbovine TODO: Update with new opcodes for Valgrind 3.1.0
//                Look at expr2vbits_Binop() from ../mc_translate.c:
static
IRAtom* expr2tags_Binop_DC ( DCEnv* dce,
                              IROp op,
                              IRAtom* atom1, IRAtom* atom2 )
{
   IRAtom* vatom1 = expr2tags_DC( dce, atom1 );
   IRAtom* vatom2 = expr2tags_DC( dce, atom2 );

   void*    helper = 0;
   Char*    hname = 0;

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
   case Iop_Add8:  case Iop_Add16:  case Iop_Add32:  case Iop_Add64:
   case Iop_Sub8:  case Iop_Sub16:  case Iop_Sub32:  case Iop_Sub64:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

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

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* ------ Floating point.  We try and be IEEE754 compliant. ------ */

      /* Binary operations mandated by IEEE754. */
   case Iop_AddF64: case Iop_SubF64:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

   case Iop_MulF64: case Iop_DivF64: /* Iop_RemF64, */

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

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* ------------------ 64-bit SIMD Integer. ------------------ */

      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x8:   case Iop_Add16x4:   case Iop_Add32x2:
   case Iop_QAdd8Ux8: case Iop_QAdd16Ux4:
   case Iop_QAdd8Sx8: case Iop_QAdd16Sx4:

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x8:   case Iop_Sub16x4:   case Iop_Sub32x2:
   case Iop_QSub8Ux8: case Iop_QSub16Ux4:
   case Iop_QSub8Sx8: case Iop_QSub16Sx4:

      /* AVERAGING: note: (arg1 + arg2 + 1) >>u 1 */
   case Iop_Avg8Ux8:
   case Iop_Avg16Ux4:

      /* MIN/MAX */
   case Iop_Max16Sx4:
   case Iop_Max8Ux8:
   case Iop_Min16Sx4:
   case Iop_Min8Ux8:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* MULTIPLICATION (normal / high half of signed/unsigned) */
   case Iop_Mul16x4:
   case Iop_MulHi16Ux4:
   case Iop_MulHi16Sx4:

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;


      /* ------------------ 128-bit SIMD FP. ------------------ */

      /* --- 32x4 vector FP --- */

   case Iop_Add32Fx4: case Iop_Sub32Fx4:
   case Iop_Max32Fx4: case Iop_Min32Fx4:

      /* --- 32x4 lowest-lane-only scalar FP --- */

   case Iop_Add32F0x4: case Iop_Sub32F0x4:
   case Iop_Max32F0x4: case Iop_Min32F0x4:

      /* --- 64x2 vector FP --- */

   case Iop_Add64Fx2: case Iop_Sub64Fx2:
   case Iop_Max64Fx2: case Iop_Min64Fx2:

      /* --- 64x2 lowest-lane-only scalar FP --- */

   case Iop_Add64F0x2: case Iop_Sub64F0x2:
   case Iop_Max64F0x2: case Iop_Min64F0x2:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* --- 32x4 vector FP --- */
   case Iop_Mul32Fx4: case Iop_Div32Fx4:
      /* --- 32x4 lowest-lane-only scalar FP --- */
   case Iop_Mul32F0x4: case Iop_Div32F0x4:
      /* --- 64x2 vector FP --- */
   case Iop_Mul64Fx2: case Iop_Div64Fx2:
      /* --- 64x2 lowest-lane-only scalar FP --- */
   case Iop_Mul64F0x2: case Iop_Div64F0x2:

      if (!dyncomp_dataflow_comparisons_mode && !dyncomp_units_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;


      /* ------------------ 128-bit SIMD Integer. ------------------ */

      /* ADDITION (normal / unsigned sat / signed sat) */
   case Iop_Add8x16:   case Iop_Add16x8:   case Iop_Add32x4:  case Iop_Add64x2:
   case Iop_QAdd8Ux16: case Iop_QAdd16Ux8:
   case Iop_QAdd8Sx16: case Iop_QAdd16Sx8:

      /* SUBTRACTION (normal / unsigned sat / signed sat) */
   case Iop_Sub8x16:   case Iop_Sub16x8:   case Iop_Sub32x4:  case Iop_Sub64x2:
   case Iop_QSub8Ux16: case Iop_QSub16Ux8:
   case Iop_QSub8Sx16: case Iop_QSub16Sx8:

      /* MIN/MAX */
   case Iop_Max16Sx8:
   case Iop_Max8Ux16:
   case Iop_Min16Sx8:
   case Iop_Min8Ux16:

      /* AVERAGING: note: (arg1 + arg2 + 1) >>u 1 */
   case Iop_Avg8Ux16:
   case Iop_Avg16Ux8:

      if (!dyncomp_dataflow_comparisons_mode) {
         helper = &MC_(helperc_MERGE_TAGS);
         hname = "MC_(helperc_MERGE_TAGS)";
      }
      break;

      /* BITWISE OPS */
   case Iop_AndV128: case Iop_OrV128: case Iop_XorV128:

      /* MULTIPLICATION (normal / high half of signed/unsigned) */
   case Iop_Mul16x8:
   case Iop_MulHi16Ux8:
   case Iop_MulHi16Sx8:

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
   case Iop_CmpEQ8:  case Iop_CmpEQ16:  case Iop_CmpEQ32:  case Iop_CmpEQ64:
   case Iop_CmpNE8:  case Iop_CmpNE16:  case Iop_CmpNE32:  case Iop_CmpNE64:
   case Iop_CmpLT32S:  case Iop_CmpLT64S:
   case Iop_CmpLE32S:  case Iop_CmpLE64S:
   case Iop_CmpLT32U:  case Iop_CmpLT64U:
   case Iop_CmpLE32U:  case Iop_CmpLE64U:

     // New CAS operations. They're semantically identical to normal comparisons
     // They're used by memcheck to differentiate the compares done by a CAS and
     // a normal compare.
   case Iop_CasCmpEQ8:  case Iop_CasCmpNE8:
   case Iop_CasCmpEQ16: case Iop_CasCmpNE16:
   case Iop_CasCmpEQ32: case Iop_CasCmpNE32:
   case Iop_CasCmpEQ64: case Iop_CasCmpNE64:

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

      helper = &MC_(helperc_MERGE_TAGS_RETURN_0);
      hname = "MC_(helperc_MERGE_TAGS_RETURN_0)";
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
   case Iop_F64toI16:  /* IRRoundingMode(I32) x F64 -> I16 */
   case Iop_F64toI32:  /* IRRoundingMode(I32) x F64 -> I32 */
   case Iop_F64toI64:  /* IRRoundingMode(I32) x F64 -> I64 */
   case Iop_I64toF64:  /* IRRoundingMode(I32) x I64 -> F64 */
   case Iop_F64toF32:  /* IRRoundingMode(I32) x F64 -> F32 */

   case Iop_RoundF64toInt:
   case Iop_RoundF64toF32:
   case Iop_SinF64:
   case Iop_CosF64:
   case Iop_TanF64:
   case Iop_2xm1F64:
   case Iop_SqrtF64:

      /* F64 -> F64, also takes an I32 first argument encoding the
         rounding mode. */
      //   case Iop_RoundF64: // pgbovine - not in Valgrind 3.1.0

      if (!dyncomp_dataflow_comparisons_mode) {
         return vatom2;
      }
      break;


      // ------------------------
      // Return a fresh tag of 0:
      // ------------------------

      // Random bogus stuff do not qualify as interactions

   case Iop_PRemC3210F64:  /* C3210 flags resulting from FPREM, :: I32 */
   case Iop_PRem1C3210F64: /* C3210 flags resulting from FPREM1, :: I32 */

      break;


      // Hopefully we will never get here if we've had had cases which
      // handle every possible IR binary op. type (right?)
      // pgbovine TODO: Look at expr2vbits_Binop() from ../mc_translate.c
      //                and make sure we've covered all possible cases.
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
   // pgbovine TODO: Actually, when you widen stuff, don't you want to
   //       create new tags for the new bytes and merge them?
   //       But you can't do that because you only have the word-sized
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
   vbits0 = expr2tags_DC(dce, expr0);
   vbitsX = expr2tags_DC(dce, exprX);
   tl_assert(sameKindedAtoms(vbits0, vbitsX));// Both should be word-sized tags

   return assignNew_DC(dce, Ity_Word, IRExpr_Mux0X(cond, vbits0, vbitsX));
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
   //   VG_(printf)("\n");

   switch (e->tag) {

      case Iex_Get:
         return shadow_GET_DC( dce, e->Iex.Get.offset, e->Iex.Get.ty );

      case Iex_GetI:
         return shadow_GETI_DC( dce, e->Iex.GetI.descr,
                                e->Iex.GetI.ix, e->Iex.GetI.bias );

      case Iex_RdTmp:
         return IRExpr_RdTmp( findShadowTmp_DC(dce, e->Iex.RdTmp.tmp) );

      case Iex_Const:

         // Fast mode implementation - create a special reserved
         // WEAKE_FRESH_TAG tag one tag for each static instance of a
         // program literal:
         if (dyncomp_fast_mode) {
	    return IRExpr_Const(IRConst_UWord(WEAK_FRESH_TAG));
         }
         else {
	    static Int static_fresh_count = 0;

            //            VG_(printf)("******PREV CONST******\n");

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
                   e->Iex.Qop.op,
                   e->Iex.Qop.arg1, e->Iex.Qop.arg2,
		   e->Iex.Qop.arg3, e->Iex.Qop.arg4
                );

      case Iex_Triop:
         return expr2tags_Triop_DC(
                   dce,
                   e->Iex.Triop.op,
                   e->Iex.Triop.arg1, e->Iex.Triop.arg2, e->Iex.Triop.arg3
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
   IRAtom   *vdataLo64, *vdataHi64;
   IRAtom   *vaddr;
   IRTemp   addrTag;
   void*    helper = NULL;
   Char*    hname = NULL;
   Int      pcOffset = -1;

   tyAddr = dce->hWordTy;
   mkAdd  = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
   tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );

   di = diLo64 = diHi64 = NULL;
   addrHi64 = NULL;
   vdataLo64 = vdataHi64 = NULL;

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
