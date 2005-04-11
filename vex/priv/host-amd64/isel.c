
/*---------------------------------------------------------------*/
/*---                                                         ---*/
/*--- This file (host-amd64/isel.c) is                        ---*/
/*--- Copyright (c) OpenWorks LLP.  All rights reserved.      ---*/
/*---                                                         ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of LibVEX, a library for dynamic binary
   instrumentation and translation.

   Copyright (C) 2004-2005 OpenWorks LLP.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; Version 2 dated June 1991 of the
   license.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE, or liability
   for damages.  See the GNU General Public License for more details.

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
   USA.
*/

#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"

#include "ir/irmatch.h"
#include "main/vex_util.h"
#include "main/vex_globals.h"
#include "host-generic/h_generic_regs.h"
//.. #include "host-generic/h_generic_simd64.h"
#include "host-amd64/hdefs.h"


/*---------------------------------------------------------*/
/*--- x87/SSE control word stuff                        ---*/
/*---------------------------------------------------------*/

/* Vex-generated code expects to run with the FPU set as follows: all
   exceptions masked, round-to-nearest, precision = 53 bits.  This
   corresponds to a FPU control word value of 0x027F.

   Similarly the SSE control word (%mxcsr) should be 0x1F80.

   %fpucw and %mxcsr should have these values on entry to
   Vex-generated code, and should those values should be
   unchanged at exit.
*/

#define DEFAULT_FPUCW 0x027F

#define DEFAULT_MXCSR 0x1F80

/* debugging only, do not use */
/* define DEFAULT_FPUCW 0x037F */


/*---------------------------------------------------------*/
/*--- misc helpers                                      ---*/
/*---------------------------------------------------------*/

/* These are duplicated in guest-amd64/toIR.c */
static IRExpr* unop ( IROp op, IRExpr* a )
{
   return IRExpr_Unop(op, a);
}

static IRExpr* binop ( IROp op, IRExpr* a1, IRExpr* a2 )
{
   return IRExpr_Binop(op, a1, a2);
}

//.. static IRExpr* mkU64 ( ULong i )
//.. {
//..    return IRExpr_Const(IRConst_U64(i));
//.. }
//.. 
//.. static IRExpr* mkU32 ( UInt i )
//.. {
//..    return IRExpr_Const(IRConst_U32(i));
//.. }

static IRExpr* bind ( Int binder )
{
   return IRExpr_Binder(binder);
}


/*---------------------------------------------------------*/
/*--- ISelEnv                                           ---*/
/*---------------------------------------------------------*/

/* This carries around:

   - A mapping from IRTemp to IRType, giving the type of any IRTemp we
     might encounter.  This is computed before insn selection starts,
     and does not change.

   - A mapping from IRTemp to HReg.  This tells the insn selector
     which virtual register is associated with each IRTemp
     temporary.  This is computed before insn selection starts, and
     does not change.  We expect this mapping to map precisely the
     same set of IRTemps as the type mapping does.

        - vregmap   holds the primary register for the IRTemp.
        - vregmapHI is only used for 128-bit integer-typed
             IRTemps.  It holds the identity of a second
             64-bit virtual HReg, which holds the high half
             of the value.

   - The code array, that is, the insns selected so far.

   - A counter, for generating new virtual registers.

   - The host subarchitecture we are selecting insns for.  
     This is set at the start and does not change.

   Note, this is all host-independent.  (JRS 20050201: well, kinda
   ... not completely.  Compare with ISelEnv for X86.)
*/

typedef
   struct {
      IRTypeEnv*   type_env;

      HReg*        vregmap;
      HReg*        vregmapHI;
      Int          n_vregmap;

      HInstrArray* code;

      Int          vreg_ctr;

      VexSubArch   subarch;
   }
   ISelEnv;


static HReg lookupIRTemp ( ISelEnv* env, IRTemp tmp )
{
   vassert(tmp >= 0);
   vassert(tmp < env->n_vregmap);
   return env->vregmap[tmp];
}

static void lookupIRTemp128 ( HReg* vrHI, HReg* vrLO, 
                              ISelEnv* env, IRTemp tmp )
{
   vassert(tmp >= 0);
   vassert(tmp < env->n_vregmap);
   vassert(env->vregmapHI[tmp] != INVALID_HREG);
   *vrLO = env->vregmap[tmp];
   *vrHI = env->vregmapHI[tmp];
}

static void addInstr ( ISelEnv* env, AMD64Instr* instr )
{
   addHInstr(env->code, instr);
   if (vex_traceflags & VEX_TRACE_VCODE) {
      ppAMD64Instr(instr);
      vex_printf("\n");
   }
}

static HReg newVRegI ( ISelEnv* env )
{
   HReg reg = mkHReg(env->vreg_ctr, HRcInt64, True/*virtual reg*/);
   env->vreg_ctr++;
   return reg;
}

//.. static HReg newVRegF ( ISelEnv* env )
//.. {
//..    HReg reg = mkHReg(env->vreg_ctr, HRcFlt64, True/*virtual reg*/);
//..    env->vreg_ctr++;
//..    return reg;
//.. }

static HReg newVRegV ( ISelEnv* env )
{
   HReg reg = mkHReg(env->vreg_ctr, HRcVec128, True/*virtual reg*/);
   env->vreg_ctr++;
   return reg;
}


/*---------------------------------------------------------*/
/*--- ISEL: Forward declarations                        ---*/
/*---------------------------------------------------------*/

/* These are organised as iselXXX and iselXXX_wrk pairs.  The
   iselXXX_wrk do the real work, but are not to be called directly.
   For each XXX, iselXXX calls its iselXXX_wrk counterpart, then
   checks that all returned registers are virtual.  You should not
   call the _wrk version directly.
*/
static AMD64RMI*     iselIntExpr_RMI_wrk ( ISelEnv* env, IRExpr* e );
static AMD64RMI*     iselIntExpr_RMI     ( ISelEnv* env, IRExpr* e );

static AMD64RI*      iselIntExpr_RI_wrk  ( ISelEnv* env, IRExpr* e );
static AMD64RI*      iselIntExpr_RI      ( ISelEnv* env, IRExpr* e );

static AMD64RM*      iselIntExpr_RM_wrk  ( ISelEnv* env, IRExpr* e );
static AMD64RM*      iselIntExpr_RM      ( ISelEnv* env, IRExpr* e );

static HReg          iselIntExpr_R_wrk   ( ISelEnv* env, IRExpr* e );
static HReg          iselIntExpr_R       ( ISelEnv* env, IRExpr* e );

static AMD64AMode*   iselIntExpr_AMode_wrk ( ISelEnv* env, IRExpr* e );
static AMD64AMode*   iselIntExpr_AMode     ( ISelEnv* env, IRExpr* e );

static void          iselInt128Expr_wrk ( HReg* rHi, HReg* rLo, 
                                          ISelEnv* env, IRExpr* e );
static void          iselInt128Expr     ( HReg* rHi, HReg* rLo, 
                                          ISelEnv* env, IRExpr* e );

static AMD64CondCode iselCondCode_wrk    ( ISelEnv* env, IRExpr* e );
static AMD64CondCode iselCondCode        ( ISelEnv* env, IRExpr* e );

static HReg          iselDblExpr_wrk     ( ISelEnv* env, IRExpr* e );
static HReg          iselDblExpr         ( ISelEnv* env, IRExpr* e );

static HReg          iselFltExpr_wrk     ( ISelEnv* env, IRExpr* e );
static HReg          iselFltExpr         ( ISelEnv* env, IRExpr* e );

static HReg          iselVecExpr_wrk     ( ISelEnv* env, IRExpr* e );
static HReg          iselVecExpr         ( ISelEnv* env, IRExpr* e );


/*---------------------------------------------------------*/
/*--- ISEL: Misc helpers                                ---*/
/*---------------------------------------------------------*/

static Bool sane_AMode ( AMD64AMode* am )
{
   switch (am->tag) {
      case Aam_IR:
         return 
            toBool( hregClass(am->Aam.IR.reg) == HRcInt64
                    && (hregIsVirtual(am->Aam.IR.reg)
                        || am->Aam.IR.reg == hregAMD64_RBP()) );
      case Aam_IRRS:
         return 
            toBool( hregClass(am->Aam.IRRS.base) == HRcInt64
                    && hregIsVirtual(am->Aam.IRRS.base)
                    && hregClass(am->Aam.IRRS.index) == HRcInt64
                    && hregIsVirtual(am->Aam.IRRS.index) );
      default:
        vpanic("sane_AMode: unknown amd64 amode tag");
   }
}


/* Can the lower 32 bits be signedly widened to produce the whole
   64-bit value?  In other words, are the top 33 bits either all 0 or
   all 1 ? */
static Bool fitsIn32Bits ( ULong x )
{
   Long y0 = (Long)x;
   Long y1 = y0;
   y1 <<= 32;
   y1 >>=/*s*/ 32;
   return toBool(x == y1);
}

//.. /* Is this a 32-bit zero expression? */
//.. 
//.. static Bool isZero32 ( IRExpr* e )
//.. {
//..    return e->tag == Iex_Const
//..           && e->Iex.Const.con->tag == Ico_U32
//..           && e->Iex.Const.con->Ico.U32 == 0;
//.. }

/* Make a int reg-reg move. */

static AMD64Instr* mk_iMOVsd_RR ( HReg src, HReg dst )
{
   vassert(hregClass(src) == HRcInt64);
   vassert(hregClass(dst) == HRcInt64);
   return AMD64Instr_Alu64R(Aalu_MOV, AMD64RMI_Reg(src), dst);
}

/* Make a vector reg-reg move. */

static AMD64Instr* mk_vMOVsd_RR ( HReg src, HReg dst )
{
   vassert(hregClass(src) == HRcVec128);
   vassert(hregClass(dst) == HRcVec128);
   return AMD64Instr_SseReRg(Asse_MOV, src, dst);
}

/* Advance/retreat %rsp by n. */

static void add_to_rsp ( ISelEnv* env, Int n )
{
   vassert(n > 0 && n < 256 && (n%8) == 0);
   addInstr(env, 
            AMD64Instr_Alu64R(Aalu_ADD, AMD64RMI_Imm(n), 
                                        hregAMD64_RSP()));
}

static void sub_from_rsp ( ISelEnv* env, Int n )
{
   vassert(n > 0 && n < 256 && (n%8) == 0);
   addInstr(env, 
            AMD64Instr_Alu64R(Aalu_SUB, AMD64RMI_Imm(n), 
                                        hregAMD64_RSP()));
}


//.. /* Given an amode, return one which references 4 bytes further
//..    along. */
//.. 
//.. static X86AMode* advance4 ( X86AMode* am )
//.. {
//..    X86AMode* am4 = dopyX86AMode(am);
//..    switch (am4->tag) {
//..       case Xam_IRRS:
//..          am4->Xam.IRRS.imm += 4; break;
//..       case Xam_IR:
//..          am4->Xam.IR.imm += 4; break;
//..       default:
//..          vpanic("advance4(x86,host)");
//..    }
//..    return am4;
//.. }
//.. 
//.. 
//.. /* Push an arg onto the host stack, in preparation for a call to a
//..    helper function of some kind.  Returns the number of 32-bit words
//..    pushed. */
//.. 
//.. static Int pushArg ( ISelEnv* env, IRExpr* arg )
//.. {
//..    IRType arg_ty = typeOfIRExpr(env->type_env, arg);
//..    if (arg_ty == Ity_I32) {
//..       addInstr(env, X86Instr_Push(iselIntExpr_RMI(env, arg)));
//..       return 1;
//..    } else 
//..    if (arg_ty == Ity_I64) {
//..       HReg rHi, rLo;
//..       iselInt64Expr(&rHi, &rLo, env, arg);
//..       addInstr(env, X86Instr_Push(X86RMI_Reg(rHi)));
//..       addInstr(env, X86Instr_Push(X86RMI_Reg(rLo)));
//..       return 2;
//..    }
//..    ppIRExpr(arg);
//..    vpanic("pushArg(x86): can't handle arg of this type");
//.. }


/* Used only in doHelperCall.  See big comment in doHelperCall re
   handling of register-parameter args.  This function figures out
   whether evaluation of an expression might require use of a fixed
   register.  If in doubt return True (safe but suboptimal).
*/
static
Bool mightRequireFixedRegs ( IRExpr* e )
{
   switch (e->tag) {
      case Iex_Tmp: case Iex_Const: case Iex_Get: 
         return False;
      default:
         return True;
   }
}


/* Do a complete function call.  guard is a Ity_Bit expression
   indicating whether or not the call happens.  If guard==NULL, the
   call is unconditional. */

static
void doHelperCall ( ISelEnv* env, 
                    Bool passBBP, 
                    IRExpr* guard, IRCallee* cee, IRExpr** args )
{
   AMD64CondCode cc;
   HReg          argregs[6];
   HReg          tmpregs[6];
   Bool          go_fast;
   Int           n_args, i, argreg;

   /* Marshal args for a call and do the call.

      If passBBP is True, %rbp (the baseblock pointer) is to be passed
      as the first arg.

      This function only deals with a tiny set of possibilities, which
      cover all helpers in practice.  The restrictions are that only
      arguments in registers are supported, hence only 6x64 integer
      bits in total can be passed.  In fact the only supported arg
      type is I64.

      Generating code which is both efficient and correct when
      parameters are to be passed in registers is difficult, for the
      reasons elaborated in detail in comments attached to
      doHelperCall() in priv/host-x86/isel.c.  Here, we use a variant
      of the method described in those comments.

      The problem is split into two cases: the fast scheme and the
      slow scheme.  In the fast scheme, arguments are computed
      directly into the target (real) registers.  This is only safe
      when we can be sure that computation of each argument will not
      trash any real registers set by computation of any other
      argument.

      In the slow scheme, all args are first computed into vregs, and
      once they are all done, they are moved to the relevant real
      regs.  This always gives correct code, but it also gives a bunch
      of vreg-to-rreg moves which are usually redundant but are hard
      for the register allocator to get rid of.

      To decide which scheme to use, all argument expressions are
      first examined.  If they are all so simple that it is clear they
      will be evaluated without use of any fixed registers, use the
      fast scheme, else use the slow scheme.  Note also that only
      unconditional calls may use the fast scheme, since having to
      compute a condition expression could itself trash real
      registers.

      Note this requires being able to examine an expression and
      determine whether or not evaluation of it might use a fixed
      register.  That requires knowledge of how the rest of this insn
      selector works.  Currently just the following 3 are regarded as
      safe -- hopefully they cover the majority of arguments in
      practice: IRExpr_Tmp IRExpr_Const IRExpr_Get.
   */

   /* Note that the cee->regparms field is meaningless on AMD64 host
      (since there is only one calling convention) and so we always
      ignore it. */

   n_args = 0;
   for (i = 0; args[i]; i++)
      n_args++;

   if (6 < n_args + (passBBP ? 1 : 0))
      vpanic("doHelperCall(AMD64): cannot currently handle > 6 args");

   argregs[0] = hregAMD64_RDI();
   argregs[1] = hregAMD64_RSI();
   argregs[2] = hregAMD64_RDX();
   argregs[3] = hregAMD64_RCX();
   argregs[4] = hregAMD64_R8();
   argregs[5] = hregAMD64_R9();

   tmpregs[0] = tmpregs[1] = tmpregs[2] =
   tmpregs[3] = tmpregs[4] = tmpregs[5] = INVALID_HREG;

   /* First decide which scheme (slow or fast) is to be used.  First
      assume the fast scheme, and select slow if any contraindications
      (wow) appear. */

   go_fast = True;

   if (guard) {
      if (guard->tag == Iex_Const 
          && guard->Iex.Const.con->tag == Ico_U1
          && guard->Iex.Const.con->Ico.U1 == True) {
         /* unconditional */
      } else {
         /* Not manifestly unconditional -- be conservative. */
         go_fast = False;
      }
   }

   if (go_fast) {
      for (i = 0; i < n_args; i++) {
         if (mightRequireFixedRegs(args[i])) {
            go_fast = False;
            break;
         }
      }
   }

   /* At this point the scheme to use has been established.  Generate
      code to get the arg values into the argument rregs. */

   if (go_fast) {

      /* FAST SCHEME */
      argreg = 0;
      if (passBBP) {
         addInstr(env, mk_iMOVsd_RR( hregAMD64_RBP(), argregs[argreg]));
         argreg++;
      }

      for (i = 0; i < n_args; i++) {
         vassert(argreg < 6);
         vassert(typeOfIRExpr(env->type_env, args[i]) == Ity_I64);
         addInstr(env, AMD64Instr_Alu64R(
                          Aalu_MOV, 
                          iselIntExpr_RMI(env, args[i]),
                          argregs[argreg]
                       )
                 );
         argreg++;
      }

      /* Fast scheme only applies for unconditional calls.  Hence: */
      cc = Acc_ALWAYS;

   } else {

      /* SLOW SCHEME; move via temporaries */
      argreg = 0;

      if (passBBP) {
         /* This is pretty stupid; better to move directly to rdi
            after the rest of the args are done. */
         tmpregs[argreg] = newVRegI(env);
         addInstr(env, mk_iMOVsd_RR( hregAMD64_RBP(), tmpregs[argreg]));
         argreg++;
      }

      for (i = 0; i < n_args; i++) {
         vassert(argreg < 6);
         vassert(typeOfIRExpr(env->type_env, args[i]) == Ity_I64);
         tmpregs[argreg] = iselIntExpr_R(env, args[i]);
         argreg++;
      }

      /* Now we can compute the condition.  We can't do it earlier
         because the argument computations could trash the condition
         codes.  Be a bit clever to handle the common case where the
         guard is 1:Bit. */
      cc = Acc_ALWAYS;
      if (guard) {
         if (guard->tag == Iex_Const 
             && guard->Iex.Const.con->tag == Ico_U1
             && guard->Iex.Const.con->Ico.U1 == True) {
            /* unconditional -- do nothing */
         } else {
            cc = iselCondCode( env, guard );
         }
      }

      /* Move the args to their final destinations. */
      for (i = 0; i < argreg; i++) {
         /* None of these insns, including any spill code that might
            be generated, may alter the condition codes. */
         addInstr( env, mk_iMOVsd_RR( tmpregs[i], argregs[i] ) );
      }

   }

   /* Finally, the call itself. */
   addInstr(env, AMD64Instr_Call( 
                    cc, 
                    Ptr_to_ULong(cee->addr), 
                    n_args + (passBBP ? 1 : 0) 
                 )
   );
}


/* Given a guest-state array descriptor, an index expression and a
   bias, generate an AMD64AMode holding the relevant guest state
   offset. */

static
AMD64AMode* genGuestArrayOffset ( ISelEnv* env, IRArray* descr, 
                                  IRExpr* off, Int bias )
{
   HReg tmp, roff;
   Int  elemSz = sizeofIRType(descr->elemTy);
   Int  nElems = descr->nElems;

   /* Throw out any cases not generated by an amd64 front end.  In
      theory there might be a day where we need to handle them -- if
      we ever run non-amd64-guest on amd64 host. */

   if (nElems != 8 || (elemSz != 1 && elemSz != 8))
      vpanic("genGuestArrayOffset(amd64 host)");

   /* Compute off into a reg, %off.  Then return:

         movq %off, %tmp
         addq $bias, %tmp  (if bias != 0)
         andq %tmp, 7
         ... base(%rbp, %tmp, shift) ...
   */
   tmp  = newVRegI(env);
   roff = iselIntExpr_R(env, off);
   addInstr(env, mk_iMOVsd_RR(roff, tmp));
   if (bias != 0) {
      /* Make sure the bias is sane, in the sense that there are
         no significant bits above bit 30 in it. */
      vassert(-10000 < bias && bias < 10000);
      addInstr(env, 
               AMD64Instr_Alu64R(Aalu_ADD, AMD64RMI_Imm(bias), tmp));
   }
   addInstr(env, 
            AMD64Instr_Alu64R(Aalu_AND, AMD64RMI_Imm(7), tmp));
   vassert(elemSz == 1 || elemSz == 8);
   return
      AMD64AMode_IRRS( descr->base, hregAMD64_RBP(), tmp,
                                    elemSz==8 ? 3 : 0);
}


/* Set the SSE unit's rounding mode to default (%mxcsr = 0x1F80) */
static
void set_SSE_rounding_default ( ISelEnv* env )
{
   /* pushq $DEFAULT_MXCSR 
      ldmxcsr 0(%rsp)
      addq $8, %rsp
   */
   AMD64AMode* zero_rsp = AMD64AMode_IR(0, hregAMD64_RSP());
   addInstr(env, AMD64Instr_Push(AMD64RMI_Imm(DEFAULT_MXCSR)));
   addInstr(env, AMD64Instr_LdMXCSR(zero_rsp));
   add_to_rsp(env, 8);
}

//.. /* Mess with the FPU's rounding mode: set to the default rounding mode
//..    (DEFAULT_FPUCW). */
//.. static 
//.. void set_FPU_rounding_default ( ISelEnv* env )
//.. {
//..    /* pushl $DEFAULT_FPUCW
//..       fldcw 0(%esp)
//..       addl $4, %esp 
//..    */
//..    X86AMode* zero_esp = X86AMode_IR(0, hregX86_ESP());
//..    addInstr(env, X86Instr_Push(X86RMI_Imm(DEFAULT_FPUCW)));
//..    addInstr(env, X86Instr_FpLdStCW(True/*load*/, zero_esp));
//..    add_to_esp(env, 4);
//.. }


/* Mess with the SSE unit's rounding mode: 'mode' is an I32-typed
   expression denoting a value in the range 0 .. 3, indicating a round
   mode encoded as per type IRRoundingMode.  Set the SSE machinery to
   have the same rounding.
*/
static
void set_SSE_rounding_mode ( ISelEnv* env, IRExpr* mode )
{
   /* Note: this sequence only makes sense because DEFAULT_MXCSR has
      both rounding bits == 0.  If that wasn't the case, we couldn't
      create a new rounding field simply by ORing the new value into
      place. */

   /* movq $3, %reg
      andq [[mode]], %reg  -- shouldn't be needed; paranoia
      shlq $13, %reg
      orq $DEFAULT_MXCSR, %reg
      pushq %reg
      ldmxcsr 0(%esp)
      addq $8, %rsp
   */      
   HReg        reg      = newVRegI(env);
   AMD64AMode* zero_rsp = AMD64AMode_IR(0, hregAMD64_RSP());
   addInstr(env, AMD64Instr_Alu64R(Aalu_MOV, AMD64RMI_Imm(3), reg));
   addInstr(env, AMD64Instr_Alu64R(Aalu_AND,
                                   iselIntExpr_RMI(env, mode), reg));
   addInstr(env, AMD64Instr_Sh64(Ash_SHL, 13, AMD64RM_Reg(reg)));
   addInstr(env, AMD64Instr_Alu64R(
                    Aalu_OR, AMD64RMI_Imm(DEFAULT_MXCSR), reg));
   addInstr(env, AMD64Instr_Push(AMD64RMI_Reg(reg)));
   addInstr(env, AMD64Instr_LdMXCSR(zero_rsp));
   add_to_rsp(env, 8);
}


//.. /* Mess with the FPU's rounding mode: 'mode' is an I32-typed
//..    expression denoting a value in the range 0 .. 3, indicating a round
//..    mode encoded as per type IRRoundingMode.  Set the x87 FPU to have
//..    the same rounding.
//.. */
//.. static
//.. void set_FPU_rounding_mode ( ISelEnv* env, IRExpr* mode )
//.. {
//..    HReg rrm  = iselIntExpr_R(env, mode);
//..    HReg rrm2 = newVRegI(env);
//..    X86AMode* zero_esp = X86AMode_IR(0, hregX86_ESP());
//.. 
//..    /* movl  %rrm, %rrm2
//..       andl  $3, %rrm2   -- shouldn't be needed; paranoia
//..       shll  $10, %rrm2
//..       orl   $DEFAULT_FPUCW, %rrm2
//..       pushl %rrm2
//..       fldcw 0(%esp)
//..       addl  $4, %esp
//..    */
//..    addInstr(env, mk_iMOVsd_RR(rrm, rrm2));
//..    addInstr(env, X86Instr_Alu32R(Xalu_AND, X86RMI_Imm(3), rrm2));
//..    addInstr(env, X86Instr_Sh32(Xsh_SHL, 10, X86RM_Reg(rrm2)));
//..    addInstr(env, X86Instr_Alu32R(Xalu_OR, X86RMI_Imm(DEFAULT_FPUCW), rrm2));
//..    addInstr(env, X86Instr_Push(X86RMI_Reg(rrm2)));
//..    addInstr(env, X86Instr_FpLdStCW(True/*load*/, zero_esp));
//..    add_to_esp(env, 4);
//.. }


/* Generate !src into a new vector register, and be sure that the code
   is SSE1 compatible.  Amazing that Intel doesn't offer a less crappy
   way to do this. 
*/
static HReg do_sse_NotV128 ( ISelEnv* env, HReg src )
{
   HReg dst = newVRegV(env);
   /* Set dst to zero.  Not strictly necessary, but the idea of doing
      a FP comparison on whatever junk happens to be floating around
      in it is just too scary. */
   addInstr(env, AMD64Instr_SseReRg(Asse_XOR, dst, dst));
   /* And now make it all 1s ... */
   addInstr(env, AMD64Instr_Sse32Fx4(Asse_CMPEQF, dst, dst));
   /* Finally, xor 'src' into it. */
   addInstr(env, AMD64Instr_SseReRg(Asse_XOR, src, dst));
   return dst;
}


//.. /* Round an x87 FPU value to 53-bit-mantissa precision, to be used
//..    after most non-simple FPU operations (simple = +, -, *, / and
//..    sqrt).
//.. 
//..    This could be done a lot more efficiently if needed, by loading
//..    zero and adding it to the value to be rounded (fldz ; faddp?).
//.. */
//.. static void roundToF64 ( ISelEnv* env, HReg reg )
//.. {
//..    X86AMode* zero_esp = X86AMode_IR(0, hregX86_ESP());
//..    sub_from_esp(env, 8);
//..    addInstr(env, X86Instr_FpLdSt(False/*store*/, 8, reg, zero_esp));
//..    addInstr(env, X86Instr_FpLdSt(True/*load*/, 8, reg, zero_esp));
//..    add_to_esp(env, 8);
//.. }


/*---------------------------------------------------------*/
/*--- ISEL: Integer expressions (64/32/16/8 bit)        ---*/
/*---------------------------------------------------------*/

/* Select insns for an integer-typed expression, and add them to the
   code list.  Return a reg holding the result.  This reg will be a
   virtual register.  THE RETURNED REG MUST NOT BE MODIFIED.  If you
   want to modify it, ask for a new vreg, copy it in there, and modify
   the copy.  The register allocator will do its best to map both
   vregs to the same real register, so the copies will often disappear
   later in the game.

   This should handle expressions of 64, 32, 16 and 8-bit type.  All
   results are returned in a 64-bit register.  For 32-, 16- and 8-bit
   expressions, the upper 32/16/24 bits are arbitrary, so you should
   mask or sign extend partial values if necessary.
*/

static HReg iselIntExpr_R ( ISelEnv* env, IRExpr* e )
{
   HReg r = iselIntExpr_R_wrk(env, e);
   /* sanity checks ... */
#  if 0
   vex_printf("\niselIntExpr_R: "); ppIRExpr(e); vex_printf("\n");
#  endif
   vassert(hregClass(r) == HRcInt64);
   vassert(hregIsVirtual(r));
   return r;
}

/* DO NOT CALL THIS DIRECTLY ! */
static HReg iselIntExpr_R_wrk ( ISelEnv* env, IRExpr* e )
{
   MatchInfo mi;
   DECLARE_PATTERN(p_8Uto64);
   DECLARE_PATTERN(p_16Uto64);
   DECLARE_PATTERN(p_1Uto8_32to1_64to32);
//..    DECLARE_PATTERN(p_32to1_then_1Uto8);

   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(ty == Ity_I32 || Ity_I16 || Ity_I8);

   switch (e->tag) {

   /* --------- TEMP --------- */
   case Iex_Tmp: {
      return lookupIRTemp(env, e->Iex.Tmp.tmp);
   }

   /* --------- LOAD --------- */
   case Iex_LDle: {
      HReg dst = newVRegI(env);
      AMD64AMode* amode = iselIntExpr_AMode ( env, e->Iex.LDle.addr );
      if (ty == Ity_I64) {
         addInstr(env, AMD64Instr_Alu64R(Aalu_MOV,
                                         AMD64RMI_Mem(amode), dst) );
         return dst;
      }
      if (ty == Ity_I32) {
         addInstr(env, AMD64Instr_LoadEX(4,False,amode,dst));
         return dst;
      }
      if (ty == Ity_I16) {
         addInstr(env, AMD64Instr_LoadEX(2,False,amode,dst));
         return dst;
      }
      if (ty == Ity_I8) {
         addInstr(env, AMD64Instr_LoadEX(1,False,amode,dst));
         return dst;
      }
      break;
   }

   /* --------- BINARY OP --------- */
   case Iex_Binop: {
      AMD64AluOp   aluOp;
      AMD64ShiftOp shOp;
//.. 
//..       /* Pattern: Sub32(0,x) */
//..       if (e->Iex.Binop.op == Iop_Sub32 && isZero32(e->Iex.Binop.arg1)) {
//..          HReg dst = newVRegI(env);
//..          HReg reg = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..          addInstr(env, mk_iMOVsd_RR(reg,dst));
//..          addInstr(env, X86Instr_Unary32(Xun_NEG,X86RM_Reg(dst)));
//..          return dst;
//..       }
//.. 
      /* Is it an addition or logical style op? */
      switch (e->Iex.Binop.op) {
         case Iop_Add8: case Iop_Add16: case Iop_Add32: case Iop_Add64: 
            aluOp = Aalu_ADD; break;
         case Iop_Sub8: case Iop_Sub16: case Iop_Sub32: case Iop_Sub64:
            aluOp = Aalu_SUB; break;
         case Iop_And8: case Iop_And16: case Iop_And32: case Iop_And64: 
            aluOp = Aalu_AND; break;
         case Iop_Or8:  case Iop_Or16:  case Iop_Or32:  case Iop_Or64: 
            aluOp = Aalu_OR; break;
         case Iop_Xor8: case Iop_Xor16: case Iop_Xor32: case Iop_Xor64: 
            aluOp = Aalu_XOR; break;
         case Iop_Mul16: case Iop_Mul32: case Iop_Mul64:
            aluOp = Aalu_MUL; break;
         default:
            aluOp = Aalu_INVALID; break;
      }
      /* For commutative ops we assume any literal
         values are on the second operand. */
      if (aluOp != Aalu_INVALID) {
         HReg dst      = newVRegI(env);
         HReg reg      = iselIntExpr_R(env, e->Iex.Binop.arg1);
         AMD64RMI* rmi = iselIntExpr_RMI(env, e->Iex.Binop.arg2);
         addInstr(env, mk_iMOVsd_RR(reg,dst));
         addInstr(env, AMD64Instr_Alu64R(aluOp, rmi, dst));
         return dst;
      }

      /* Perhaps a shift op? */
      switch (e->Iex.Binop.op) {
         case Iop_Shl64: case Iop_Shl32: case Iop_Shl16: case Iop_Shl8:
            shOp = Ash_SHL; break;
         case Iop_Shr64: case Iop_Shr32: case Iop_Shr16: case Iop_Shr8: 
            shOp = Ash_SHR; break;
         case Iop_Sar64: case Iop_Sar32: case Iop_Sar16: case Iop_Sar8: 
            shOp = Ash_SAR; break;
         default:
            shOp = Ash_INVALID; break;
      }
      if (shOp != Ash_INVALID) {
         HReg dst = newVRegI(env);

         /* regL = the value to be shifted */
         HReg regL   = iselIntExpr_R(env, e->Iex.Binop.arg1);
         addInstr(env, mk_iMOVsd_RR(regL,dst));

         /* Do any necessary widening for 32/16/8 bit operands */
         switch (e->Iex.Binop.op) {
            case Iop_Shr64: case Iop_Shl64: case Iop_Sar64: 
               break;
            case Iop_Shl32: case Iop_Shl16: case Iop_Shl8:
               break;
            case Iop_Shr8:
               addInstr(env, AMD64Instr_Alu64R(
                                Aalu_AND, AMD64RMI_Imm(0xFF), dst));
               break;
            case Iop_Shr16:
               addInstr(env, AMD64Instr_Alu64R(
                                Aalu_AND, AMD64RMI_Imm(0xFFFF), dst));
               break;
            case Iop_Shr32:
               addInstr(env, AMD64Instr_MovZLQ(dst,dst));
               break;
//..             case Iop_Sar8:
//..                addInstr(env, X86Instr_Sh32(Xsh_SHL, 24, X86RM_Reg(dst)));
//..                addInstr(env, X86Instr_Sh32(Xsh_SAR, 24, X86RM_Reg(dst)));
//..                break;
//..             case Iop_Sar16:
//..                addInstr(env, X86Instr_Sh32(Xsh_SHL, 16, X86RM_Reg(dst)));
//..                addInstr(env, X86Instr_Sh32(Xsh_SAR, 16, X86RM_Reg(dst)));
//..                break;
            case Iop_Sar32:
               addInstr(env, AMD64Instr_Sh64(Ash_SHL, 32, AMD64RM_Reg(dst)));
               addInstr(env, AMD64Instr_Sh64(Ash_SAR, 32, AMD64RM_Reg(dst)));
               break;
            default: 
               ppIROp(e->Iex.Binop.op);
               vassert(0);
         }

         /* Now consider the shift amount.  If it's a literal, we
            can do a much better job than the general case. */
         if (e->Iex.Binop.arg2->tag == Iex_Const) {
            /* assert that the IR is well-typed */
            Int nshift;
            vassert(e->Iex.Binop.arg2->Iex.Const.con->tag == Ico_U8);
            nshift = e->Iex.Binop.arg2->Iex.Const.con->Ico.U8;
            vassert(nshift >= 0);
            if (nshift > 0)
               /* Can't allow nshift==0 since that means %cl */
               addInstr(env, AMD64Instr_Sh64(
                                shOp, 
                                nshift,
                                AMD64RM_Reg(dst)));
         } else {
            /* General case; we have to force the amount into %cl. */
            HReg regR = iselIntExpr_R(env, e->Iex.Binop.arg2);
            addInstr(env, mk_iMOVsd_RR(regR,hregAMD64_RCX()));
            addInstr(env, AMD64Instr_Sh64(shOp, 0/* %cl */, AMD64RM_Reg(dst)));
         }
         return dst;
      }

      /* Handle misc other ops. */

      if (e->Iex.Binop.op == Iop_DivModS64to32
          || e->Iex.Binop.op == Iop_DivModU64to32) {
         /* 64 x 32 -> (32(rem),32(div)) division */
         /* Get the 64-bit operand into edx:eax, and the other into
            any old R/M. */
         HReg      rax     = hregAMD64_RAX();
         HReg      rdx     = hregAMD64_RDX();
         HReg      dst     = newVRegI(env);
         Bool      syned   = toBool(e->Iex.Binop.op == Iop_DivModS64to32);
         AMD64RM*  rmRight = iselIntExpr_RM(env, e->Iex.Binop.arg2);
         /* Compute the left operand into a reg, and then 
            put the top half in edx and the bottom in eax. */
         HReg left64 = iselIntExpr_R(env, e->Iex.Binop.arg1);
         addInstr(env, mk_iMOVsd_RR(left64, rdx));
         addInstr(env, mk_iMOVsd_RR(left64, rax));
         addInstr(env, AMD64Instr_Sh64(Ash_SHR, 32, AMD64RM_Reg(rdx)));
         addInstr(env, AMD64Instr_Div(syned, 4, rmRight));
	 addInstr(env, AMD64Instr_MovZLQ(rdx,rdx));
	 addInstr(env, AMD64Instr_MovZLQ(rax,rax));
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, 32, AMD64RM_Reg(rdx)));
         addInstr(env, mk_iMOVsd_RR(rax, dst));
         addInstr(env, AMD64Instr_Alu64R(Aalu_OR, AMD64RMI_Reg(rdx), dst));
         return dst;
      }

      if (e->Iex.Binop.op == Iop_32HLto64) {
         HReg hi32  = newVRegI(env);
         HReg lo32  = newVRegI(env);
         HReg hi32s = iselIntExpr_R(env, e->Iex.Binop.arg1);
         HReg lo32s = iselIntExpr_R(env, e->Iex.Binop.arg2);
         addInstr(env, mk_iMOVsd_RR(hi32s, hi32));
         addInstr(env, mk_iMOVsd_RR(lo32s, lo32));
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, 32, AMD64RM_Reg(hi32)));
	 addInstr(env, AMD64Instr_MovZLQ(lo32,lo32));
         addInstr(env, AMD64Instr_Alu64R(
                          Aalu_OR, AMD64RMI_Reg(lo32), hi32));
         return hi32;
      }

      if (e->Iex.Binop.op == Iop_16HLto32) {
         HReg hi16  = newVRegI(env);
         HReg lo16  = newVRegI(env);
         HReg hi16s = iselIntExpr_R(env, e->Iex.Binop.arg1);
         HReg lo16s = iselIntExpr_R(env, e->Iex.Binop.arg2);
         addInstr(env, mk_iMOVsd_RR(hi16s, hi16));
         addInstr(env, mk_iMOVsd_RR(lo16s, lo16));
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, 16, AMD64RM_Reg(hi16)));
         addInstr(env, AMD64Instr_Alu64R(
                          Aalu_AND, AMD64RMI_Imm(0xFFFF), lo16));
         addInstr(env, AMD64Instr_Alu64R(
                          Aalu_OR, AMD64RMI_Reg(lo16), hi16));
         return hi16;
      }

//..       if (e->Iex.Binop.op == Iop_8HLto16) {
//..          HReg hi8  = newVRegI(env);
//..          HReg lo8  = newVRegI(env);
//..          HReg hi8s = iselIntExpr_R(env, e->Iex.Binop.arg1);
//..          HReg lo8s = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..          addInstr(env, mk_iMOVsd_RR(hi8s, hi8));
//..          addInstr(env, mk_iMOVsd_RR(lo8s, lo8));
//..          addInstr(env, X86Instr_Sh32(Xsh_SHL, 8, X86RM_Reg(hi8)));
//..          addInstr(env, X86Instr_Alu32R(Xalu_AND, X86RMI_Imm(0xFF), lo8));
//..          addInstr(env, X86Instr_Alu32R(Xalu_OR, X86RMI_Reg(lo8), hi8));
//..          return hi8;
//..       }
//.. 
//..       if (e->Iex.Binop.op == Iop_16HLto32) {
//..          HReg hi16  = newVRegI(env);
//..          HReg lo16  = newVRegI(env);
//..          HReg hi16s = iselIntExpr_R(env, e->Iex.Binop.arg1);
//..          HReg lo16s = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..          addInstr(env, mk_iMOVsd_RR(hi16s, hi16));
//..          addInstr(env, mk_iMOVsd_RR(lo16s, lo16));
//..          addInstr(env, X86Instr_Sh32(Xsh_SHL, 16, X86RM_Reg(hi16)));
//..          addInstr(env, X86Instr_Alu32R(Xalu_AND, X86RMI_Imm(0xFFFF), lo16));
//..          addInstr(env, X86Instr_Alu32R(Xalu_OR, X86RMI_Reg(lo16), hi16));
//..          return hi16;
//..       }

      if (e->Iex.Binop.op == Iop_MullS32
          || e->Iex.Binop.op == Iop_MullS16
          || e->Iex.Binop.op == Iop_MullS8
          || e->Iex.Binop.op == Iop_MullU32 
          || e->Iex.Binop.op == Iop_MullU16 
          || e->Iex.Binop.op == Iop_MullU8) {
         HReg a32   = newVRegI(env);
         HReg b32   = newVRegI(env);
         HReg a32s  = iselIntExpr_R(env, e->Iex.Binop.arg1);
         HReg b32s  = iselIntExpr_R(env, e->Iex.Binop.arg2);
         Int          shift  = 0;
         AMD64ShiftOp shr_op = Ash_SHR;
         switch (e->Iex.Binop.op) {
            case Iop_MullS32: shr_op = Ash_SAR; shift = 32; break;
            case Iop_MullS16: shr_op = Ash_SAR; shift = 48; break;
            case Iop_MullS8:  shr_op = Ash_SAR; shift = 56; break;
            case Iop_MullU32: shr_op = Ash_SHR; shift = 32; break;
            case Iop_MullU16: shr_op = Ash_SHR; shift = 48; break;
            case Iop_MullU8:  shr_op = Ash_SHR; shift = 56; break;
            default: vassert(0);
         }

         addInstr(env, mk_iMOVsd_RR(a32s, a32));
         addInstr(env, mk_iMOVsd_RR(b32s, b32));
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, shift, AMD64RM_Reg(a32)));
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, shift, AMD64RM_Reg(b32)));
         addInstr(env, AMD64Instr_Sh64(shr_op,  shift, AMD64RM_Reg(a32)));
         addInstr(env, AMD64Instr_Sh64(shr_op,  shift, AMD64RM_Reg(b32)));
         addInstr(env, AMD64Instr_Alu64R(Aalu_MUL, AMD64RMI_Reg(a32), b32));
         return b32;
      }

      if (e->Iex.Binop.op == Iop_CmpF64) {
         HReg fL = iselDblExpr(env, e->Iex.Binop.arg1);
         HReg fR = iselDblExpr(env, e->Iex.Binop.arg2);
         HReg dst = newVRegI(env);
         addInstr(env, AMD64Instr_SseUComIS(8,fL,fR,dst));
         /* Mask out irrelevant parts of the result so as to conform
            to the CmpF64 definition. */
         addInstr(env, AMD64Instr_Alu64R(Aalu_AND, AMD64RMI_Imm(0x45), dst));
         return dst;
      }

      if (e->Iex.Binop.op == Iop_F64toI32
          || e->Iex.Binop.op == Iop_F64toI64) {
         Int  szD = e->Iex.Binop.op==Iop_F64toI32 ? 4 : 8;
         HReg rf  = iselDblExpr(env, e->Iex.Binop.arg2);
         HReg dst = newVRegI(env);
         set_SSE_rounding_mode( env, e->Iex.Binop.arg1 );
         addInstr(env, AMD64Instr_SseSF2SI( 8, szD, rf, dst ));
         set_SSE_rounding_default(env);
         return dst;
      }

//..       if (e->Iex.Binop.op == Iop_F64toI32 || e->Iex.Binop.op == Iop_F64toI16) {
//..          Int  sz  = e->Iex.Binop.op == Iop_F64toI16 ? 2 : 4;
//..          HReg rf  = iselDblExpr(env, e->Iex.Binop.arg2);
//..          HReg dst = newVRegI(env);
//.. 
//..          /* Used several times ... */
//..          X86AMode* zero_esp = X86AMode_IR(0, hregX86_ESP());
//.. 
//..          /* rf now holds the value to be converted, and rrm holds the
//.. 	    rounding mode value, encoded as per the IRRoundingMode
//.. 	    enum.  The first thing to do is set the FPU's rounding
//.. 	    mode accordingly. */
//.. 
//..          /* Create a space for the format conversion. */
//..          /* subl $4, %esp */
//..          sub_from_esp(env, 4);
//.. 
//.. 	 /* Set host rounding mode */
//.. 	 set_FPU_rounding_mode( env, e->Iex.Binop.arg1 );
//.. 
//..          /* gistw/l %rf, 0(%esp) */
//..          addInstr(env, X86Instr_FpLdStI(False/*store*/, sz, rf, zero_esp));
//.. 
//..          if (sz == 2) {
//..             /* movzwl 0(%esp), %dst */
//..             addInstr(env, X86Instr_LoadEX(2,False,zero_esp,dst));
//..          } else {
//..             /* movl 0(%esp), %dst */
//..             vassert(sz == 4);
//..             addInstr(env, X86Instr_Alu32R(
//..                              Xalu_MOV, X86RMI_Mem(zero_esp), dst));
//..          }
//.. 
//.. 	 /* Restore default FPU rounding. */
//..          set_FPU_rounding_default( env );
//.. 
//..          /* addl $4, %esp */
//.. 	 add_to_esp(env, 4);
//..          return dst;
//..       }
//.. 
//..       /* C3210 flags following FPU partial remainder (fprem), both
//..          IEEE compliant (PREM1) and non-IEEE compliant (PREM). */
//..       if (e->Iex.Binop.op == Iop_PRemC3210F64
//..           || e->Iex.Binop.op == Iop_PRem1C3210F64) {
//..          HReg junk = newVRegF(env);
//..          HReg dst  = newVRegI(env);
//..          HReg srcL = iselDblExpr(env, e->Iex.Binop.arg1);
//..          HReg srcR = iselDblExpr(env, e->Iex.Binop.arg2);
//..          addInstr(env, X86Instr_FpBinary(
//..                            e->Iex.Binop.op==Iop_PRemC3210F64 
//..                               ? Xfp_PREM : Xfp_PREM1,
//..                            srcL,srcR,junk
//..                  ));
//..          /* The previous pseudo-insn will have left the FPU's C3210
//..             flags set correctly.  So bag them. */
//..          addInstr(env, X86Instr_FpStSW_AX());
//..          addInstr(env, mk_iMOVsd_RR(hregX86_EAX(), dst));
//.. 	 addInstr(env, X86Instr_Alu32R(Xalu_AND, X86RMI_Imm(0x4700), dst));
//..          return dst;
//..       }

      break;
   }

   /* --------- UNARY OP --------- */
   case Iex_Unop: {
      /* 32Uto64(16Uto32(expr16)) */
      DEFINE_PATTERN(p_16Uto64,
                     unop(Iop_32Uto64, unop(Iop_16Uto32, bind(0)) ) );
      if (matchIRExpr(&mi,p_16Uto64,e)) {
         IRExpr* expr16 = mi.bindee[0];
         HReg    dst    = newVRegI(env);
         HReg    src    = iselIntExpr_R(env, expr16);
         addInstr(env, mk_iMOVsd_RR(src,dst) );
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, 48, AMD64RM_Reg(dst)));
         addInstr(env, AMD64Instr_Sh64(Ash_SHR, 48, AMD64RM_Reg(dst)));
         return dst;
      }

      /* 32Uto64(8Uto32(expr16)) */
      DEFINE_PATTERN(p_8Uto64,
                     unop(Iop_32Uto64, unop(Iop_8Uto32, bind(0)) ) );
      if (matchIRExpr(&mi,p_8Uto64,e)) {
         IRExpr* expr8 = mi.bindee[0];
         HReg    dst   = newVRegI(env);
         HReg    src   = iselIntExpr_R(env, expr8);
         addInstr(env, mk_iMOVsd_RR(src,dst) );
         addInstr(env, AMD64Instr_Sh64(Ash_SHL, 56, AMD64RM_Reg(dst)));
         addInstr(env, AMD64Instr_Sh64(Ash_SHR, 56, AMD64RM_Reg(dst)));
         return dst;
      }

      /* 1Uto8(32to1(64to32(expr64))) */
      DEFINE_PATTERN(p_1Uto8_32to1_64to32,
                     unop(Iop_1Uto8, 
                          unop(Iop_32to1, unop(Iop_64to32, bind(0)))));
      if (matchIRExpr(&mi,p_1Uto8_32to1_64to32,e)) {
         IRExpr* expr64 = mi.bindee[0];
         HReg    dst    = newVRegI(env);
         HReg    src    = iselIntExpr_R(env, expr64);
         addInstr(env, mk_iMOVsd_RR(src,dst) );
         addInstr(env, AMD64Instr_Alu64R(Aalu_AND,
                                         AMD64RMI_Imm(1), dst));
         return dst;
      }

//..       /* 16Uto32(LDle(expr32)) */
//..       {
//..          DECLARE_PATTERN(p_LDle16_then_16Uto32);
//..          DEFINE_PATTERN(p_LDle16_then_16Uto32,
//..             unop(Iop_16Uto32,IRExpr_LDle(Ity_I16,bind(0))) );
//..          if (matchIRExpr(&mi,p_LDle16_then_16Uto32,e)) {
//..             HReg dst = newVRegI(env);
//..             X86AMode* amode = iselIntExpr_AMode ( env, mi.bindee[0] );
//..             addInstr(env, X86Instr_LoadEX(2,False,amode,dst));
//..             return dst;
//..          }
//..       }

      switch (e->Iex.Unop.op) {
         case Iop_32Uto64: {
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            addInstr(env, AMD64Instr_MovZLQ(src,dst) );
            return dst;
         }
         case Iop_32Sto64: {
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            UInt amt = 32;
            addInstr(env, mk_iMOVsd_RR(src,dst) );
            addInstr(env, AMD64Instr_Sh64(Ash_SHL, amt, AMD64RM_Reg(dst)));
            addInstr(env, AMD64Instr_Sh64(Ash_SAR, amt, AMD64RM_Reg(dst)));
            return dst;
         }
         case Iop_128HIto64: {
            HReg rHi, rLo;
            iselInt128Expr(&rHi,&rLo, env, e->Iex.Unop.arg);
            return rHi; /* and abandon rLo */
         }
         case Iop_128to64: {
            HReg rHi, rLo;
            iselInt128Expr(&rHi,&rLo, env, e->Iex.Unop.arg);
            return rLo; /* and abandon rHi */
         }
         case Iop_8Uto16:
//..          case Iop_8Uto32:
         case Iop_16Uto32: {
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            UInt mask = e->Iex.Unop.op==Iop_16Uto32 ? 0xFFFF : 0xFF;
            addInstr(env, mk_iMOVsd_RR(src,dst) );
            addInstr(env, AMD64Instr_Alu64R(Aalu_AND,
                                            AMD64RMI_Imm(mask), dst));
            return dst;
         }
         case Iop_8Sto16:
         case Iop_8Sto32:
         case Iop_16Sto32: {
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            UInt amt = e->Iex.Unop.op==Iop_16Sto32 ? 48 : 56;
            addInstr(env, mk_iMOVsd_RR(src,dst) );
            addInstr(env, AMD64Instr_Sh64(Ash_SHL, amt, AMD64RM_Reg(dst)));
            addInstr(env, AMD64Instr_Sh64(Ash_SAR, amt, AMD64RM_Reg(dst)));
            return dst;
         }
 	 case Iop_Not8:
 	 case Iop_Not16:
         case Iop_Not32:
         case Iop_Not64: {
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            addInstr(env, mk_iMOVsd_RR(src,dst) );
            addInstr(env, AMD64Instr_Unary64(Aun_NOT,AMD64RM_Reg(dst)));
            return dst;
         }
//..          case Iop_64HIto32: {
//..             HReg rHi, rLo;
//..             iselInt64Expr(&rHi,&rLo, env, e->Iex.Unop.arg);
//..             return rHi; /* and abandon rLo .. poor wee thing :-) */
//..          }
//..          case Iop_64to32: {
//..             HReg rHi, rLo;
//..             iselInt64Expr(&rHi,&rLo, env, e->Iex.Unop.arg);
//..             return rLo; /* similar stupid comment to the above ... */
//..          }
//..          case Iop_16HIto8:
         case Iop_32HIto16:
         case Iop_64HIto32: {
            HReg dst  = newVRegI(env);
            HReg src  = iselIntExpr_R(env, e->Iex.Unop.arg);
            Int shift = 0;
            switch (e->Iex.Unop.op) {
               case Iop_32HIto16: shift = 16; break;
               case Iop_64HIto32: shift = 32; break;
               default: vassert(0);
            }
            addInstr(env, mk_iMOVsd_RR(src,dst) );
            addInstr(env, AMD64Instr_Sh64(
                             Ash_SHR, shift, AMD64RM_Reg(dst)));
            return dst;
         }
//..          case Iop_1Uto32:
         case Iop_1Uto8: {
            HReg dst           = newVRegI(env);
            AMD64CondCode cond = iselCondCode(env, e->Iex.Unop.arg);
            addInstr(env, AMD64Instr_Set64(cond,dst));
            return dst;
         }
//..          case Iop_1Sto8:
//..          case Iop_1Sto16:
//..          case Iop_1Sto32: {
//..             /* could do better than this, but for now ... */
//..             HReg dst         = newVRegI(env);
//..             X86CondCode cond = iselCondCode(env, e->Iex.Unop.arg);
//..             addInstr(env, X86Instr_Set32(cond,dst));
//..             addInstr(env, X86Instr_Sh32(Xsh_SHL, 31, X86RM_Reg(dst)));
//..             addInstr(env, X86Instr_Sh32(Xsh_SAR, 31, X86RM_Reg(dst)));
//..             return dst;
//..          }
         case Iop_Ctz64: {
            /* Count trailing zeroes, implemented by amd64 'bsfq' */
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            addInstr(env, AMD64Instr_Bsfr64(True,src,dst));
            return dst;
         }
         case Iop_Clz64: {
            /* Count leading zeroes.  Do 'bsrq' to establish the index
               of the highest set bit, and subtract that value from
               63. */
            HReg tmp = newVRegI(env);
            HReg dst = newVRegI(env);
            HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
            addInstr(env, AMD64Instr_Bsfr64(False,src,tmp));
            addInstr(env, AMD64Instr_Alu64R(Aalu_MOV, 
                                            AMD64RMI_Imm(63), dst));
            addInstr(env, AMD64Instr_Alu64R(Aalu_SUB,
                                            AMD64RMI_Reg(tmp), dst));
            return dst;
         }

//..          case Iop_128to32: {
//..             HReg      dst  = newVRegI(env);
//..             HReg      vec  = iselVecExpr(env, e->Iex.Unop.arg);
//..             X86AMode* esp0 = X86AMode_IR(0, hregX86_ESP());
//..             sub_from_esp(env, 16);
//..             addInstr(env, X86Instr_SseLdSt(False/*store*/, vec, esp0));
//..             addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(esp0), dst ));
//..             add_to_esp(env, 16);
//..             return dst;
//..          }


         /* V128{HI}to64 */
         case Iop_V128HIto64:
         case Iop_V128to64: {
            Int  off = e->Iex.Unop.op==Iop_V128HIto64 ? 8 : 0;
            HReg dst = newVRegI(env);
            HReg vec = iselVecExpr(env, e->Iex.Unop.arg);
            AMD64AMode* rsp0 = AMD64AMode_IR(0,   hregAMD64_RSP());
            AMD64AMode* rspN = AMD64AMode_IR(off, hregAMD64_RSP());
            sub_from_rsp(env, 16);
            addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 16, vec, rsp0));
            addInstr(env, AMD64Instr_Alu64R( Aalu_MOV, 
                                           AMD64RMI_Mem(rspN), dst ));
            add_to_rsp(env, 16);
            return dst;
         }

         /* ReinterpF64asI64(e) */
         /* Given an IEEE754 double, produce an I64 with the same bit
            pattern. */
         case Iop_ReinterpF64asI64: {
            AMD64AMode* m8_rsp = AMD64AMode_IR(-8, hregAMD64_RSP());
            HReg        dst    = newVRegI(env);
            HReg        src    = iselDblExpr(env, e->Iex.Unop.arg);
            /* paranoia */
            set_SSE_rounding_default(env);
            addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 8, src, m8_rsp));
            addInstr(env, AMD64Instr_Alu64R(
                             Aalu_MOV, AMD64RMI_Mem(m8_rsp), dst));
            return dst;
         }

         case Iop_16to8:
         case Iop_32to8:
         case Iop_32to16:
         case Iop_64to32:
            /* These are no-ops. */
            return iselIntExpr_R(env, e->Iex.Unop.arg);

         default: 
            break;
      }
      break;
   }

   /* --------- GET --------- */
   case Iex_Get: {
      if (ty == Ity_I64) {
         HReg dst = newVRegI(env);
         addInstr(env, AMD64Instr_Alu64R(
                          Aalu_MOV, 
                          AMD64RMI_Mem(
                             AMD64AMode_IR(e->Iex.Get.offset,
                                           hregAMD64_RBP())),
                          dst));
         return dst;
      }
      if (ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32) {
         HReg dst = newVRegI(env);
         addInstr(env, AMD64Instr_LoadEX(
                          toUChar(ty==Ity_I8 ? 1 : (ty==Ity_I16 ? 2 : 4)),
                          False,
                          AMD64AMode_IR(e->Iex.Get.offset,hregAMD64_RBP()),
                          dst));
         return dst;
      }
      break;
   }

   case Iex_GetI: {
      AMD64AMode* am 
         = genGuestArrayOffset(
              env, e->Iex.GetI.descr, 
                   e->Iex.GetI.ix, e->Iex.GetI.bias );
      HReg dst = newVRegI(env);
      if (ty == Ity_I8) {
         addInstr(env, AMD64Instr_LoadEX( 1, False, am, dst ));
         return dst;
      }
      break;
   }

   /* --------- CCALL --------- */
   case Iex_CCall: {
      HReg    dst = newVRegI(env);
      vassert(ty == e->Iex.CCall.retty);

      /* be very restrictive for now.  Only 64-bit ints allowed
         for args, and 64 bits for return type. */
      if (e->Iex.CCall.retty != Ity_I64)
         goto irreducible;

      /* Marshal args, do the call. */
      doHelperCall( env, False, NULL, e->Iex.CCall.cee, e->Iex.CCall.args );

      addInstr(env, mk_iMOVsd_RR(hregAMD64_RAX(), dst));
      return dst;
   }

   /* --------- LITERAL --------- */
   /* 64/32/16/8-bit literals */
   case Iex_Const:
      if (ty == Ity_I64) {
         HReg r = newVRegI(env);
         addInstr(env, AMD64Instr_Imm64(e->Iex.Const.con->Ico.U64, r));
         return r;
      } else {
         AMD64RMI* rmi = iselIntExpr_RMI ( env, e );
         HReg      r   = newVRegI(env);
         addInstr(env, AMD64Instr_Alu64R(Aalu_MOV, rmi, r));
         return r;
      }

   /* --------- MULTIPLEX --------- */
   case Iex_Mux0X: {
     if ((ty == Ity_I64 || ty == Ity_I32 || ty == Ity_I16 || ty == Ity_I8)
         && typeOfIRExpr(env->type_env,e->Iex.Mux0X.cond) == Ity_I8) {
        HReg     r8;
        HReg     rX  = iselIntExpr_R(env, e->Iex.Mux0X.exprX);
        AMD64RM* r0  = iselIntExpr_RM(env, e->Iex.Mux0X.expr0);
        HReg dst = newVRegI(env);
        addInstr(env, mk_iMOVsd_RR(rX,dst));
        r8 = iselIntExpr_R(env, e->Iex.Mux0X.cond);
        addInstr(env, AMD64Instr_Test64(AMD64RI_Imm(0xFF), AMD64RM_Reg(r8)));
        addInstr(env, AMD64Instr_CMov64(Acc_Z,r0,dst));
        return dst;
      }
      break;
   }

   default: 
   break;
   } /* switch (e->tag) */

   /* We get here if no pattern matched. */
  irreducible:
   ppIRExpr(e);
   vpanic("iselIntExpr_R(amd64): cannot reduce tree");
}


/*---------------------------------------------------------*/
/*--- ISEL: Integer expression auxiliaries              ---*/
/*---------------------------------------------------------*/

/* --------------------- AMODEs --------------------- */

/* Return an AMode which computes the value of the specified
   expression, possibly also adding insns to the code list as a
   result.  The expression may only be a 32-bit one.
*/

static AMD64AMode* iselIntExpr_AMode ( ISelEnv* env, IRExpr* e )
{
   AMD64AMode* am = iselIntExpr_AMode_wrk(env, e);
   vassert(sane_AMode(am));
   return am;
}

/* DO NOT CALL THIS DIRECTLY ! */
static AMD64AMode* iselIntExpr_AMode_wrk ( ISelEnv* env, IRExpr* e )
{
   MatchInfo mi;
   DECLARE_PATTERN(p_complex);
   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(ty == Ity_I64);

   /* Add64( Add64(expr1, Shl64(expr2, imm8)), simm32 ) */
   /*              bind0        bind1  bind2   bind3   */
   DEFINE_PATTERN(p_complex,
      binop( Iop_Add64,
             binop( Iop_Add64, 
                    bind(0), 
                    binop(Iop_Shl64, bind(1), bind(2))
                  ),
             bind(3)
           )
   );
   if (matchIRExpr(&mi, p_complex, e)) {
      IRExpr* expr1  = mi.bindee[0];
      IRExpr* expr2  = mi.bindee[1];
      IRExpr* imm8   = mi.bindee[2];
      IRExpr* simm32 = mi.bindee[3];
      if (imm8->tag == Iex_Const 
          && imm8->Iex.Const.con->tag == Ico_U8
          && imm8->Iex.Const.con->Ico.U8 < 4
          /* imm8 is OK, now check simm32 */
          && simm32->tag == Iex_Const
          && simm32->Iex.Const.con->tag == Ico_U64
          && fitsIn32Bits(simm32->Iex.Const.con->Ico.U64)) {
         UInt shift = imm8->Iex.Const.con->Ico.U8;
         UInt offset = toUInt(simm32->Iex.Const.con->Ico.U64);
         HReg r1 = iselIntExpr_R(env, expr1);
         HReg r2 = iselIntExpr_R(env, expr2);
         vassert(shift == 0 || shift == 1 || shift == 2 || shift == 3);
         return AMD64AMode_IRRS(offset, r1, r2, shift);
      }
   }

   /* Add64(expr1, Shl64(expr2, imm)) */
   if (e->tag == Iex_Binop
       && e->Iex.Binop.op == Iop_Add64
       && e->Iex.Binop.arg2->tag == Iex_Binop
       && e->Iex.Binop.arg2->Iex.Binop.op == Iop_Shl64
       && e->Iex.Binop.arg2->Iex.Binop.arg2->tag == Iex_Const
       && e->Iex.Binop.arg2->Iex.Binop.arg2->Iex.Const.con->tag == Ico_U8) {
      UInt shift = e->Iex.Binop.arg2->Iex.Binop.arg2->Iex.Const.con->Ico.U8;
      if (shift == 1 || shift == 2 || shift == 3) {
         HReg r1 = iselIntExpr_R(env, e->Iex.Binop.arg1);
         HReg r2 = iselIntExpr_R(env, e->Iex.Binop.arg2->Iex.Binop.arg1 );
         return AMD64AMode_IRRS(0, r1, r2, shift);
      }
   }

   /* Add64(expr,i) */
   if (e->tag == Iex_Binop 
       && e->Iex.Binop.op == Iop_Add64
       && e->Iex.Binop.arg2->tag == Iex_Const
       && e->Iex.Binop.arg2->Iex.Const.con->tag == Ico_U64
       && fitsIn32Bits(e->Iex.Binop.arg2->Iex.Const.con->Ico.U64)) {
      HReg r1 = iselIntExpr_R(env, e->Iex.Binop.arg1);
      return AMD64AMode_IR(
                toUInt(e->Iex.Binop.arg2->Iex.Const.con->Ico.U64), 
                r1
             );
   }

   /* Doesn't match anything in particular.  Generate it into
      a register and use that. */
   {
      HReg r1 = iselIntExpr_R(env, e);
      return AMD64AMode_IR(0, r1);
   }
}


/* --------------------- RMIs --------------------- */

/* Similarly, calculate an expression into an X86RMI operand.  As with
   iselIntExpr_R, the expression can have type 32, 16 or 8 bits.  */

static AMD64RMI* iselIntExpr_RMI ( ISelEnv* env, IRExpr* e )
{
   AMD64RMI* rmi = iselIntExpr_RMI_wrk(env, e);
   /* sanity checks ... */
   switch (rmi->tag) {
      case Armi_Imm:
         return rmi;
      case Armi_Reg:
         vassert(hregClass(rmi->Armi.Reg.reg) == HRcInt64);
         vassert(hregIsVirtual(rmi->Armi.Reg.reg));
         return rmi;
      case Armi_Mem:
         vassert(sane_AMode(rmi->Armi.Mem.am));
         return rmi;
      default:
         vpanic("iselIntExpr_RMI: unknown amd64 RMI tag");
   }
}

/* DO NOT CALL THIS DIRECTLY ! */
static AMD64RMI* iselIntExpr_RMI_wrk ( ISelEnv* env, IRExpr* e )
{
   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(ty == Ity_I64 || ty == Ity_I32 
           || ty == Ity_I16 || ty == Ity_I8);

   /* special case: immediate 64/32/16/8 */
   if (e->tag == Iex_Const) {
      switch (e->Iex.Const.con->tag) {
        case Ico_U64:
           if (fitsIn32Bits(e->Iex.Const.con->Ico.U64)) {
              return AMD64RMI_Imm(toUInt(e->Iex.Const.con->Ico.U64));
           }
           break;
         case Ico_U32:
            return AMD64RMI_Imm(e->Iex.Const.con->Ico.U32); break;
         case Ico_U16:
            return AMD64RMI_Imm(0xFFFF & e->Iex.Const.con->Ico.U16); break;
         case Ico_U8:
            return AMD64RMI_Imm(0xFF & e->Iex.Const.con->Ico.U8); break;
         default:
            vpanic("iselIntExpr_RMI.Iex_Const(amd64)");
      }
   }

   /* special case: 64-bit GET */
   if (e->tag == Iex_Get && ty == Ity_I64) {
      return AMD64RMI_Mem(AMD64AMode_IR(e->Iex.Get.offset,
                                        hregAMD64_RBP()));
   }

   /* special case: 64-bit load from memory */
   if (e->tag == Iex_LDle && ty == Ity_I64) {
      AMD64AMode* am = iselIntExpr_AMode(env, e->Iex.LDle.addr);
      return AMD64RMI_Mem(am);
   }

   /* default case: calculate into a register and return that */
   {
      HReg r = iselIntExpr_R ( env, e );
      return AMD64RMI_Reg(r);
   }
}


/* --------------------- RIs --------------------- */

/* Calculate an expression into an AMD64RI operand.  As with
   iselIntExpr_R, the expression can have type 64, 32, 16 or 8
   bits. */

static AMD64RI* iselIntExpr_RI ( ISelEnv* env, IRExpr* e )
{
   AMD64RI* ri = iselIntExpr_RI_wrk(env, e);
   /* sanity checks ... */
   switch (ri->tag) {
      case Ari_Imm:
         return ri;
      case Armi_Reg:
         vassert(hregClass(ri->Ari.Reg.reg) == HRcInt64);
         vassert(hregIsVirtual(ri->Ari.Reg.reg));
         return ri;
      default:
         vpanic("iselIntExpr_RI: unknown amd64 RI tag");
   }
}

/* DO NOT CALL THIS DIRECTLY ! */
static AMD64RI* iselIntExpr_RI_wrk ( ISelEnv* env, IRExpr* e )
{
   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(ty == Ity_I64 || ty == Ity_I32 
           || ty == Ity_I16 || ty == Ity_I8);

   /* special case: immediate */
   if (e->tag == Iex_Const) {
      switch (e->Iex.Const.con->tag) {
        case Ico_U64:
           if (fitsIn32Bits(e->Iex.Const.con->Ico.U64)) {
              return AMD64RI_Imm(toUInt(e->Iex.Const.con->Ico.U64));
           }
           break;
         case Ico_U32:
            return AMD64RI_Imm(e->Iex.Const.con->Ico.U32);
         case Ico_U16: 
            return AMD64RI_Imm(0xFFFF & e->Iex.Const.con->Ico.U16);
         case Ico_U8:
            return AMD64RI_Imm(0xFF & e->Iex.Const.con->Ico.U8);
         default:
            vpanic("iselIntExpr_RMI.Iex_Const(amd64)");
      }
   }

   /* default case: calculate into a register and return that */
   {
      HReg r = iselIntExpr_R ( env, e );
      return AMD64RI_Reg(r);
   }
}


/* --------------------- RMs --------------------- */

/* Similarly, calculate an expression into an AMD64RM operand.  As
   with iselIntExpr_R, the expression can have type 64, 32, 16 or 8
   bits.  */

static AMD64RM* iselIntExpr_RM ( ISelEnv* env, IRExpr* e )
{
   AMD64RM* rm = iselIntExpr_RM_wrk(env, e);
   /* sanity checks ... */
   switch (rm->tag) {
      case Arm_Reg:
         vassert(hregClass(rm->Arm.Reg.reg) == HRcInt64);
         vassert(hregIsVirtual(rm->Arm.Reg.reg));
         return rm;
      case Arm_Mem:
         vassert(sane_AMode(rm->Arm.Mem.am));
         return rm;
      default:
         vpanic("iselIntExpr_RM: unknown amd64 RM tag");
   }
}

/* DO NOT CALL THIS DIRECTLY ! */
static AMD64RM* iselIntExpr_RM_wrk ( ISelEnv* env, IRExpr* e )
{
   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(ty == Ity_I64 || ty == Ity_I32 || ty == Ity_I16 || ty == Ity_I8);

   /* special case: 64-bit GET */
   if (e->tag == Iex_Get && ty == Ity_I64) {
      return AMD64RM_Mem(AMD64AMode_IR(e->Iex.Get.offset,
                                       hregAMD64_RBP()));
   }

   /* special case: load from memory */

   /* default case: calculate into a register and return that */
   {
      HReg r = iselIntExpr_R ( env, e );
      return AMD64RM_Reg(r);
   }
}


/* --------------------- CONDCODE --------------------- */

/* Generate code to evaluated a bit-typed expression, returning the
   condition code which would correspond when the expression would
   notionally have returned 1. */

static AMD64CondCode iselCondCode ( ISelEnv* env, IRExpr* e )
{
   /* Uh, there's nothing we can sanity check here, unfortunately. */
   return iselCondCode_wrk(env,e);
}

/* DO NOT CALL THIS DIRECTLY ! */
static AMD64CondCode iselCondCode_wrk ( ISelEnv* env, IRExpr* e )
{
   MatchInfo mi;
   DECLARE_PATTERN(p_32to1_64to32);
//..    DECLARE_PATTERN(p_1Uto32_then_32to1);
//..    DECLARE_PATTERN(p_1Sto32_then_32to1);

   vassert(e);
   vassert(typeOfIRExpr(env->type_env,e) == Ity_I1);

//..    /* Constant 1:Bit */
//..    if (e->tag == Iex_Const && e->Iex.Const.con->Ico.U1 == True) {
//..       HReg r;
//..       vassert(e->Iex.Const.con->tag == Ico_U1);
//..       r = newVRegI(env);
//..       addInstr(env, X86Instr_Alu32R(Xalu_MOV,X86RMI_Imm(0),r));
//..       addInstr(env, X86Instr_Alu32R(Xalu_XOR,X86RMI_Reg(r),r));
//..       return Xcc_Z;
//..    }

   /* Not1(...) */
   if (e->tag == Iex_Unop && e->Iex.Unop.op == Iop_Not1) {
      /* Generate code for the arg, and negate the test condition */
      return 1 ^ iselCondCode(env, e->Iex.Unop.arg);
   }

//..    /* 32to1(1Uto32(expr1)) -- the casts are pointless, ignore them */
//..    DEFINE_PATTERN(p_1Uto32_then_32to1,
//..                   unop(Iop_32to1,unop(Iop_1Uto32,bind(0))));
//..    if (matchIRExpr(&mi,p_1Uto32_then_32to1,e)) {
//..       IRExpr* expr1 = mi.bindee[0];
//..       return iselCondCode(env, expr1);
//..    }
//.. 
//..    /* 32to1(1Sto32(expr1)) -- the casts are pointless, ignore them */
//..    DEFINE_PATTERN(p_1Sto32_then_32to1,
//..                   unop(Iop_32to1,unop(Iop_1Sto32,bind(0))));
//..    if (matchIRExpr(&mi,p_1Sto32_then_32to1,e)) {
//..       IRExpr* expr1 = mi.bindee[0];
//..       return iselCondCode(env, expr1);
//..    }

   /* pattern: 32to1(64to32(expr64)) */
   DEFINE_PATTERN(p_32to1_64to32, 
      unop(Iop_32to1,unop(Iop_64to32, bind(0)))
   );
   if (matchIRExpr(&mi,p_32to1_64to32,e)) {
      AMD64RM* rm = iselIntExpr_RM(env, mi.bindee[0]);
      addInstr(env, AMD64Instr_Test64(AMD64RI_Imm(1),rm));
      return Acc_NZ;
   }

//..    /* CmpEQ8 / CmpNE8 */
//..    if (e->tag == Iex_Binop 
//..        && (e->Iex.Binop.op == Iop_CmpEQ8
//..            || e->Iex.Binop.op == Iop_CmpNE8)) {
//..       HReg    r1   = iselIntExpr_R(env, e->Iex.Binop.arg1);
//..       X86RMI* rmi2 = iselIntExpr_RMI(env, e->Iex.Binop.arg2);
//..       HReg    r    = newVRegI(env);
//..       addInstr(env, mk_iMOVsd_RR(r1,r));
//..       addInstr(env, X86Instr_Alu32R(Xalu_XOR,rmi2,r));
//..       addInstr(env, X86Instr_Alu32R(Xalu_AND,X86RMI_Imm(0xFF),r));
//..       switch (e->Iex.Binop.op) {
//..          case Iop_CmpEQ8:  return Xcc_Z;
//..          case Iop_CmpNE8:  return Xcc_NZ;
//..          default: vpanic("iselCondCode(x86): CmpXX8");
//..       }
//..    }
//.. 
//..    /* CmpEQ16 / CmpNE16 */
//..    if (e->tag == Iex_Binop 
//..        && (e->Iex.Binop.op == Iop_CmpEQ16
//..            || e->Iex.Binop.op == Iop_CmpNE16)) {
//..       HReg    r1   = iselIntExpr_R(env, e->Iex.Binop.arg1);
//..       X86RMI* rmi2 = iselIntExpr_RMI(env, e->Iex.Binop.arg2);
//..       HReg    r    = newVRegI(env);
//..       addInstr(env, mk_iMOVsd_RR(r1,r));
//..       addInstr(env, X86Instr_Alu32R(Xalu_XOR,rmi2,r));
//..       addInstr(env, X86Instr_Alu32R(Xalu_AND,X86RMI_Imm(0xFFFF),r));
//..       switch (e->Iex.Binop.op) {
//..          case Iop_CmpEQ16:  return Xcc_Z;
//..          case Iop_CmpNE16:  return Xcc_NZ;
//..          default: vpanic("iselCondCode(x86): CmpXX16");
//..       }
//..    }
//.. 
//..    /* CmpNE32(1Sto32(b), 0) ==> b */
//..    {
//..       DECLARE_PATTERN(p_CmpNE32_1Sto32);
//..       DEFINE_PATTERN(
//..          p_CmpNE32_1Sto32,
//..          binop(Iop_CmpNE32, unop(Iop_1Sto32,bind(0)), mkU32(0)));
//..       if (matchIRExpr(&mi, p_CmpNE32_1Sto32, e)) {
//..          return iselCondCode(env, mi.bindee[0]);
//..       }
//..    }

   /* Cmp*64*(x,y) */
   if (e->tag == Iex_Binop 
       && (e->Iex.Binop.op == Iop_CmpEQ64
           || e->Iex.Binop.op == Iop_CmpNE64
           //|| e->Iex.Binop.op == Iop_CmpLT64S
           //|| e->Iex.Binop.op == Iop_CmpLT64U
           //|| e->Iex.Binop.op == Iop_CmpLE64S
           //|| e->Iex.Binop.op == Iop_CmpLE64U
          )) {
      HReg      r1   = iselIntExpr_R(env, e->Iex.Binop.arg1);
      AMD64RMI* rmi2 = iselIntExpr_RMI(env, e->Iex.Binop.arg2);
      addInstr(env, AMD64Instr_Alu64R(Aalu_CMP,rmi2,r1));
      switch (e->Iex.Binop.op) {
         case Iop_CmpEQ64:  return Acc_Z;
         case Iop_CmpNE64:  return Acc_NZ;
	   //case Iop_CmpLT64S: return Acc_L;
	   //case Iop_CmpLT64U: return Acc_B;
	   //case Iop_CmpLE64S: return Acc_LE;
	   //case Iop_CmpLE64U: return Acc_BE;
         default: vpanic("iselCondCode(amd64): CmpXX64");
      }
   }

//..    /* CmpNE64(1Sto64(b), 0) ==> b */
//..    {
//..       DECLARE_PATTERN(p_CmpNE64_1Sto64);
//..       DEFINE_PATTERN(
//..          p_CmpNE64_1Sto64,
//..          binop(Iop_CmpNE64, unop(Iop_1Sto64,bind(0)), mkU64(0)));
//..       if (matchIRExpr(&mi, p_CmpNE64_1Sto64, e)) {
//..          return iselCondCode(env, mi.bindee[0]);
//..       }
//..    }
//.. 
//..    /* CmpNE64(x, 0) */
//..    {
//..       DECLARE_PATTERN(p_CmpNE64_x_zero);
//..       DEFINE_PATTERN(
//..          p_CmpNE64_x_zero,
//..          binop(Iop_CmpNE64, bind(0), mkU64(0)) );
//..       if (matchIRExpr(&mi, p_CmpNE64_x_zero, e)) {
//..          HReg hi, lo;
//..          IRExpr* x   = mi.bindee[0];
//..          HReg    tmp = newVRegI(env);
//..          iselInt64Expr( &hi, &lo, env, x );
//..          addInstr(env, mk_iMOVsd_RR(hi, tmp));
//..          addInstr(env, X86Instr_Alu32R(Xalu_OR,X86RMI_Reg(lo), tmp));
//..          return Xcc_NZ;
//..       }
//..    }
//.. 
//..    /* CmpNE64 */
//..    if (e->tag == Iex_Binop 
//..        && e->Iex.Binop.op == Iop_CmpNE64) {
//..       HReg hi1, hi2, lo1, lo2;
//..       HReg tHi = newVRegI(env);
//..       HReg tLo = newVRegI(env);
//..       iselInt64Expr( &hi1, &lo1, env, e->Iex.Binop.arg1 );
//..       iselInt64Expr( &hi2, &lo2, env, e->Iex.Binop.arg2 );
//..       addInstr(env, mk_iMOVsd_RR(hi1, tHi));
//..       addInstr(env, X86Instr_Alu32R(Xalu_XOR,X86RMI_Reg(hi2), tHi));
//..       addInstr(env, mk_iMOVsd_RR(lo1, tLo));
//..       addInstr(env, X86Instr_Alu32R(Xalu_XOR,X86RMI_Reg(lo2), tLo));
//..       addInstr(env, X86Instr_Alu32R(Xalu_OR,X86RMI_Reg(tHi), tLo));
//..       switch (e->Iex.Binop.op) {
//..          case Iop_CmpNE64:  return Xcc_NZ;
//..          default: vpanic("iselCondCode(x86): CmpXX64");
//..       }
//..    }

   /* var */
   if (e->tag == Iex_Tmp) {
      HReg r64 = lookupIRTemp(env, e->Iex.Tmp.tmp);
      HReg dst = newVRegI(env);
      addInstr(env, mk_iMOVsd_RR(r64,dst));
      addInstr(env, AMD64Instr_Alu64R(Aalu_AND,AMD64RMI_Imm(1),dst));
      return Acc_NZ;
   }

   ppIRExpr(e);
   vpanic("iselCondCode(amd64)");
}


/*---------------------------------------------------------*/
/*--- ISEL: Integer expressions (128 bit)               ---*/
/*---------------------------------------------------------*/

/* Compute a 128-bit value into a register pair, which is returned as
   the first two parameters.  As with iselIntExpr_R, these may be
   either real or virtual regs; in any case they must not be changed
   by subsequent code emitted by the caller.  */

static void iselInt128Expr ( HReg* rHi, HReg* rLo, 
                             ISelEnv* env, IRExpr* e )
{
   iselInt128Expr_wrk(rHi, rLo, env, e);
#  if 0
   vex_printf("\n"); ppIRExpr(e); vex_printf("\n");
#  endif
   vassert(hregClass(*rHi) == HRcInt64);
   vassert(hregIsVirtual(*rHi));
   vassert(hregClass(*rLo) == HRcInt64);
   vassert(hregIsVirtual(*rLo));
}

/* DO NOT CALL THIS DIRECTLY ! */
static void iselInt128Expr_wrk ( HReg* rHi, HReg* rLo, 
                                 ISelEnv* env, IRExpr* e )
{
//..    HWord fn = 0; /* helper fn for most SIMD64 stuff */
   vassert(e);
   vassert(typeOfIRExpr(env->type_env,e) == Ity_I128);

//..    /* 64-bit literal */
//..    if (e->tag == Iex_Const) {
//..       ULong w64 = e->Iex.Const.con->Ico.U64;
//..       UInt  wHi = ((UInt)(w64 >> 32)) & 0xFFFFFFFF;
//..       UInt  wLo = ((UInt)w64) & 0xFFFFFFFF;
//..       HReg  tLo = newVRegI(env);
//..       HReg  tHi = newVRegI(env);
//..       vassert(e->Iex.Const.con->tag == Ico_U64);
//..       addInstr(env, X86Instr_Alu32R(Xalu_MOV, X86RMI_Imm(wHi), tHi));
//..       addInstr(env, X86Instr_Alu32R(Xalu_MOV, X86RMI_Imm(wLo), tLo));
//..       *rHi = tHi;
//..       *rLo = tLo;
//..       return;
//..    }

   /* read 128-bit IRTemp */
   if (e->tag == Iex_Tmp) {
      lookupIRTemp128( rHi, rLo, env, e->Iex.Tmp.tmp);
      return;
   }
 
//..    /* 64-bit load */
//..    if (e->tag == Iex_LDle) {
//..       HReg     tLo, tHi;
//..       X86AMode *am0, *am4;
//..       vassert(e->Iex.LDle.ty == Ity_I64);
//..       tLo = newVRegI(env);
//..       tHi = newVRegI(env);
//..       am0 = iselIntExpr_AMode(env, e->Iex.LDle.addr);
//..       am4 = advance4(am0);
//..       addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(am0), tLo ));
//..       addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(am4), tHi ));
//..       *rHi = tHi;
//..       *rLo = tLo;
//..       return;
//..    }
//.. 
//..    /* 64-bit GET */
//..    if (e->tag == Iex_Get) {
//..       X86AMode* am  = X86AMode_IR(e->Iex.Get.offset, hregX86_EBP());
//..       X86AMode* am4 = advance4(am);
//..       HReg tLo = newVRegI(env);
//..       HReg tHi = newVRegI(env);
//..       addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(am), tLo ));
//..       addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(am4), tHi ));
//..       *rHi = tHi;
//..       *rLo = tLo;
//..       return;
//..    }
//.. 
//..    /* 64-bit GETI */
//..    if (e->tag == Iex_GetI) {
//..       X86AMode* am 
//..          = genGuestArrayOffset( env, e->Iex.GetI.descr, 
//..                                      e->Iex.GetI.ix, e->Iex.GetI.bias );
//..       X86AMode* am4 = advance4(am);
//..       HReg tLo = newVRegI(env);
//..       HReg tHi = newVRegI(env);
//..       addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(am), tLo ));
//..       addInstr(env, X86Instr_Alu32R( Xalu_MOV, X86RMI_Mem(am4), tHi ));
//..       *rHi = tHi;
//..       *rLo = tLo;
//..       return;
//..    }
//.. 
//..    /* 64-bit Mux0X */
//..    if (e->tag == Iex_Mux0X) {
//..       HReg e0Lo, e0Hi, eXLo, eXHi, r8;
//..       HReg tLo = newVRegI(env);
//..       HReg tHi = newVRegI(env);
//..       iselInt64Expr(&e0Hi, &e0Lo, env, e->Iex.Mux0X.expr0);
//..       iselInt64Expr(&eXHi, &eXLo, env, e->Iex.Mux0X.exprX);
//..       addInstr(env, mk_iMOVsd_RR(eXHi, tHi));
//..       addInstr(env, mk_iMOVsd_RR(eXLo, tLo));
//..       r8 = iselIntExpr_R(env, e->Iex.Mux0X.cond);
//..       addInstr(env, X86Instr_Test32(X86RI_Imm(0xFF), X86RM_Reg(r8)));
//..       /* This assumes the first cmov32 doesn't trash the condition
//..          codes, so they are still available for the second cmov32 */
//..       addInstr(env, X86Instr_CMov32(Xcc_Z,X86RM_Reg(e0Hi),tHi));
//..       addInstr(env, X86Instr_CMov32(Xcc_Z,X86RM_Reg(e0Lo),tLo));
//..       *rHi = tHi;
//..       *rLo = tLo;
//..       return;
//..    }

   /* --------- BINARY ops --------- */
   if (e->tag == Iex_Binop) {
      switch (e->Iex.Binop.op) {
         /* 64 x 64 -> 128 multiply */
         case Iop_MullU64:
         case Iop_MullS64: {
            /* get one operand into %rax, and the other into a R/M.
               Need to make an educated guess about which is better in
               which. */
            HReg     tLo    = newVRegI(env);
            HReg     tHi    = newVRegI(env);
            Bool     syned  = toBool(e->Iex.Binop.op == Iop_MullS64);
            AMD64RM* rmLeft = iselIntExpr_RM(env, e->Iex.Binop.arg1);
            HReg     rRight = iselIntExpr_R(env, e->Iex.Binop.arg2);
            addInstr(env, mk_iMOVsd_RR(rRight, hregAMD64_RAX()));
            addInstr(env, AMD64Instr_MulL(syned, 8, rmLeft));
            /* Result is now in RDX:RAX.  Tell the caller. */
            addInstr(env, mk_iMOVsd_RR(hregAMD64_RDX(), tHi));
            addInstr(env, mk_iMOVsd_RR(hregAMD64_RAX(), tLo));
            *rHi = tHi;
            *rLo = tLo;
            return;
         }

         /* 128 x 64 -> (64(rem),64(div)) division */
         case Iop_DivModU128to64:
         case Iop_DivModS128to64: {
            /* Get the 128-bit operand into rdx:rax, and the other into
               any old R/M. */
            HReg sHi, sLo;
            HReg     tLo     = newVRegI(env);
            HReg     tHi     = newVRegI(env);
            Bool     syned   = toBool(e->Iex.Binop.op == Iop_DivModS128to64);
            AMD64RM* rmRight = iselIntExpr_RM(env, e->Iex.Binop.arg2);
            iselInt128Expr(&sHi,&sLo, env, e->Iex.Binop.arg1);
            addInstr(env, mk_iMOVsd_RR(sHi, hregAMD64_RDX()));
            addInstr(env, mk_iMOVsd_RR(sLo, hregAMD64_RAX()));
            addInstr(env, AMD64Instr_Div(syned, 8, rmRight));
            addInstr(env, mk_iMOVsd_RR(hregAMD64_RDX(), tHi));
            addInstr(env, mk_iMOVsd_RR(hregAMD64_RAX(), tLo));
            *rHi = tHi;
            *rLo = tLo;
            return;
         }

         /* 64HLto128(e1,e2) */
         case Iop_64HLto128:
            *rHi = iselIntExpr_R(env, e->Iex.Binop.arg1);
            *rLo = iselIntExpr_R(env, e->Iex.Binop.arg2);
            return;

//..          /* Or64/And64/Xor64 */
//..          case Iop_Or64:
//..          case Iop_And64:
//..          case Iop_Xor64: {
//..             HReg xLo, xHi, yLo, yHi;
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             X86AluOp op = e->Iex.Binop.op==Iop_Or64 ? Xalu_OR
//..                           : e->Iex.Binop.op==Iop_And64 ? Xalu_AND
//..                           : Xalu_XOR;
//..             iselInt64Expr(&xHi, &xLo, env, e->Iex.Binop.arg1);
//..             addInstr(env, mk_iMOVsd_RR(xHi, tHi));
//..             addInstr(env, mk_iMOVsd_RR(xLo, tLo));
//..             iselInt64Expr(&yHi, &yLo, env, e->Iex.Binop.arg2);
//..             addInstr(env, X86Instr_Alu32R(op, X86RMI_Reg(yHi), tHi));
//..             addInstr(env, X86Instr_Alu32R(op, X86RMI_Reg(yLo), tLo));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          /* Add64/Sub64 */
//..          case Iop_Add64:
//..          case Iop_Sub64: {
//..             HReg xLo, xHi, yLo, yHi;
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             iselInt64Expr(&xHi, &xLo, env, e->Iex.Binop.arg1);
//..             addInstr(env, mk_iMOVsd_RR(xHi, tHi));
//..             addInstr(env, mk_iMOVsd_RR(xLo, tLo));
//..             iselInt64Expr(&yHi, &yLo, env, e->Iex.Binop.arg2);
//..             if (e->Iex.Binop.op==Iop_Add64) {
//..                addInstr(env, X86Instr_Alu32R(Xalu_ADD, X86RMI_Reg(yLo), tLo));
//..                addInstr(env, X86Instr_Alu32R(Xalu_ADC, X86RMI_Reg(yHi), tHi));
//..             } else {
//..                addInstr(env, X86Instr_Alu32R(Xalu_SUB, X86RMI_Reg(yLo), tLo));
//..                addInstr(env, X86Instr_Alu32R(Xalu_SBB, X86RMI_Reg(yHi), tHi));
//..             }
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          /* 32HLto64(e1,e2) */
//..          case Iop_32HLto64:
//..             *rHi = iselIntExpr_R(env, e->Iex.Binop.arg1);
//..             *rLo = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..             return;
//.. 
//..          /* 64-bit shifts */
//..          case Iop_Shl64: {
//..             /* We use the same ingenious scheme as gcc.  Put the value
//..                to be shifted into %hi:%lo, and the shift amount into
//..                %cl.  Then (dsts on right, a la ATT syntax):
//..  
//..                shldl %cl, %lo, %hi   -- make %hi be right for the
//..                                      -- shift amt %cl % 32
//..                shll  %cl, %lo        -- make %lo be right for the
//..                                      -- shift amt %cl % 32
//.. 
//..                Now, if (shift amount % 64) is in the range 32 .. 63,
//..                we have to do a fixup, which puts the result low half
//..                into the result high half, and zeroes the low half:
//.. 
//..                testl $32, %ecx
//.. 
//..                cmovnz %lo, %hi
//..                movl $0, %tmp         -- sigh; need yet another reg
//..                cmovnz %tmp, %lo 
//..             */
//..             HReg rAmt, sHi, sLo, tHi, tLo, tTemp;
//..             tLo = newVRegI(env);
//..             tHi = newVRegI(env);
//..             tTemp = newVRegI(env);
//..             rAmt = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..             iselInt64Expr(&sHi,&sLo, env, e->Iex.Binop.arg1);
//..             addInstr(env, mk_iMOVsd_RR(rAmt, hregX86_ECX()));
//..             addInstr(env, mk_iMOVsd_RR(sHi, tHi));
//..             addInstr(env, mk_iMOVsd_RR(sLo, tLo));
//..             /* Ok.  Now shift amt is in %ecx, and value is in tHi/tLo
//..                and those regs are legitimately modifiable. */
//..             addInstr(env, X86Instr_Sh3232(Xsh_SHL, 0/*%cl*/, tLo, tHi));
//..             addInstr(env, X86Instr_Sh32(Xsh_SHL, 0/*%cl*/, X86RM_Reg(tLo)));
//..             addInstr(env, X86Instr_Test32(X86RI_Imm(32), 
//..                           X86RM_Reg(hregX86_ECX())));
//..             addInstr(env, X86Instr_CMov32(Xcc_NZ, X86RM_Reg(tLo), tHi));
//..             addInstr(env, X86Instr_Alu32R(Xalu_MOV, X86RMI_Imm(0), tTemp));
//..             addInstr(env, X86Instr_CMov32(Xcc_NZ, X86RM_Reg(tTemp), tLo));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          case Iop_Shr64: {
//..             /* We use the same ingenious scheme as gcc.  Put the value
//..                to be shifted into %hi:%lo, and the shift amount into
//..                %cl.  Then:
//..  
//..                shrdl %cl, %hi, %lo   -- make %lo be right for the
//..                                      -- shift amt %cl % 32
//..                shrl  %cl, %hi        -- make %hi be right for the
//..                                      -- shift amt %cl % 32
//.. 
//..                Now, if (shift amount % 64) is in the range 32 .. 63,
//..                we have to do a fixup, which puts the result high half
//..                into the result low half, and zeroes the high half:
//.. 
//..                testl $32, %ecx
//.. 
//..                cmovnz %hi, %lo
//..                movl $0, %tmp         -- sigh; need yet another reg
//..                cmovnz %tmp, %hi
//..             */
//..             HReg rAmt, sHi, sLo, tHi, tLo, tTemp;
//..             tLo = newVRegI(env);
//..             tHi = newVRegI(env);
//..             tTemp = newVRegI(env);
//..             rAmt = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..             iselInt64Expr(&sHi,&sLo, env, e->Iex.Binop.arg1);
//..             addInstr(env, mk_iMOVsd_RR(rAmt, hregX86_ECX()));
//..             addInstr(env, mk_iMOVsd_RR(sHi, tHi));
//..             addInstr(env, mk_iMOVsd_RR(sLo, tLo));
//..             /* Ok.  Now shift amt is in %ecx, and value is in tHi/tLo
//..                and those regs are legitimately modifiable. */
//..             addInstr(env, X86Instr_Sh3232(Xsh_SHR, 0/*%cl*/, tHi, tLo));
//..             addInstr(env, X86Instr_Sh32(Xsh_SHR, 0/*%cl*/, X86RM_Reg(tHi)));
//..             addInstr(env, X86Instr_Test32(X86RI_Imm(32), 
//..                           X86RM_Reg(hregX86_ECX())));
//..             addInstr(env, X86Instr_CMov32(Xcc_NZ, X86RM_Reg(tHi), tLo));
//..             addInstr(env, X86Instr_Alu32R(Xalu_MOV, X86RMI_Imm(0), tTemp));
//..             addInstr(env, X86Instr_CMov32(Xcc_NZ, X86RM_Reg(tTemp), tHi));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          /* F64 -> I64 */
//..          /* Sigh, this is an almost exact copy of the F64 -> I32/I16
//..             case.  Unfortunately I see no easy way to avoid the
//..             duplication. */
//..          case Iop_F64toI64: {
//..             HReg rf  = iselDblExpr(env, e->Iex.Binop.arg2);
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//.. 
//..             /* Used several times ... */
//..             /* Careful ... this sharing is only safe because
//.. 	       zero_esp/four_esp do not hold any registers which the
//.. 	       register allocator could attempt to swizzle later. */
//..             X86AMode* zero_esp = X86AMode_IR(0, hregX86_ESP());
//..             X86AMode* four_esp = X86AMode_IR(4, hregX86_ESP());
//.. 
//..             /* rf now holds the value to be converted, and rrm holds
//..                the rounding mode value, encoded as per the
//..                IRRoundingMode enum.  The first thing to do is set the
//..                FPU's rounding mode accordingly. */
//.. 
//..             /* Create a space for the format conversion. */
//..             /* subl $8, %esp */
//..             sub_from_esp(env, 8);
//.. 
//..             /* Set host rounding mode */
//..             set_FPU_rounding_mode( env, e->Iex.Binop.arg1 );
//.. 
//..             /* gistll %rf, 0(%esp) */
//..             addInstr(env, X86Instr_FpLdStI(False/*store*/, 8, rf, zero_esp));
//.. 
//..             /* movl 0(%esp), %dstLo */
//..             /* movl 4(%esp), %dstHi */
//..             addInstr(env, X86Instr_Alu32R(
//..                              Xalu_MOV, X86RMI_Mem(zero_esp), tLo));
//..             addInstr(env, X86Instr_Alu32R(
//..                              Xalu_MOV, X86RMI_Mem(four_esp), tHi));
//.. 
//..             /* Restore default FPU rounding. */
//..             set_FPU_rounding_default( env );
//.. 
//..             /* addl $8, %esp */
//..             add_to_esp(env, 8);
//.. 
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          case Iop_Add8x8:
//..             fn = (HWord)h_generic_calc_Add8x8; goto binnish;
//..          case Iop_Add16x4:
//..             fn = (HWord)h_generic_calc_Add16x4; goto binnish;
//..          case Iop_Add32x2:
//..             fn = (HWord)h_generic_calc_Add32x2; goto binnish;
//.. 
//..          case Iop_Avg8Ux8:
//..             fn = (HWord)h_generic_calc_Avg8Ux8; goto binnish;
//..          case Iop_Avg16Ux4:
//..             fn = (HWord)h_generic_calc_Avg16Ux4; goto binnish;
//.. 
//..          case Iop_CmpEQ8x8:
//..             fn = (HWord)h_generic_calc_CmpEQ8x8; goto binnish;
//..          case Iop_CmpEQ16x4:
//..             fn = (HWord)h_generic_calc_CmpEQ16x4; goto binnish;
//..          case Iop_CmpEQ32x2:
//..             fn = (HWord)h_generic_calc_CmpEQ32x2; goto binnish;
//.. 
//..          case Iop_CmpGT8Sx8:
//..             fn = (HWord)h_generic_calc_CmpGT8Sx8; goto binnish;
//..          case Iop_CmpGT16Sx4:
//..             fn = (HWord)h_generic_calc_CmpGT16Sx4; goto binnish;
//..          case Iop_CmpGT32Sx2:
//..             fn = (HWord)h_generic_calc_CmpGT32Sx2; goto binnish;
//.. 
//..          case Iop_InterleaveHI8x8:
//..             fn = (HWord)h_generic_calc_InterleaveHI8x8; goto binnish;
//..          case Iop_InterleaveLO8x8:
//..             fn = (HWord)h_generic_calc_InterleaveLO8x8; goto binnish;
//..          case Iop_InterleaveHI16x4:
//..             fn = (HWord)h_generic_calc_InterleaveHI16x4; goto binnish;
//..          case Iop_InterleaveLO16x4:
//..             fn = (HWord)h_generic_calc_InterleaveLO16x4; goto binnish;
//..          case Iop_InterleaveHI32x2:
//..             fn = (HWord)h_generic_calc_InterleaveHI32x2; goto binnish;
//..          case Iop_InterleaveLO32x2:
//..             fn = (HWord)h_generic_calc_InterleaveLO32x2; goto binnish;
//.. 
//..          case Iop_Max8Ux8:
//..             fn = (HWord)h_generic_calc_Max8Ux8; goto binnish;
//..          case Iop_Max16Sx4:
//..             fn = (HWord)h_generic_calc_Max16Sx4; goto binnish;
//..          case Iop_Min8Ux8:
//..             fn = (HWord)h_generic_calc_Min8Ux8; goto binnish;
//..          case Iop_Min16Sx4:
//..             fn = (HWord)h_generic_calc_Min16Sx4; goto binnish;
//.. 
//..          case Iop_Mul16x4:
//..             fn = (HWord)h_generic_calc_Mul16x4; goto binnish;
//..          case Iop_MulHi16Sx4:
//..             fn = (HWord)h_generic_calc_MulHi16Sx4; goto binnish;
//..          case Iop_MulHi16Ux4:
//..             fn = (HWord)h_generic_calc_MulHi16Ux4; goto binnish;
//.. 
//..          case Iop_QAdd8Sx8:
//..             fn = (HWord)h_generic_calc_QAdd8Sx8; goto binnish;
//..          case Iop_QAdd16Sx4:
//..             fn = (HWord)h_generic_calc_QAdd16Sx4; goto binnish;
//..          case Iop_QAdd8Ux8:
//..             fn = (HWord)h_generic_calc_QAdd8Ux8; goto binnish;
//..          case Iop_QAdd16Ux4:
//..             fn = (HWord)h_generic_calc_QAdd16Ux4; goto binnish;
//.. 
//..          case Iop_QNarrow32Sx2:
//..             fn = (HWord)h_generic_calc_QNarrow32Sx2; goto binnish;
//..          case Iop_QNarrow16Sx4:
//..             fn = (HWord)h_generic_calc_QNarrow16Sx4; goto binnish;
//..          case Iop_QNarrow16Ux4:
//..             fn = (HWord)h_generic_calc_QNarrow16Ux4; goto binnish;
//.. 
//..          case Iop_QSub8Sx8:
//..             fn = (HWord)h_generic_calc_QSub8Sx8; goto binnish;
//..          case Iop_QSub16Sx4:
//..             fn = (HWord)h_generic_calc_QSub16Sx4; goto binnish;
//..          case Iop_QSub8Ux8:
//..             fn = (HWord)h_generic_calc_QSub8Ux8; goto binnish;
//..          case Iop_QSub16Ux4:
//..             fn = (HWord)h_generic_calc_QSub16Ux4; goto binnish;
//.. 
//..          case Iop_Sub8x8:
//..             fn = (HWord)h_generic_calc_Sub8x8; goto binnish;
//..          case Iop_Sub16x4:
//..             fn = (HWord)h_generic_calc_Sub16x4; goto binnish;
//..          case Iop_Sub32x2:
//..             fn = (HWord)h_generic_calc_Sub32x2; goto binnish;
//.. 
//..          binnish: {
//..             /* Note: the following assumes all helpers are of
//..                signature 
//..                   ULong fn ( ULong, ULong ), and they are
//..                not marked as regparm functions. 
//..             */
//..             HReg xLo, xHi, yLo, yHi;
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             iselInt64Expr(&yHi, &yLo, env, e->Iex.Binop.arg2);
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(yHi)));
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(yLo)));
//..             iselInt64Expr(&xHi, &xLo, env, e->Iex.Binop.arg1);
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(xHi)));
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(xLo)));
//..             addInstr(env, X86Instr_Call( Xcc_ALWAYS, (UInt)fn, 0 ));
//..             add_to_esp(env, 4*4);
//..             addInstr(env, mk_iMOVsd_RR(hregX86_EDX(), tHi));
//..             addInstr(env, mk_iMOVsd_RR(hregX86_EAX(), tLo));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          case Iop_ShlN32x2:
//..             fn = (HWord)h_generic_calc_ShlN32x2; goto shifty;
//..          case Iop_ShlN16x4:
//..             fn = (HWord)h_generic_calc_ShlN16x4; goto shifty;
//..          case Iop_ShrN32x2:
//..             fn = (HWord)h_generic_calc_ShrN32x2; goto shifty;
//..          case Iop_ShrN16x4:
//..             fn = (HWord)h_generic_calc_ShrN16x4; goto shifty;
//..          case Iop_SarN32x2:
//..             fn = (HWord)h_generic_calc_SarN32x2; goto shifty;
//..          case Iop_SarN16x4:
//..             fn = (HWord)h_generic_calc_SarN16x4; goto shifty;
//..          shifty: {
//..             /* Note: the following assumes all helpers are of
//..                signature 
//..                   ULong fn ( ULong, UInt ), and they are
//..                not marked as regparm functions. 
//..             */
//..             HReg xLo, xHi;
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             X86RMI* y = iselIntExpr_RMI(env, e->Iex.Binop.arg2);
//..             addInstr(env, X86Instr_Push(y));
//..             iselInt64Expr(&xHi, &xLo, env, e->Iex.Binop.arg1);
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(xHi)));
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(xLo)));
//..             addInstr(env, X86Instr_Call( Xcc_ALWAYS, (UInt)fn, 0 ));
//..             add_to_esp(env, 3*4);
//..             addInstr(env, mk_iMOVsd_RR(hregX86_EDX(), tHi));
//..             addInstr(env, mk_iMOVsd_RR(hregX86_EAX(), tLo));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }

         default: 
            break;
      }
   } /* if (e->tag == Iex_Binop) */


//..    /* --------- UNARY ops --------- */
//..    if (e->tag == Iex_Unop) {
//..       switch (e->Iex.Unop.op) {
//.. 
//..          /* 32Sto64(e) */
//..          case Iop_32Sto64: {
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
//..             addInstr(env, mk_iMOVsd_RR(src,tHi));
//..             addInstr(env, mk_iMOVsd_RR(src,tLo));
//..             addInstr(env, X86Instr_Sh32(Xsh_SAR, 31, X86RM_Reg(tHi)));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          /* 32Uto64(e) */
//..          case Iop_32Uto64: {
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
//..             addInstr(env, mk_iMOVsd_RR(src,tLo));
//..             addInstr(env, X86Instr_Alu32R(Xalu_MOV, X86RMI_Imm(0), tHi));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }

//..          /* could do better than this, but for now ... */
//..          case Iop_1Sto64: {
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             X86CondCode cond = iselCondCode(env, e->Iex.Unop.arg);
//..             addInstr(env, X86Instr_Set32(cond,tLo));
//..             addInstr(env, X86Instr_Sh32(Xsh_SHL, 31, X86RM_Reg(tLo)));
//..             addInstr(env, X86Instr_Sh32(Xsh_SAR, 31, X86RM_Reg(tLo)));
//..             addInstr(env, mk_iMOVsd_RR(tLo, tHi));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          /* Not64(e) */
//..          case Iop_Not64: {
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             HReg sHi, sLo;
//..             iselInt64Expr(&sHi, &sLo, env, e->Iex.Unop.arg);
//..             addInstr(env, mk_iMOVsd_RR(sHi, tHi));
//..             addInstr(env, mk_iMOVsd_RR(sLo, tLo));
//..             addInstr(env, X86Instr_Unary32(Xun_NOT,X86RM_Reg(tHi)));
//..             addInstr(env, X86Instr_Unary32(Xun_NOT,X86RM_Reg(tLo)));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          case Iop_CmpNEZ32x2:
//..             fn = (HWord)h_generic_calc_CmpNEZ32x2; goto unish;
//..          case Iop_CmpNEZ16x4:
//..             fn = (HWord)h_generic_calc_CmpNEZ16x4; goto unish;
//..          case Iop_CmpNEZ8x8:
//..             fn = (HWord)h_generic_calc_CmpNEZ8x8; goto unish;
//..          unish: {
//..             /* Note: the following assumes all helpers are of
//..                signature 
//..                   ULong fn ( ULong ), and they are
//..                not marked as regparm functions. 
//..             */
//..             HReg xLo, xHi;
//..             HReg tLo = newVRegI(env);
//..             HReg tHi = newVRegI(env);
//..             iselInt64Expr(&xHi, &xLo, env, e->Iex.Unop.arg);
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(xHi)));
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(xLo)));
//..             addInstr(env, X86Instr_Call( Xcc_ALWAYS, (UInt)fn, 0 ));
//..             add_to_esp(env, 2*4);
//..             addInstr(env, mk_iMOVsd_RR(hregX86_EDX(), tHi));
//..             addInstr(env, mk_iMOVsd_RR(hregX86_EAX(), tLo));
//..             *rHi = tHi;
//..             *rLo = tLo;
//..             return;
//..          }
//.. 
//..          default: 
//..             break;
//..       }
//..    } /* if (e->tag == Iex_Unop) */
//.. 
//.. 
//..    /* --------- CCALL --------- */
//..    if (e->tag == Iex_CCall) {
//..       HReg tLo = newVRegI(env);
//..       HReg tHi = newVRegI(env);
//.. 
//..       /* Marshal args, do the call, clear stack. */
//..       doHelperCall( env, False, NULL, e->Iex.CCall.cee, e->Iex.CCall.args );
//.. 
//..       addInstr(env, mk_iMOVsd_RR(hregX86_EDX(), tHi));
//..       addInstr(env, mk_iMOVsd_RR(hregX86_EAX(), tLo));
//..       *rHi = tHi;
//..       *rLo = tLo;
//..       return;
//..    }

   ppIRExpr(e);
   vpanic("iselInt128Expr");
}


/*---------------------------------------------------------*/
/*--- ISEL: Floating point expressions (32 bit)         ---*/
/*---------------------------------------------------------*/

/* Nothing interesting here; really just wrappers for
   64-bit stuff. */

static HReg iselFltExpr ( ISelEnv* env, IRExpr* e )
{
   HReg r = iselFltExpr_wrk( env, e );
#  if 0
   vex_printf("\n"); ppIRExpr(e); vex_printf("\n");
#  endif
   vassert(hregClass(r) == HRcVec128);
   vassert(hregIsVirtual(r));
   return r;
}

/* DO NOT CALL THIS DIRECTLY */
static HReg iselFltExpr_wrk ( ISelEnv* env, IRExpr* e )
{
   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(ty == Ity_F32);

   if (e->tag == Iex_Tmp) {
      return lookupIRTemp(env, e->Iex.Tmp.tmp);
   }

   if (e->tag == Iex_LDle) {
      AMD64AMode* am;
      HReg res = newVRegV(env);
      vassert(e->Iex.LDle.ty == Ity_F32);
      am = iselIntExpr_AMode(env, e->Iex.LDle.addr);
      addInstr(env, AMD64Instr_SseLdSt(True/*load*/, 4, res, am));
      return res;
   }

   if (e->tag == Iex_Binop
       && e->Iex.Binop.op == Iop_F64toF32) {
      /* Although the result is still held in a standard SSE register,
         we need to round it to reflect the loss of accuracy/range
         entailed in casting it to a 32-bit float. */
      HReg dst = newVRegV(env);
      HReg src = iselDblExpr(env, e->Iex.Binop.arg2);
      set_SSE_rounding_mode( env, e->Iex.Binop.arg1 );
      addInstr(env, AMD64Instr_SseSDSS(True/*D->S*/,src,dst));
      set_SSE_rounding_default( env );
      return dst;
   }

   if (e->tag == Iex_Get) {
      AMD64AMode* am = AMD64AMode_IR( e->Iex.Get.offset,
                                       hregAMD64_RBP() );
      HReg res = newVRegV(env);
      addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 4, res, am ));
      return res;
   }

//..    if (e->tag == Iex_Unop
//..        && e->Iex.Unop.op == Iop_ReinterpI32asF32) {
//..        /* Given an I32, produce an IEEE754 float with the same bit
//..           pattern. */
//..       HReg    dst = newVRegF(env);
//..       X86RMI* rmi = iselIntExpr_RMI(env, e->Iex.Unop.arg);
//..       /* paranoia */
//..       addInstr(env, X86Instr_Push(rmi));
//..       addInstr(env, X86Instr_FpLdSt(
//..                        True/*load*/, 4, dst, 
//..                        X86AMode_IR(0, hregX86_ESP())));
//..       add_to_esp(env, 4);
//..       return dst;
//..    }

   ppIRExpr(e);
   vpanic("iselFltExpr_wrk");
}


/*---------------------------------------------------------*/
/*--- ISEL: Floating point expressions (64 bit)         ---*/
/*---------------------------------------------------------*/

/* Compute a 64-bit floating point value into the lower half of an xmm
   register, the identity of which is returned.  As with
   iselIntExpr_R, the returned reg will be virtual, and it must not be
   changed by subsequent code emitted by the caller.
*/

/* IEEE 754 formats.  From http://www.freesoft.org/CIE/RFC/1832/32.htm:

    Type                  S (1 bit)   E (11 bits)   F (52 bits)
    ----                  ---------   -----------   -----------
    signalling NaN        u           2047 (max)    .0uuuuu---u
                                                    (with at least
                                                     one 1 bit)
    quiet NaN             u           2047 (max)    .1uuuuu---u

    negative infinity     1           2047 (max)    .000000---0

    positive infinity     0           2047 (max)    .000000---0

    negative zero         1           0             .000000---0

    positive zero         0           0             .000000---0
*/

static HReg iselDblExpr ( ISelEnv* env, IRExpr* e )
{
   HReg r = iselDblExpr_wrk( env, e );
#  if 0
   vex_printf("\n"); ppIRExpr(e); vex_printf("\n");
#  endif
   vassert(hregClass(r) == HRcVec128);
   vassert(hregIsVirtual(r));
   return r;
}

/* DO NOT CALL THIS DIRECTLY */
static HReg iselDblExpr_wrk ( ISelEnv* env, IRExpr* e )
{
   IRType ty = typeOfIRExpr(env->type_env,e);
   vassert(e);
   vassert(ty == Ity_F64);

   if (e->tag == Iex_Tmp) {
      return lookupIRTemp(env, e->Iex.Tmp.tmp);
   }

   if (e->tag == Iex_Const) {
      union { ULong u64; Double f64; } u;
      HReg res = newVRegV(env);
      HReg tmp = newVRegI(env);
      vassert(sizeof(u) == 8);
      vassert(sizeof(u.u64) == 8);
      vassert(sizeof(u.f64) == 8);

      if (e->Iex.Const.con->tag == Ico_F64) {
         u.f64 = e->Iex.Const.con->Ico.F64;
      }
      else if (e->Iex.Const.con->tag == Ico_F64i) {
         u.u64 = e->Iex.Const.con->Ico.F64i;
      }
      else
         vpanic("iselDblExpr(amd64): const");

      addInstr(env, AMD64Instr_Imm64(u.u64, tmp));
      addInstr(env, AMD64Instr_Push(AMD64RMI_Reg(tmp)));
      addInstr(env, AMD64Instr_SseLdSt(
                       True/*load*/, 8, res, 
                       AMD64AMode_IR(0, hregAMD64_RSP())
              ));
      add_to_rsp(env, 8);
      return res;
   }

   if (e->tag == Iex_LDle) {
      AMD64AMode* am;
      HReg res = newVRegV(env);
      vassert(e->Iex.LDle.ty == Ity_F64);
      am = iselIntExpr_AMode(env, e->Iex.LDle.addr);
      addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 8, res, am ));
      return res;
   }

   if (e->tag == Iex_Get) {
      AMD64AMode* am = AMD64AMode_IR( e->Iex.Get.offset,
                                      hregAMD64_RBP() );
      HReg res = newVRegV(env);
      addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 8, res, am ));
      return res;
   }

   if (e->tag == Iex_GetI) {
      AMD64AMode* am 
         = genGuestArrayOffset(
              env, e->Iex.GetI.descr, 
                   e->Iex.GetI.ix, e->Iex.GetI.bias );
      HReg res = newVRegV(env);
      addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 8, res, am ));
      return res;
   }

   if (e->tag == Iex_Binop) {
      AMD64SseOp op = Asse_INVALID;
      switch (e->Iex.Binop.op) {
         case Iop_AddF64: op = Asse_ADDF; break;
         case Iop_SubF64: op = Asse_SUBF; break;
         case Iop_MulF64: op = Asse_MULF; break;
         case Iop_DivF64: op = Asse_DIVF; break;
         default: break;
      }
      if (op != Asse_INVALID) {
         HReg dst  = newVRegV(env);
         HReg argL = iselDblExpr(env, e->Iex.Binop.arg1);
         HReg argR = iselDblExpr(env, e->Iex.Binop.arg2);
         addInstr(env, mk_vMOVsd_RR(argL, dst));
         addInstr(env, AMD64Instr_Sse64FLo(op, argR, dst));
         return dst;
      }
   }

//..    if (e->tag == Iex_Binop) {
//..       X86FpOp fpop = Xfp_INVALID;
//..       switch (e->Iex.Binop.op) {
//..          case Iop_AddF64:    fpop = Xfp_ADD; break;
//..          case Iop_SubF64:    fpop = Xfp_SUB; break;
//..          case Iop_MulF64:    fpop = Xfp_MUL; break;
//..          case Iop_DivF64:    fpop = Xfp_DIV; break;
//..          case Iop_ScaleF64:  fpop = Xfp_SCALE; break;
//..          case Iop_AtanF64:   fpop = Xfp_ATAN; break;
//..          case Iop_Yl2xF64:   fpop = Xfp_YL2X; break;
//..          case Iop_Yl2xp1F64: fpop = Xfp_YL2XP1; break;
//..          case Iop_PRemF64:   fpop = Xfp_PREM; break;
//..          case Iop_PRem1F64:  fpop = Xfp_PREM1; break;
//..          default: break;
//..       }
//..       if (fpop != Xfp_INVALID) {
//..          HReg res  = newVRegF(env);
//..          HReg srcL = iselDblExpr(env, e->Iex.Binop.arg1);
//..          HReg srcR = iselDblExpr(env, e->Iex.Binop.arg2);
//..          addInstr(env, X86Instr_FpBinary(fpop,srcL,srcR,res));
//.. 	 if (fpop != Xfp_ADD && fpop != Xfp_SUB 
//.. 	     && fpop != Xfp_MUL && fpop != Xfp_DIV)
//..             roundToF64(env, res);
//..          return res;
//..       }
//..    }
//.. 
//..    if (e->tag == Iex_Binop && e->Iex.Binop.op == Iop_RoundF64) {
//..       HReg rf  = iselDblExpr(env, e->Iex.Binop.arg2);
//..       HReg dst = newVRegF(env);
//.. 
//..       /* rf now holds the value to be rounded.  The first thing to do
//..          is set the FPU's rounding mode accordingly. */
//.. 
//..       /* Set host rounding mode */
//..       set_FPU_rounding_mode( env, e->Iex.Binop.arg1 );
//.. 
//..       /* grndint %rf, %dst */
//..       addInstr(env, X86Instr_FpUnary(Xfp_ROUND, rf, dst));
//.. 
//..       /* Restore default FPU rounding. */
//..       set_FPU_rounding_default( env );
//.. 
//..       return dst;
//..    }

   if (e->tag == Iex_Binop && e->Iex.Binop.op == Iop_I64toF64) {
      HReg dst = newVRegV(env);
      HReg src = iselIntExpr_R(env, e->Iex.Binop.arg2);
      set_SSE_rounding_mode( env, e->Iex.Binop.arg1 );
      addInstr(env, AMD64Instr_SseSI2SF( 8, 8, src, dst ));
      set_SSE_rounding_default( env );
      return dst;
   }

   if (e->tag == Iex_Unop && e->Iex.Unop.op == Iop_I32toF64) {
      HReg dst = newVRegV(env);
      HReg src = iselIntExpr_R(env, e->Iex.Unop.arg);
      set_SSE_rounding_default( env );
      addInstr(env, AMD64Instr_SseSI2SF( 4, 8, src, dst ));
      return dst;
   }

   if (e->tag == Iex_Unop 
       && (e->Iex.Unop.op == Iop_NegF64
           || e->Iex.Unop.op == Iop_AbsF64)) {
      /* Sigh ... very rough code.  Could do much better. */
      /* Get the 128-bit literal 00---0 10---0 into a register
         and xor/nand it with the value to be negated. */
      HReg r1  = newVRegI(env);
      HReg dst = newVRegV(env);
      HReg tmp = newVRegV(env);
      HReg src = iselDblExpr(env, e->Iex.Unop.arg);
      AMD64AMode* rsp0 = AMD64AMode_IR(0, hregAMD64_RSP());
      addInstr(env, mk_vMOVsd_RR(src,tmp));
      addInstr(env, AMD64Instr_Push(AMD64RMI_Imm(0)));
      addInstr(env, AMD64Instr_Imm64( 1ULL<<63, r1 ));
      addInstr(env, AMD64Instr_Push(AMD64RMI_Reg(r1)));
      addInstr(env, AMD64Instr_SseLdSt(True, 16, dst, rsp0));

      if (e->Iex.Unop.op == Iop_NegF64)
         addInstr(env, AMD64Instr_SseReRg(Asse_XOR, tmp, dst));
      else
         addInstr(env, AMD64Instr_SseReRg(Asse_ANDN, tmp, dst));

      add_to_rsp(env, 16);
      return dst;
   }

//..    if (e->tag == Iex_Unop) {
//..       X86FpOp fpop = Xfp_INVALID;
//..       switch (e->Iex.Unop.op) {
//..          case Iop_NegF64:  fpop = Xfp_NEG; break;
//..          case Iop_AbsF64:  fpop = Xfp_ABS; break;
//..          case Iop_SqrtF64: fpop = Xfp_SQRT; break;
//..          case Iop_SinF64:  fpop = Xfp_SIN; break;
//..          case Iop_CosF64:  fpop = Xfp_COS; break;
//..          case Iop_TanF64:  fpop = Xfp_TAN; break;
//..          case Iop_2xm1F64: fpop = Xfp_2XM1; break;
//..          default: break;
//..       }
//..       if (fpop != Xfp_INVALID) {
//..          HReg res = newVRegF(env);
//..          HReg src = iselDblExpr(env, e->Iex.Unop.arg);
//..          addInstr(env, X86Instr_FpUnary(fpop,src,res));
//.. 	 if (fpop != Xfp_SQRT
//..              && fpop != Xfp_NEG && fpop != Xfp_ABS)
//..             roundToF64(env, res);
//..          return res;
//..       }
//..    }

   if (e->tag == Iex_Unop) {
      switch (e->Iex.Unop.op) {
//..          case Iop_I32toF64: {
//..             HReg dst = newVRegF(env);
//..             HReg ri  = iselIntExpr_R(env, e->Iex.Unop.arg);
//..             addInstr(env, X86Instr_Push(X86RMI_Reg(ri)));
//..             set_FPU_rounding_default(env);
//..             addInstr(env, X86Instr_FpLdStI(
//..                              True/*load*/, 4, dst, 
//..                              X86AMode_IR(0, hregX86_ESP())));
//..             add_to_esp(env, 4);
//..             return dst;
//..          }
         case Iop_ReinterpI64asF64: {
            /* Given an I64, produce an IEEE754 double with the same
               bit pattern. */
            AMD64AMode* m8_rsp = AMD64AMode_IR(-8, hregAMD64_RSP());
            HReg        dst    = newVRegV(env);
            AMD64RI*    src    = iselIntExpr_RI(env, e->Iex.Unop.arg);
            /* paranoia */
            set_SSE_rounding_default(env);
            addInstr(env, AMD64Instr_Alu64M(Aalu_MOV, src, m8_rsp));
            addInstr(env, AMD64Instr_SseLdSt(True/*load*/, 8, dst, m8_rsp));
            return dst;
         }
         case Iop_F32toF64: {
            HReg f32;
            HReg f64 = newVRegV(env);
            /* this shouldn't be necessary, but be paranoid ... */
            set_SSE_rounding_default(env);
            f32 = iselFltExpr(env, e->Iex.Unop.arg);
            addInstr(env, AMD64Instr_SseSDSS(False/*S->D*/, f32, f64));
            return f64;
         }
         default: 
            break;
      }
   }

   /* --------- MULTIPLEX --------- */
   if (e->tag == Iex_Mux0X) {
      HReg r8, rX, r0, dst;
      vassert(ty == Ity_F64);
      vassert(typeOfIRExpr(env->type_env,e->Iex.Mux0X.cond) == Ity_I8);
      r8  = iselIntExpr_R(env, e->Iex.Mux0X.cond);
      rX  = iselDblExpr(env, e->Iex.Mux0X.exprX);
      r0  = iselDblExpr(env, e->Iex.Mux0X.expr0);
      dst = newVRegV(env);
      addInstr(env, mk_vMOVsd_RR(rX,dst));
      addInstr(env, AMD64Instr_Test64(AMD64RI_Imm(0xFF), AMD64RM_Reg(r8)));
      addInstr(env, AMD64Instr_SseCMov(Acc_Z,r0,dst));
      return dst;
   }

   ppIRExpr(e);
   vpanic("iselDblExpr_wrk");
}


/*---------------------------------------------------------*/
/*--- ISEL: SIMD (Vector) expressions, 128 bit.         ---*/
/*---------------------------------------------------------*/

static HReg iselVecExpr ( ISelEnv* env, IRExpr* e )
{
   HReg r = iselVecExpr_wrk( env, e );
#  if 0
   vex_printf("\n"); ppIRExpr(e); vex_printf("\n");
#  endif
   vassert(hregClass(r) == HRcVec128);
   vassert(hregIsVirtual(r));
   return r;
}


/* DO NOT CALL THIS DIRECTLY */
static HReg iselVecExpr_wrk ( ISelEnv* env, IRExpr* e )
{
   Bool     arg1isEReg = False;
   AMD64SseOp op = Asse_INVALID;
   IRType     ty = typeOfIRExpr(env->type_env,e);
   vassert(e);
   vassert(ty == Ity_V128);

   if (e->tag == Iex_Tmp) {
      return lookupIRTemp(env, e->Iex.Tmp.tmp);
   }

   if (e->tag == Iex_Get) {
      HReg dst = newVRegV(env);
      addInstr(env, AMD64Instr_SseLdSt(
                       True/*load*/, 
                       16,
                       dst,
                       AMD64AMode_IR(e->Iex.Get.offset, hregAMD64_RBP())
                    )
              );
      return dst;
   }

   if (e->tag == Iex_LDle) {
      HReg        dst = newVRegV(env);
      AMD64AMode* am  = iselIntExpr_AMode(env, e->Iex.LDle.addr);
      addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 16, dst, am ));
      return dst;
   }

   if (e->tag == Iex_Const) {
      HReg dst = newVRegV(env);
      vassert(e->Iex.Const.con->tag == Ico_V128);
      if (e->Iex.Const.con->Ico.V128 == 0x0000) {
         addInstr(env, AMD64Instr_SseReRg(Asse_XOR, dst, dst));
         return dst;
      } else
      if (e->Iex.Const.con->Ico.V128 == 0x00FF) {
         AMD64AMode* rsp0 = AMD64AMode_IR(0, hregAMD64_RSP());
         /* Both of these literals are sign-extended to 64 bits. */
         addInstr(env, AMD64Instr_Push(AMD64RMI_Imm(0)));
         addInstr(env, AMD64Instr_Push(AMD64RMI_Imm(0xFFFFFFFF)));
         addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 16, dst, rsp0 ));
         add_to_rsp(env, 16);
         return dst;
      } else 
      if (e->Iex.Const.con->Ico.V128 == 0x000F) {
         HReg tmp = newVRegI(env);
         AMD64AMode* rsp0 = AMD64AMode_IR(0, hregAMD64_RSP());
         addInstr(env, AMD64Instr_Imm64(0xFFFFFFFFULL, tmp));
         addInstr(env, AMD64Instr_Push(AMD64RMI_Imm(0)));
         addInstr(env, AMD64Instr_Push(AMD64RMI_Reg(tmp)));
         addInstr(env, AMD64Instr_SseLdSt( True/*load*/, 16, dst, rsp0 ));
         add_to_rsp(env, 16);
         return dst;
      } else {
         goto vec_fail;
#        if 0
         addInstr(env, X86Instr_SseConst(e->Iex.Const.con->Ico.V128, dst));
         return dst;
#        endif
      }
   }

   if (e->tag == Iex_Unop) {
   switch (e->Iex.Unop.op) {

      case Iop_NotV128: {
         HReg arg = iselVecExpr(env, e->Iex.Unop.arg);
         return do_sse_NotV128(env, arg);
      }

//..       case Iop_CmpNEZ64x2: {
//..          /* We can use SSE2 instructions for this. */
//..          /* Ideally, we want to do a 64Ix2 comparison against zero of
//..             the operand.  Problem is no such insn exists.  Solution
//..             therefore is to do a 32Ix4 comparison instead, and bitwise-
//..             negate (NOT) the result.  Let a,b,c,d be 32-bit lanes, and 
//..             let the not'd result of this initial comparison be a:b:c:d.
//..             What we need to compute is (a|b):(a|b):(c|d):(c|d).  So, use
//..             pshufd to create a value b:a:d:c, and OR that with a:b:c:d,
//..             giving the required result.
//.. 
//..             The required selection sequence is 2,3,0,1, which
//..             according to Intel's documentation means the pshufd
//..             literal value is 0xB1, that is, 
//..             (2 << 6) | (3 << 4) | (0 << 2) | (1 << 0) 
//..          */
//..          HReg arg  = iselVecExpr(env, e->Iex.Unop.arg);
//..          HReg tmp  = newVRegV(env);
//..          HReg dst  = newVRegV(env);
//..          REQUIRE_SSE2;
//..          addInstr(env, X86Instr_SseReRg(Xsse_XOR, tmp, tmp));
//..          addInstr(env, X86Instr_SseReRg(Xsse_CMPEQ32, arg, tmp));
//..          tmp = do_sse_Not128(env, tmp);
//..          addInstr(env, X86Instr_SseShuf(0xB1, tmp, dst));
//..          addInstr(env, X86Instr_SseReRg(Xsse_OR, tmp, dst));
//..          return dst;
//..       }
//.. 
//..       case Iop_CmpNEZ32x4: {
//..          /* Sigh, we have to generate lousy code since this has to
//..             work on SSE1 hosts */
//..          /* basically, the idea is: for each lane:
//..                movl lane, %r ; negl %r   (now CF = lane==0 ? 0 : 1)
//..                sbbl %r, %r               (now %r = 1Sto32(CF))
//..                movl %r, lane
//..          */
//..          Int       i;
//..          X86AMode* am;
//..          X86AMode* esp0 = X86AMode_IR(0, hregX86_ESP());
//..          HReg      arg  = iselVecExpr(env, e->Iex.Unop.arg);
//..          HReg      dst  = newVRegV(env);
//..          HReg      r32  = newVRegI(env);
//..          sub_from_esp(env, 16);
//..          addInstr(env, X86Instr_SseLdSt(False/*store*/, arg, esp0));
//..          for (i = 0; i < 4; i++) {
//..             am = X86AMode_IR(i*4, hregX86_ESP());
//..             addInstr(env, X86Instr_Alu32R(Xalu_MOV, X86RMI_Mem(am), r32));
//..             addInstr(env, X86Instr_Unary32(Xun_NEG, X86RM_Reg(r32)));
//..             addInstr(env, X86Instr_Alu32R(Xalu_SBB, X86RMI_Reg(r32), r32));
//..             addInstr(env, X86Instr_Alu32M(Xalu_MOV, X86RI_Reg(r32), am));
//..          }
//..          addInstr(env, X86Instr_SseLdSt(True/*load*/, dst, esp0));
//..          add_to_esp(env, 16);
//..          return dst;
//..       }
//.. 
//..       case Iop_CmpNEZ8x16:
//..       case Iop_CmpNEZ16x8: {
//..          /* We can use SSE2 instructions for this. */
//..          HReg arg;
//..          HReg vec0 = newVRegV(env);
//..          HReg vec1 = newVRegV(env);
//..          HReg dst  = newVRegV(env);
//..          X86SseOp cmpOp 
//..             = e->Iex.Unop.op==Iop_CmpNEZ16x8 ? Xsse_CMPEQ16
//..                                              : Xsse_CMPEQ8;
//..          REQUIRE_SSE2;
//..          addInstr(env, X86Instr_SseReRg(Xsse_XOR, vec0, vec0));
//..          addInstr(env, mk_vMOVsd_RR(vec0, vec1));
//..          addInstr(env, X86Instr_Sse32Fx4(Xsse_CMPEQF, vec1, vec1));
//..          /* defer arg computation to here so as to give CMPEQF as long
//..             as possible to complete */
//..          arg = iselVecExpr(env, e->Iex.Unop.arg);
//..          /* vec0 is all 0s; vec1 is all 1s */
//..          addInstr(env, mk_vMOVsd_RR(arg, dst));
//..          /* 16x8 or 8x16 comparison == */
//..          addInstr(env, X86Instr_SseReRg(cmpOp, vec0, dst));
//..          /* invert result */
//..          addInstr(env, X86Instr_SseReRg(Xsse_XOR, vec1, dst));
//..          return dst;
//..       }
//.. 
//..       case Iop_Recip32Fx4: op = Xsse_RCPF;   goto do_32Fx4_unary;
//..       case Iop_RSqrt32Fx4: op = Xsse_RSQRTF; goto do_32Fx4_unary;
//..       case Iop_Sqrt32Fx4:  op = Xsse_SQRTF;  goto do_32Fx4_unary;
//..       do_32Fx4_unary:
//..       {
//..          HReg arg = iselVecExpr(env, e->Iex.Unop.arg);
//..          HReg dst = newVRegV(env);
//..          addInstr(env, X86Instr_Sse32Fx4(op, arg, dst));
//..          return dst;
//..       }
//.. 
//..       case Iop_Recip64Fx2: op = Xsse_RCPF;   goto do_64Fx2_unary;
//..       case Iop_RSqrt64Fx2: op = Xsse_RSQRTF; goto do_64Fx2_unary;
//..       case Iop_Sqrt64Fx2:  op = Xsse_SQRTF;  goto do_64Fx2_unary;
//..       do_64Fx2_unary:
//..       {
//..          HReg arg = iselVecExpr(env, e->Iex.Unop.arg);
//..          HReg dst = newVRegV(env);
//..          REQUIRE_SSE2;
//..          addInstr(env, X86Instr_Sse64Fx2(op, arg, dst));
//..          return dst;
//..       }
//.. 
//..       case Iop_Recip32F0x4: op = Xsse_RCPF;   goto do_32F0x4_unary;
//..       case Iop_RSqrt32F0x4: op = Xsse_RSQRTF; goto do_32F0x4_unary;
//..       case Iop_Sqrt32F0x4:  op = Xsse_SQRTF;  goto do_32F0x4_unary;
//..       do_32F0x4_unary:
//..       {
//..          /* A bit subtle.  We have to copy the arg to the result
//..             register first, because actually doing the SSE scalar insn
//..             leaves the upper 3/4 of the destination register
//..             unchanged.  Whereas the required semantics of these
//..             primops is that the upper 3/4 is simply copied in from the
//..             argument. */
//..          HReg arg = iselVecExpr(env, e->Iex.Unop.arg);
//..          HReg dst = newVRegV(env);
//..          addInstr(env, mk_vMOVsd_RR(arg, dst));
//..          addInstr(env, X86Instr_Sse32FLo(op, arg, dst));
//..          return dst;
//..       }
//.. 
//..       case Iop_Recip64F0x2: op = Xsse_RCPF;   goto do_64F0x2_unary;
//..       case Iop_RSqrt64F0x2: op = Xsse_RSQRTF; goto do_64F0x2_unary;
      case Iop_Sqrt64F0x2:  op = Asse_SQRTF;  goto do_64F0x2_unary;
      do_64F0x2_unary:
      {
         /* A bit subtle.  We have to copy the arg to the result
            register first, because actually doing the SSE scalar insn
            leaves the upper half of the destination register
            unchanged.  Whereas the required semantics of these
            primops is that the upper half is simply copied in from the
            argument. */
         HReg arg = iselVecExpr(env, e->Iex.Unop.arg);
         HReg dst = newVRegV(env);
         addInstr(env, mk_vMOVsd_RR(arg, dst));
         addInstr(env, AMD64Instr_Sse64FLo(op, arg, dst));
         return dst;
      }

      case Iop_32UtoV128: {
         HReg        dst     = newVRegV(env);
         AMD64AMode* rsp_m32 = AMD64AMode_IR(-32, hregAMD64_RSP());
         AMD64RI*    ri      = iselIntExpr_RI(env, e->Iex.Unop.arg);
         addInstr(env, AMD64Instr_Alu64M(Aalu_MOV, ri, rsp_m32));
         addInstr(env, AMD64Instr_SseLdzLO(4, dst, rsp_m32));
         return dst;
      }

      case Iop_64UtoV128: {
         HReg        dst  = newVRegV(env);
         AMD64AMode* rsp0 = AMD64AMode_IR(0, hregAMD64_RSP());
         AMD64RMI*   rmi  = iselIntExpr_RMI(env, e->Iex.Unop.arg);
         addInstr(env, AMD64Instr_Push(rmi));
         addInstr(env, AMD64Instr_SseLdzLO(8, dst, rsp0));
         add_to_rsp(env, 8);
         return dst;
      }

      default:
         break;
   } /* switch (e->Iex.Unop.op) */
   } /* if (e->tag == Iex_Unop) */

   if (e->tag == Iex_Binop) {
   switch (e->Iex.Binop.op) {

//..       case Iop_Set128lo32: {
//..          HReg dst = newVRegV(env);
//..          HReg srcV = iselVecExpr(env, e->Iex.Binop.arg1);
//..          HReg srcI = iselIntExpr_R(env, e->Iex.Binop.arg2);
//..          X86AMode* esp0 = X86AMode_IR(0, hregX86_ESP());
//..          sub_from_esp(env, 16);
//..          addInstr(env, X86Instr_SseLdSt(False/*store*/, srcV, esp0));
//..          addInstr(env, X86Instr_Alu32M(Xalu_MOV, X86RI_Reg(srcI), esp0));
//..          addInstr(env, X86Instr_SseLdSt(True/*load*/, dst, esp0));
//..          add_to_esp(env, 16);
//..          return dst;
//..       }

      case Iop_SetV128lo64: {
         HReg dst  = newVRegV(env);
         HReg srcV = iselVecExpr(env, e->Iex.Binop.arg1);
         HReg srcI = iselIntExpr_R(env, e->Iex.Binop.arg2);
         AMD64AMode* rsp0 = AMD64AMode_IR(0, hregAMD64_RSP());
         sub_from_rsp(env, 16);
         addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 16, srcV, rsp0));
         addInstr(env, AMD64Instr_Alu64M(Aalu_MOV, AMD64RI_Reg(srcI), rsp0));
         addInstr(env, AMD64Instr_SseLdSt(True/*load*/, 16, dst, rsp0));
         add_to_rsp(env, 16);
         return dst;
      }

      case Iop_64HLtoV128: {
         AMD64AMode* rsp = AMD64AMode_IR(0, hregAMD64_RSP());
         HReg        dst = newVRegV(env);
         /* do this via the stack (easy, convenient, etc) */
         addInstr(env, AMD64Instr_Push(iselIntExpr_RMI(env, e->Iex.Binop.arg1)));
         addInstr(env, AMD64Instr_Push(iselIntExpr_RMI(env, e->Iex.Binop.arg2)));
         addInstr(env, AMD64Instr_SseLdSt(True/*load*/, 16, dst, rsp));
         add_to_rsp(env, 16);
         return dst;
      }

//..       case Iop_CmpEQ32Fx4: op = Xsse_CMPEQF; goto do_32Fx4;
//..       case Iop_CmpLT32Fx4: op = Xsse_CMPLTF; goto do_32Fx4;
//..       case Iop_CmpLE32Fx4: op = Xsse_CMPLEF; goto do_32Fx4;
//..       case Iop_Add32Fx4:   op = Xsse_ADDF;   goto do_32Fx4;
//..       case Iop_Div32Fx4:   op = Xsse_DIVF;   goto do_32Fx4;
//..       case Iop_Max32Fx4:   op = Xsse_MAXF;   goto do_32Fx4;
//..       case Iop_Min32Fx4:   op = Xsse_MINF;   goto do_32Fx4;
//..       case Iop_Mul32Fx4:   op = Xsse_MULF;   goto do_32Fx4;
//..       case Iop_Sub32Fx4:   op = Xsse_SUBF;   goto do_32Fx4;
//..       do_32Fx4:
//..       {
//..          HReg argL = iselVecExpr(env, e->Iex.Binop.arg1);
//..          HReg argR = iselVecExpr(env, e->Iex.Binop.arg2);
//..          HReg dst = newVRegV(env);
//..          addInstr(env, mk_vMOVsd_RR(argL, dst));
//..          addInstr(env, X86Instr_Sse32Fx4(op, argR, dst));
//..          return dst;
//..       }
//.. 
//..       case Iop_CmpEQ64Fx2: op = Xsse_CMPEQF; goto do_64Fx2;
//..       case Iop_CmpLT64Fx2: op = Xsse_CMPLTF; goto do_64Fx2;
//..       case Iop_CmpLE64Fx2: op = Xsse_CMPLEF; goto do_64Fx2;
//..       case Iop_Add64Fx2:   op = Xsse_ADDF;   goto do_64Fx2;
//..       case Iop_Div64Fx2:   op = Xsse_DIVF;   goto do_64Fx2;
//..       case Iop_Max64Fx2:   op = Xsse_MAXF;   goto do_64Fx2;
//..       case Iop_Min64Fx2:   op = Xsse_MINF;   goto do_64Fx2;
//..       case Iop_Mul64Fx2:   op = Xsse_MULF;   goto do_64Fx2;
//..       case Iop_Sub64Fx2:   op = Xsse_SUBF;   goto do_64Fx2;
//..       do_64Fx2:
//..       {
//..          HReg argL = iselVecExpr(env, e->Iex.Binop.arg1);
//..          HReg argR = iselVecExpr(env, e->Iex.Binop.arg2);
//..          HReg dst = newVRegV(env);
//..          REQUIRE_SSE2;
//..          addInstr(env, mk_vMOVsd_RR(argL, dst));
//..          addInstr(env, X86Instr_Sse64Fx2(op, argR, dst));
//..          return dst;
//..       }

//..       case Iop_CmpEQ32F0x4: op = Xsse_CMPEQF; goto do_32F0x4;
      case Iop_CmpLT32F0x4: op = Asse_CMPLTF; goto do_32F0x4;
//..       case Iop_CmpLE32F0x4: op = Xsse_CMPLEF; goto do_32F0x4;
      case Iop_Add32F0x4:   op = Asse_ADDF;   goto do_32F0x4;
      case Iop_Div32F0x4:   op = Asse_DIVF;   goto do_32F0x4;
      case Iop_Max32F0x4:   op = Asse_MAXF;   goto do_32F0x4;
      case Iop_Min32F0x4:   op = Asse_MINF;   goto do_32F0x4;
      case Iop_Mul32F0x4:   op = Asse_MULF;   goto do_32F0x4;
      case Iop_Sub32F0x4:   op = Asse_SUBF;   goto do_32F0x4;
      do_32F0x4: {
         HReg argL = iselVecExpr(env, e->Iex.Binop.arg1);
         HReg argR = iselVecExpr(env, e->Iex.Binop.arg2);
         HReg dst = newVRegV(env);
         addInstr(env, mk_vMOVsd_RR(argL, dst));
         addInstr(env, AMD64Instr_Sse32FLo(op, argR, dst));
         return dst;
      }

      case Iop_CmpEQ64F0x2: op = Asse_CMPEQF; goto do_64F0x2;
      case Iop_CmpLT64F0x2: op = Asse_CMPLTF; goto do_64F0x2;
      case Iop_CmpLE64F0x2: op = Asse_CMPLEF; goto do_64F0x2;
      case Iop_Add64F0x2:   op = Asse_ADDF;   goto do_64F0x2;
      case Iop_Div64F0x2:   op = Asse_DIVF;   goto do_64F0x2;
      case Iop_Max64F0x2:   op = Asse_MAXF;   goto do_64F0x2;
      case Iop_Min64F0x2:   op = Asse_MINF;   goto do_64F0x2;
      case Iop_Mul64F0x2:   op = Asse_MULF;   goto do_64F0x2;
      case Iop_Sub64F0x2:   op = Asse_SUBF;   goto do_64F0x2;
      do_64F0x2: {
         HReg argL = iselVecExpr(env, e->Iex.Binop.arg1);
         HReg argR = iselVecExpr(env, e->Iex.Binop.arg2);
         HReg dst = newVRegV(env);
         addInstr(env, mk_vMOVsd_RR(argL, dst));
         addInstr(env, AMD64Instr_Sse64FLo(op, argR, dst));
         return dst;
      }

//..       case Iop_QNarrow32Sx4: 
//..          op = Xsse_PACKSSD; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_QNarrow16Sx8: 
//..          op = Xsse_PACKSSW; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_QNarrow16Ux8: 
//..          op = Xsse_PACKUSW; arg1isEReg = True; goto do_SseReRg;
//.. 
//..       case Iop_InterleaveHI8x16: 
//..          op = Xsse_UNPCKHB; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_InterleaveHI16x8: 
//..          op = Xsse_UNPCKHW; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_InterleaveHI32x4: 
//..          op = Xsse_UNPCKHD; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_InterleaveHI64x2: 
//..          op = Xsse_UNPCKHQ; arg1isEReg = True; goto do_SseReRg;
//.. 
//..       case Iop_InterleaveLO8x16: 
//..          op = Xsse_UNPCKLB; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_InterleaveLO16x8: 
//..          op = Xsse_UNPCKLW; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_InterleaveLO32x4: 
//..          op = Xsse_UNPCKLD; arg1isEReg = True; goto do_SseReRg;
//..       case Iop_InterleaveLO64x2: 
//..          op = Xsse_UNPCKLQ; arg1isEReg = True; goto do_SseReRg;
//.. 
      case Iop_AndV128:    op = Asse_AND;      goto do_SseReRg;
      case Iop_OrV128:     op = Asse_OR;       goto do_SseReRg;
      case Iop_XorV128:    op = Asse_XOR;      goto do_SseReRg;
//..       case Iop_Add8x16:    op = Xsse_ADD8;     goto do_SseReRg;
//..       case Iop_Add16x8:    op = Xsse_ADD16;    goto do_SseReRg;
//..       case Iop_Add32x4:    op = Xsse_ADD32;    goto do_SseReRg;
//..       case Iop_Add64x2:    op = Xsse_ADD64;    goto do_SseReRg;
//..       case Iop_QAdd8Sx16:  op = Xsse_QADD8S;   goto do_SseReRg;
//..       case Iop_QAdd16Sx8:  op = Xsse_QADD16S;  goto do_SseReRg;
//..       case Iop_QAdd8Ux16:  op = Xsse_QADD8U;   goto do_SseReRg;
//..       case Iop_QAdd16Ux8:  op = Xsse_QADD16U;  goto do_SseReRg;
//..       case Iop_Avg8Ux16:   op = Xsse_AVG8U;    goto do_SseReRg;
//..       case Iop_Avg16Ux8:   op = Xsse_AVG16U;   goto do_SseReRg;
//..       case Iop_CmpEQ8x16:  op = Xsse_CMPEQ8;   goto do_SseReRg;
//..       case Iop_CmpEQ16x8:  op = Xsse_CMPEQ16;  goto do_SseReRg;
//..       case Iop_CmpEQ32x4:  op = Xsse_CMPEQ32;  goto do_SseReRg;
//..       case Iop_CmpGT8Sx16: op = Xsse_CMPGT8S;  goto do_SseReRg;
//..       case Iop_CmpGT16Sx8: op = Xsse_CMPGT16S; goto do_SseReRg;
//..       case Iop_CmpGT32Sx4: op = Xsse_CMPGT32S; goto do_SseReRg;
//..       case Iop_Max16Sx8:   op = Xsse_MAX16S;   goto do_SseReRg;
//..       case Iop_Max8Ux16:   op = Xsse_MAX8U;    goto do_SseReRg;
//..       case Iop_Min16Sx8:   op = Xsse_MIN16S;   goto do_SseReRg;
//..       case Iop_Min8Ux16:   op = Xsse_MIN8U;    goto do_SseReRg;
//..       case Iop_MulHi16Ux8: op = Xsse_MULHI16U; goto do_SseReRg;
//..       case Iop_MulHi16Sx8: op = Xsse_MULHI16S; goto do_SseReRg;
//..       case Iop_Mul16x8:    op = Xsse_MUL16;    goto do_SseReRg;
//..       case Iop_Sub8x16:    op = Xsse_SUB8;     goto do_SseReRg;
//..       case Iop_Sub16x8:    op = Xsse_SUB16;    goto do_SseReRg;
//..       case Iop_Sub32x4:    op = Xsse_SUB32;    goto do_SseReRg;
//..       case Iop_Sub64x2:    op = Xsse_SUB64;    goto do_SseReRg;
//..       case Iop_QSub8Sx16:  op = Xsse_QSUB8S;   goto do_SseReRg;
//..       case Iop_QSub16Sx8:  op = Xsse_QSUB16S;  goto do_SseReRg;
//..       case Iop_QSub8Ux16:  op = Xsse_QSUB8U;   goto do_SseReRg;
//..       case Iop_QSub16Ux8:  op = Xsse_QSUB16U;  goto do_SseReRg;
      do_SseReRg: {
         HReg arg1 = iselVecExpr(env, e->Iex.Binop.arg1);
         HReg arg2 = iselVecExpr(env, e->Iex.Binop.arg2);
         HReg dst = newVRegV(env);
         if (arg1isEReg) {
            goto vec_fail; /* awaiting test case */
            addInstr(env, mk_vMOVsd_RR(arg2, dst));
            addInstr(env, AMD64Instr_SseReRg(op, arg1, dst));
         } else {
            addInstr(env, mk_vMOVsd_RR(arg1, dst));
            addInstr(env, AMD64Instr_SseReRg(op, arg2, dst));
         }
         return dst;
      }

//..       case Iop_ShlN16x8: op = Xsse_SHL16; goto do_SseShift;
//..       case Iop_ShlN32x4: op = Xsse_SHL32; goto do_SseShift;
//..       case Iop_ShlN64x2: op = Xsse_SHL64; goto do_SseShift;
//..       case Iop_SarN16x8: op = Xsse_SAR16; goto do_SseShift;
//..       case Iop_SarN32x4: op = Xsse_SAR32; goto do_SseShift;
//..       case Iop_ShrN16x8: op = Xsse_SHR16; goto do_SseShift;
//..       case Iop_ShrN32x4: op = Xsse_SHR32; goto do_SseShift;
//..       case Iop_ShrN64x2: op = Xsse_SHR64; goto do_SseShift;
//..       do_SseShift: {
//..          HReg      greg = iselVecExpr(env, e->Iex.Binop.arg1);
//..          X86RMI*   rmi  = iselIntExpr_RMI(env, e->Iex.Binop.arg2);
//..          X86AMode* esp0 = X86AMode_IR(0, hregX86_ESP());
//..          HReg      ereg = newVRegV(env);
//..          HReg      dst  = newVRegV(env);
//..          REQUIRE_SSE2;
//..          addInstr(env, X86Instr_Push(X86RMI_Imm(0)));
//..          addInstr(env, X86Instr_Push(X86RMI_Imm(0)));
//..          addInstr(env, X86Instr_Push(X86RMI_Imm(0)));
//..          addInstr(env, X86Instr_Push(rmi));
//..          addInstr(env, X86Instr_SseLdSt(True/*load*/, ereg, esp0));
//..          addInstr(env, mk_vMOVsd_RR(greg, dst));
//..          addInstr(env, X86Instr_SseReRg(op, ereg, dst));
//..          add_to_esp(env, 16);
//..          return dst;
//..       }

      default:
         break;
   } /* switch (e->Iex.Binop.op) */
   } /* if (e->tag == Iex_Binop) */

//..    if (e->tag == Iex_Mux0X) {
//..       HReg r8  = iselIntExpr_R(env, e->Iex.Mux0X.cond);
//..       HReg rX  = iselVecExpr(env, e->Iex.Mux0X.exprX);
//..       HReg r0  = iselVecExpr(env, e->Iex.Mux0X.expr0);
//..       HReg dst = newVRegV(env);
//..       addInstr(env, mk_vMOVsd_RR(rX,dst));
//..       addInstr(env, X86Instr_Test32(X86RI_Imm(0xFF), X86RM_Reg(r8)));
//..       addInstr(env, X86Instr_SseCMov(Xcc_Z,r0,dst));
//..       return dst;
//..    }
//.. 
   vec_fail:
   vex_printf("iselVecExpr (amd64, subarch = %s): can't reduce\n",
              LibVEX_ppVexSubArch(env->subarch));
   ppIRExpr(e);
   vpanic("iselVecExpr_wrk");
}


/*---------------------------------------------------------*/
/*--- ISEL: Statements                                  ---*/
/*---------------------------------------------------------*/

static void iselStmt ( ISelEnv* env, IRStmt* stmt )
{
   if (vex_traceflags & VEX_TRACE_VCODE) {
      vex_printf("\n-- ");
      ppIRStmt(stmt);
      vex_printf("\n");
   }

   switch (stmt->tag) {

   /* --------- STORE --------- */
   case Ist_STle: {
      AMD64AMode* am;
      IRType tya = typeOfIRExpr(env->type_env, stmt->Ist.STle.addr);
      IRType tyd = typeOfIRExpr(env->type_env, stmt->Ist.STle.data);
      vassert(tya == Ity_I64);
      am = iselIntExpr_AMode(env, stmt->Ist.STle.addr);
      if (tyd == Ity_I64) {
         AMD64RI* ri = iselIntExpr_RI(env, stmt->Ist.STle.data);
         addInstr(env, AMD64Instr_Alu64M(Aalu_MOV,ri,am));
         return;
      }
      if (tyd == Ity_I8 || tyd == Ity_I16 || tyd == Ity_I32) {
         HReg r = iselIntExpr_R(env, stmt->Ist.STle.data);
         addInstr(env, AMD64Instr_Store(
                          toUChar(tyd==Ity_I8 ? 1 : (tyd==Ity_I16 ? 2 : 4)),
                          r,am));
         return;
      }
      if (tyd == Ity_F64) {
         HReg r = iselDblExpr(env, stmt->Ist.STle.data);
         addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 8, r, am));
         return;
      }
      if (tyd == Ity_F32) {
         HReg r = iselFltExpr(env, stmt->Ist.STle.data);
         addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 4, r, am));
         return;
      }
//..       if (tyd == Ity_I64) {
//..          HReg vHi, vLo, rA;
//..          iselInt64Expr(&vHi, &vLo, env, stmt->Ist.STle.data);
//..          rA = iselIntExpr_R(env, stmt->Ist.STle.addr);
//..          addInstr(env, X86Instr_Alu32M(
//..                           Xalu_MOV, X86RI_Reg(vLo), X86AMode_IR(0, rA)));
//..          addInstr(env, X86Instr_Alu32M(
//..                           Xalu_MOV, X86RI_Reg(vHi), X86AMode_IR(4, rA)));
//..          return;
//..       }
      if (tyd == Ity_V128) {
         HReg r = iselVecExpr(env, stmt->Ist.STle.data);
         addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 16, r, am));
         return;
      }
      break;
   }

   /* --------- PUT --------- */
   case Ist_Put: {
      IRType ty = typeOfIRExpr(env->type_env, stmt->Ist.Put.data);
      if (ty == Ity_I64) {
         /* We're going to write to memory, so compute the RHS into an
            AMD64RI. */
         AMD64RI* ri = iselIntExpr_RI(env, stmt->Ist.Put.data);
         addInstr(env,
                  AMD64Instr_Alu64M(
                     Aalu_MOV,
                     ri,
                     AMD64AMode_IR(stmt->Ist.Put.offset,
                                   hregAMD64_RBP())
                 ));
         return;
      }
      if (ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32) {
         HReg r = iselIntExpr_R(env, stmt->Ist.Put.data);
         addInstr(env, AMD64Instr_Store(
                          toUChar(ty==Ity_I8 ? 1 : (ty==Ity_I16 ? 2 : 4)),
                          r,
                          AMD64AMode_IR(stmt->Ist.Put.offset,
                                        hregAMD64_RBP())));
         return;
      }
      if (ty == Ity_V128) {
         HReg        vec = iselVecExpr(env, stmt->Ist.Put.data);
         AMD64AMode* am  = AMD64AMode_IR(stmt->Ist.Put.offset, 
                                         hregAMD64_RBP());
         addInstr(env, AMD64Instr_SseLdSt(False/*store*/, 16, vec, am));
         return;
      }
      if (ty == Ity_F32) {
         HReg f32 = iselFltExpr(env, stmt->Ist.Put.data);
         AMD64AMode* am = AMD64AMode_IR(stmt->Ist.Put.offset, hregAMD64_RBP());
         set_SSE_rounding_default(env); /* paranoia */
         addInstr(env, AMD64Instr_SseLdSt( False/*store*/, 4, f32, am ));
         return;
      }
      if (ty == Ity_F64) {
         HReg f64 = iselDblExpr(env, stmt->Ist.Put.data);
         AMD64AMode* am = AMD64AMode_IR( stmt->Ist.Put.offset, 
                                         hregAMD64_RBP() );
         addInstr(env, AMD64Instr_SseLdSt( False/*store*/, 8, f64, am ));
         return;
      }
      break;
   }

   /* --------- Indexed PUT --------- */
   case Ist_PutI: {
      AMD64AMode* am 
         = genGuestArrayOffset(
              env, stmt->Ist.PutI.descr, 
                   stmt->Ist.PutI.ix, stmt->Ist.PutI.bias );

      IRType ty = typeOfIRExpr(env->type_env, stmt->Ist.PutI.data);
      if (ty == Ity_F64) {
         HReg val = iselDblExpr(env, stmt->Ist.PutI.data);
         addInstr(env, AMD64Instr_SseLdSt( False/*store*/, 8, val, am ));
         return;
      }
      if (ty == Ity_I8) {
         HReg r = iselIntExpr_R(env, stmt->Ist.PutI.data);
         addInstr(env, AMD64Instr_Store( 1, r, am ));
         return;
      }
//..       if (ty == Ity_I64) {
//..          HReg rHi, rLo;
//..          X86AMode* am4 = advance4(am);
//..          iselInt64Expr(&rHi, &rLo, env, stmt->Ist.PutI.data);
//..          addInstr(env, X86Instr_Alu32M( Xalu_MOV, X86RI_Reg(rLo), am ));
//..          addInstr(env, X86Instr_Alu32M( Xalu_MOV, X86RI_Reg(rHi), am4 ));
//..          return;
//..       }
      break;
   }

   /* --------- TMP --------- */
   case Ist_Tmp: {
      IRTemp tmp = stmt->Ist.Tmp.tmp;
      IRType ty = typeOfIRTemp(env->type_env, tmp);
      if (ty == Ity_I64 || ty == Ity_I32 
          || ty == Ity_I16 || ty == Ity_I8) {
         AMD64RMI* rmi = iselIntExpr_RMI(env, stmt->Ist.Tmp.data);
         HReg dst = lookupIRTemp(env, tmp);
         addInstr(env, AMD64Instr_Alu64R(Aalu_MOV,rmi,dst));
         return;
      }
      if (ty == Ity_I128) {
         HReg rHi, rLo, dstHi, dstLo;
         iselInt128Expr(&rHi,&rLo, env, stmt->Ist.Tmp.data);
         lookupIRTemp128( &dstHi, &dstLo, env, tmp);
         addInstr(env, mk_iMOVsd_RR(rHi,dstHi) );
         addInstr(env, mk_iMOVsd_RR(rLo,dstLo) );
         return;
      }
      if (ty == Ity_I1) {
         AMD64CondCode cond = iselCondCode(env, stmt->Ist.Tmp.data);
         HReg dst = lookupIRTemp(env, tmp);
         addInstr(env, AMD64Instr_Set64(cond, dst));
         return;
      }
      if (ty == Ity_F64) {
         HReg dst = lookupIRTemp(env, tmp);
         HReg src = iselDblExpr(env, stmt->Ist.Tmp.data);
         addInstr(env, mk_vMOVsd_RR(src, dst));
         return;
      }
      if (ty == Ity_F32) {
         HReg dst = lookupIRTemp(env, tmp);
         HReg src = iselFltExpr(env, stmt->Ist.Tmp.data);
         addInstr(env, mk_vMOVsd_RR(src, dst));
         return;
      }
      if (ty == Ity_V128) {
         HReg dst = lookupIRTemp(env, tmp);
         HReg src = iselVecExpr(env, stmt->Ist.Tmp.data);
         addInstr(env, mk_vMOVsd_RR(src, dst));
         return;
      }
      break;
   }

   /* --------- Call to DIRTY helper --------- */
   case Ist_Dirty: {
      IRType   retty;
      IRDirty* d = stmt->Ist.Dirty.details;
      Bool     passBBP = False;

      if (d->nFxState == 0)
         vassert(!d->needsBBP);

      passBBP = toBool(d->nFxState > 0 && d->needsBBP);

      /* Marshal args, do the call, clear stack. */
      doHelperCall( env, passBBP, d->guard, d->cee, d->args );

      /* Now figure out what to do with the returned value, if any. */
      if (d->tmp == IRTemp_INVALID)
         /* No return value.  Nothing to do. */
         return;

      retty = typeOfIRTemp(env->type_env, d->tmp);
      if (retty == Ity_I64) {
         /* The returned value is in %rax.  Park it in the register
            associated with tmp. */
         HReg dst = lookupIRTemp(env, d->tmp);
         addInstr(env, mk_iMOVsd_RR(hregAMD64_RAX(),dst) );
         return;
      }
      break;
   }

   /* --------- MEM FENCE --------- */
   case Ist_MFence:
      addInstr(env, AMD64Instr_MFence());
      return;

   /* --------- INSTR MARK --------- */
   /* Doesn't generate any executable code ... */
   case Ist_IMark:
       return;

   /* --------- NO-OP --------- */
   case Ist_NoOp:
       return;

   /* --------- EXIT --------- */
   case Ist_Exit: {
      AMD64RI*      dst;
      AMD64CondCode cc;
      if (stmt->Ist.Exit.dst->tag != Ico_U64)
         vpanic("iselStmt(amd64): Ist_Exit: dst is not a 64-bit value");
      dst = iselIntExpr_RI(env, IRExpr_Const(stmt->Ist.Exit.dst));
      cc  = iselCondCode(env,stmt->Ist.Exit.guard);
      addInstr(env, AMD64Instr_Goto(stmt->Ist.Exit.jk, cc, dst));
      return;
   }

   default: break;
   }
   ppIRStmt(stmt);
   vpanic("iselStmt(amd64)");
}


/*---------------------------------------------------------*/
/*--- ISEL: Basic block terminators (Nexts)             ---*/
/*---------------------------------------------------------*/

static void iselNext ( ISelEnv* env, IRExpr* next, IRJumpKind jk )
{
   AMD64RI* ri;
   if (vex_traceflags & VEX_TRACE_VCODE) {
      vex_printf("\n-- goto {");
      ppIRJumpKind(jk);
      vex_printf("} ");
      ppIRExpr(next);
      vex_printf("\n");
   }
   ri = iselIntExpr_RI(env, next);
   addInstr(env, AMD64Instr_Goto(jk, Acc_ALWAYS,ri));
}


/*---------------------------------------------------------*/
/*--- Insn selector top-level                           ---*/
/*---------------------------------------------------------*/

/* Translate an entire BB to amd64 code. */

HInstrArray* iselBB_AMD64 ( IRBB* bb, VexSubArch subarch_host )
{
   Int      i, j;
   HReg     hreg, hregHI;
   ISelEnv* env;

   /* sanity ... */
   vassert(subarch_host == VexSubArch_NONE);

   /* Make up an initial environment to use. */
   env = LibVEX_Alloc(sizeof(ISelEnv));
   env->vreg_ctr = 0;

   /* Set up output code array. */
   env->code = newHInstrArray();

   /* Copy BB's type env. */
   env->type_env = bb->tyenv;

   /* Make up an IRTemp -> virtual HReg mapping.  This doesn't
      change as we go along. */
   env->n_vregmap = bb->tyenv->types_used;
   env->vregmap   = LibVEX_Alloc(env->n_vregmap * sizeof(HReg));
   env->vregmapHI = LibVEX_Alloc(env->n_vregmap * sizeof(HReg));

   /* and finally ... */
   env->subarch = subarch_host;

   /* For each IR temporary, allocate a suitably-kinded virtual
      register. */
   j = 0;
   for (i = 0; i < env->n_vregmap; i++) {
      hregHI = hreg = INVALID_HREG;
      switch (bb->tyenv->types[i]) {
         case Ity_I1:
         case Ity_I8:
         case Ity_I16:
         case Ity_I32:
         case Ity_I64:  hreg   = mkHReg(j++, HRcInt64, True); break;
         case Ity_I128: hreg   = mkHReg(j++, HRcInt64, True);
                        hregHI = mkHReg(j++, HRcInt64, True); break;
         case Ity_F32:
         case Ity_F64:
         case Ity_V128: hreg   = mkHReg(j++, HRcVec128, True); break;
         default: ppIRType(bb->tyenv->types[i]);
                  vpanic("iselBB(amd64): IRTemp type");
      }
      env->vregmap[i]   = hreg;
      env->vregmapHI[i] = hregHI;
   }
   env->vreg_ctr = j;

   /* Ok, finally we can iterate over the statements. */
   for (i = 0; i < bb->stmts_used; i++)
      if (bb->stmts[i])
         iselStmt(env,bb->stmts[i]);

   iselNext(env,bb->next,bb->jumpkind);

   /* record the number of vregs we used. */
   env->code->n_vregs = env->vreg_ctr;
   return env->code;
}


/*---------------------------------------------------------------*/
/*--- end                                   host-amd64/isel.c ---*/
/*---------------------------------------------------------------*/
