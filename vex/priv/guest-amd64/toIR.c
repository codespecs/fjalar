
/*--------------------------------------------------------------------*/
/*---                                                              ---*/
/*--- This file (guest-amd64/toIR.c) is                            ---*/
/*--- Copyright (c) OpenWorks LLP.  All rights reserved.           ---*/
/*---                                                              ---*/
/*--------------------------------------------------------------------*/

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

/* LIMITATIONS: 

   LOCK prefix handling is only safe in the situation where
   Vex-generated code is run single-threadedly.  (This is not the same
   as saying that Valgrind can't safely use Vex to run multithreaded
   programs).  See comment attached to LOCK prefix handling in
   disInstr for details.
*/

/* TODO:

   MOVQ (sse) is wrong wrt is the upper half zeroed or not?
   It always should be if dst is a reg; not quite the same
   as MOVSD.
*/

//.. /* TODO:
//.. 
//..    check flag settings for cmpxchg
//..    FUCOMI(P): what happens to A and S flags?  Currently are forced
//..       to zero.
//.. 
//..    x87 FP Limitations:
//.. 
//..    * all arithmetic done at 64 bits
//.. 
//..    * no FP exceptions, except for handling stack over/underflow
//.. 
//..    * FP rounding mode observed only for float->int conversions
//..      and int->float conversions which could lose accuracy, and
//..      for float-to-float rounding.  For all other operations, 
//..      round-to-nearest is used, regardless.
//.. 
//..    * FP sin/cos/tan/sincos: C2 flag is always cleared.  IOW the
//..      simulation claims the argument is in-range (-2^63 <= arg <= 2^63)
//..      even when it isn't.
//.. 
//..    * some of the FCOM cases could do with testing -- not convinced
//..      that the args are the right way round.
//.. 
//..    * FSAVE does not re-initialise the FPU; it should do
//.. 
//..    * FINIT not only initialises the FPU environment, it also
//..      zeroes all the FP registers.  It should leave the registers
//..      unchanged.
//.. 
//..    RDTSC returns zero, always.
//.. 
//..    SAHF should cause eflags[1] == 1, and in fact it produces 0.  As
//..    per Intel docs this bit has no meaning anyway.  Since PUSHF is the
//..    only way to observe eflags[1], a proper fix would be to make that
//..    bit be set by PUSHF.
//.. 
//..    This module uses global variables and so is not MT-safe (if that
//..    should ever become relevant).  */

/* Translates AMD64 code to IR. */

#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"
#include "libvex_guest_amd64.h"

#include "main/vex_util.h"
#include "main/vex_globals.h"
#include "guest-amd64/gdefs.h"


/*------------------------------------------------------------*/
/*--- Globals                                              ---*/
/*------------------------------------------------------------*/

/* ------ CONST for entire BB ------ */

/* These are set at the start of the translation of a BB, so
   that we don't have to pass them around endlessly. */

/* We need to know this to do sub-register accesses correctly. */
/* CONST for entire BB */
static Bool host_is_bigendian;

/* Pointer to the guest code area. */
/* CONST for entire BB  */
static UChar* guest_code;

/* The guest address corresponding to guest_code[0]. */
/* CONST for entire BB  */
static Addr64 guest_rip_bbstart;

/* The IRBB* into which we're generating code. */
/* CONST for entire BB  */
static IRBB* irbb;


/* ------ CONST for each instruction ------ */

/* The guest address for the instruction currently being
   translated. */
/* CONST for any specific insn, not for the entire BB */
static Addr64 guest_rip_curr_instr;

/* Emergency verboseness just for this insn?  DEBUG ONLY */
static Bool  insn_verbose = False;


/* For ensuring that %rip-relative addressing is done right.  A read
   of %rip generates the address of the next instruction.  It may be
   that we don't conveniently know that inside disAMode().  For sanity
   checking, if the next insn %rip is needed, we make a guess at what
   it is, record that guess here, and set the accompanying Bool to
   indicate that -- after this insn's decode is finished -- that guess
   needs to be checked.  */

/* At the start of each insn decode, is set to (0, False).
   After the decode, if _mustcheck is now True, _assumed is
   checked. */

static Addr64 guest_rip_next_assumed;
static Bool   guest_rip_next_mustcheck;


/*------------------------------------------------------------*/
/*--- Helpers for constructing IR.                         ---*/
/*------------------------------------------------------------*/
 
/* Generate a new temporary of the given type. */
static IRTemp newTemp ( IRType ty )
{
   vassert(isPlausibleIRType(ty));
   return newIRTemp( irbb->tyenv, ty );
}

/* Add a statement to the list held by "irbb". */
static void stmt ( IRStmt* st )
{
   addStmtToIRBB( irbb, st );
}

/* Generate a statement "dst := e". */ 
static void assign ( IRTemp dst, IRExpr* e )
{
   stmt( IRStmt_Tmp(dst, e) );
}

static IRExpr* unop ( IROp op, IRExpr* a )
{
   return IRExpr_Unop(op, a);
}

static IRExpr* binop ( IROp op, IRExpr* a1, IRExpr* a2 )
{
   return IRExpr_Binop(op, a1, a2);
}

static IRExpr* mkexpr ( IRTemp tmp )
{
   return IRExpr_Tmp(tmp);
}

static IRExpr* mkU8 ( ULong i )
{
   vassert(i < 256);
   return IRExpr_Const(IRConst_U8( (UChar)i ));
}

static IRExpr* mkU16 ( ULong i )
{
   vassert(i < 0x10000ULL);
   return IRExpr_Const(IRConst_U16( (UShort)i ));
}

static IRExpr* mkU32 ( ULong i )
{
   vassert(i < 0x100000000ULL);
   return IRExpr_Const(IRConst_U32( (UInt)i ));
}

static IRExpr* mkU64 ( ULong i )
{
   return IRExpr_Const(IRConst_U64(i));
}

static IRExpr* mkU ( IRType ty, ULong i )
{
   switch (ty) {
      case Ity_I8:  return mkU8(i);
      case Ity_I16: return mkU16(i);
      case Ity_I32: return mkU32(i);
      case Ity_I64: return mkU64(i);
      default: vpanic("mkU(amd64)");
   }
}

static void storeLE ( IRExpr* addr, IRExpr* data )
{
   stmt( IRStmt_STle(addr,data) );
}

static IRExpr* loadLE ( IRType ty, IRExpr* data )
{
   return IRExpr_LDle(ty,data);
}

static IROp mkSizedOp ( IRType ty, IROp op8 )
{
   vassert(op8 == Iop_Add8 || op8 == Iop_Sub8 
           || op8 == Iop_Mul8 
           || op8 == Iop_Or8 || op8 == Iop_And8 || op8 == Iop_Xor8
           || op8 == Iop_Shl8 || op8 == Iop_Shr8 || op8 == Iop_Sar8
           || op8 == Iop_CmpEQ8 || op8 == Iop_CmpNE8
           || op8 == Iop_Not8 );
   switch (ty) {
      case Ity_I8:  return 0 +op8;
      case Ity_I16: return 1 +op8;
      case Ity_I32: return 2 +op8;
      case Ity_I64: return 3 +op8;
      default: vpanic("mkSizedOp(amd64)");
   }
}

static 
IRExpr* doScalarWidening ( Int szSmall, Int szBig, Bool signd, IRExpr* src )
{
   if (szSmall == 1 && szBig == 4) {
      return unop(signd ? Iop_8Sto32 : Iop_8Uto32, src);
   }
   if (szSmall == 1 && szBig == 2) {
      return unop(signd ? Iop_8Sto16 : Iop_8Uto16, src);
   }
   if (szSmall == 2 && szBig == 4) {
      return unop(signd ? Iop_16Sto32 : Iop_16Uto32, src);
   }
   if (szSmall == 1 && szBig == 8 && !signd) {
      return unop(Iop_32Uto64, unop(Iop_8Uto32, src));
   }
   if (szSmall == 1 && szBig == 8 && signd) {
      return unop(Iop_32Sto64, unop(Iop_8Sto32, src));
   }
   if (szSmall == 2 && szBig == 8 && !signd) {
      return unop(Iop_32Uto64, unop(Iop_16Uto32, src));
   }
   if (szSmall == 2 && szBig == 8 && signd) {
      return unop(Iop_32Sto64, unop(Iop_16Sto32, src));
   }
   vpanic("doScalarWidening(amd64)");
}



/*------------------------------------------------------------*/
/*--- Debugging output                                     ---*/
/*------------------------------------------------------------*/

/* Bomb out if we can't handle something. */
__attribute__ ((noreturn))
static void unimplemented ( HChar* str )
{
   vex_printf("amd64toIR: unimplemented feature\n");
   vpanic(str);
}

#define DIP(format, args...)           \
   if (insn_verbose || (vex_traceflags & VEX_TRACE_FE))  \
      vex_printf(format, ## args)

#define DIS(buf, format, args...)      \
   if (insn_verbose || (vex_traceflags & VEX_TRACE_FE))  \
      vex_sprintf(buf, format, ## args)


/*------------------------------------------------------------*/
/*--- Offsets of various parts of the amd64 guest state.   ---*/
/*------------------------------------------------------------*/

#define OFFB_RAX       offsetof(VexGuestAMD64State,guest_RAX)
#define OFFB_RBX       offsetof(VexGuestAMD64State,guest_RBX)
#define OFFB_RCX       offsetof(VexGuestAMD64State,guest_RCX)
#define OFFB_RDX       offsetof(VexGuestAMD64State,guest_RDX)
#define OFFB_RSP       offsetof(VexGuestAMD64State,guest_RSP)
#define OFFB_RBP       offsetof(VexGuestAMD64State,guest_RBP)
#define OFFB_RSI       offsetof(VexGuestAMD64State,guest_RSI)
#define OFFB_RDI       offsetof(VexGuestAMD64State,guest_RDI)
#define OFFB_R8        offsetof(VexGuestAMD64State,guest_R8)
#define OFFB_R9        offsetof(VexGuestAMD64State,guest_R9)
#define OFFB_R10       offsetof(VexGuestAMD64State,guest_R10)
#define OFFB_R11       offsetof(VexGuestAMD64State,guest_R11)
#define OFFB_R12       offsetof(VexGuestAMD64State,guest_R12)
#define OFFB_R13       offsetof(VexGuestAMD64State,guest_R13)
#define OFFB_R14       offsetof(VexGuestAMD64State,guest_R14)
#define OFFB_R15       offsetof(VexGuestAMD64State,guest_R15)

#define OFFB_RIP       offsetof(VexGuestAMD64State,guest_RIP)

#define OFFB_FS_ZERO   offsetof(VexGuestAMD64State,guest_FS_ZERO)

#define OFFB_CC_OP     offsetof(VexGuestAMD64State,guest_CC_OP)
#define OFFB_CC_DEP1   offsetof(VexGuestAMD64State,guest_CC_DEP1)
#define OFFB_CC_DEP2   offsetof(VexGuestAMD64State,guest_CC_DEP2)
#define OFFB_CC_NDEP   offsetof(VexGuestAMD64State,guest_CC_NDEP)

#define OFFB_FPREGS    offsetof(VexGuestAMD64State,guest_FPREG[0])
#define OFFB_FPTAGS    offsetof(VexGuestAMD64State,guest_FPTAG[0])
#define OFFB_DFLAG     offsetof(VexGuestAMD64State,guest_DFLAG)
#define OFFB_IDFLAG    offsetof(VexGuestAMD64State,guest_IDFLAG)
#define OFFB_FTOP      offsetof(VexGuestAMD64State,guest_FTOP)
//.. #define OFFB_FC3210    offsetof(VexGuestX86State,guest_FC3210)
#define OFFB_FPROUND   offsetof(VexGuestAMD64State,guest_FPROUND)
//.. 
//.. #define OFFB_CS        offsetof(VexGuestX86State,guest_CS)
//.. #define OFFB_DS        offsetof(VexGuestX86State,guest_DS)
//.. #define OFFB_ES        offsetof(VexGuestX86State,guest_ES)
//.. #define OFFB_FS        offsetof(VexGuestX86State,guest_FS)
//.. #define OFFB_GS        offsetof(VexGuestX86State,guest_GS)
//.. #define OFFB_SS        offsetof(VexGuestX86State,guest_SS)
//.. #define OFFB_LDT       offsetof(VexGuestX86State,guest_LDT)
//.. #define OFFB_GDT       offsetof(VexGuestX86State,guest_GDT)

#define OFFB_SSEROUND  offsetof(VexGuestAMD64State,guest_SSEROUND)
#define OFFB_XMM0      offsetof(VexGuestAMD64State,guest_XMM0)
#define OFFB_XMM1      offsetof(VexGuestAMD64State,guest_XMM1)
#define OFFB_XMM2      offsetof(VexGuestAMD64State,guest_XMM2)
#define OFFB_XMM3      offsetof(VexGuestAMD64State,guest_XMM3)
#define OFFB_XMM4      offsetof(VexGuestAMD64State,guest_XMM4)
#define OFFB_XMM5      offsetof(VexGuestAMD64State,guest_XMM5)
#define OFFB_XMM6      offsetof(VexGuestAMD64State,guest_XMM6)
#define OFFB_XMM7      offsetof(VexGuestAMD64State,guest_XMM7)
#define OFFB_XMM8      offsetof(VexGuestAMD64State,guest_XMM8)
#define OFFB_XMM9      offsetof(VexGuestAMD64State,guest_XMM9)
#define OFFB_XMM10     offsetof(VexGuestAMD64State,guest_XMM10)
#define OFFB_XMM11     offsetof(VexGuestAMD64State,guest_XMM11)
#define OFFB_XMM12     offsetof(VexGuestAMD64State,guest_XMM12)
#define OFFB_XMM13     offsetof(VexGuestAMD64State,guest_XMM13)
#define OFFB_XMM14     offsetof(VexGuestAMD64State,guest_XMM14)
#define OFFB_XMM15     offsetof(VexGuestAMD64State,guest_XMM15)

#define OFFB_EMWARN    offsetof(VexGuestAMD64State,guest_EMWARN)


/*------------------------------------------------------------*/
/*--- Disassemble an entire basic block                    ---*/
/*------------------------------------------------------------*/

/* The results of disassembling an instruction.  There are three
   possible outcomes.  For Dis_Resteer, the disassembler _must_
   continue at the specified address.  For Dis_StopHere, the
   disassembler _must_ terminate the BB.  For Dis_Continue, we may at
   our option either disassemble the next insn, or terminate the BB;
   but in the latter case we must set the bb's ->next field to point
   to the next instruction.  */

typedef
   enum { 
      Dis_StopHere, /* this insn terminates the BB; we must stop. */
      Dis_Continue, /* we can optionally continue into the next insn */
      Dis_Resteer   /* followed a branch; continue at the spec'd addr */
   }
   DisResult;


/* forward decls .. */
//.. static IRExpr* mkU32 ( UInt i );
//.. static void stmt ( IRStmt* st );
//.. 
//.. 
/* disInstr disassembles an instruction located at &guest_code[delta],
   and sets *size to its size.  If the returned value is Dis_Resteer,
   the next guest address is assigned to *whereNext.  disInstr is not
   permitted to return Dis_Resteer if either (1) resteerOK is False,
   or (2) resteerOkFn, when applied to the address which it wishes to
   resteer into, returns False.  */
   
static 
DisResult disInstr ( /*IN*/  Bool       resteerOK,
                     /*IN*/  Bool       (*resteerOkFn) ( Addr64 ),
                     /*IN*/  ULong      delta, 
                     /*IN*/  VexSubArch subarch,
                     /*OUT*/ Long*      size,
                     /*OUT*/ Addr64*    whereNext );


/* This is the main (only, in fact) entry point for this module. */

/* Disassemble a complete basic block, starting at eip, and dumping
   the ucode into cb.  Returns the size, in bytes, of the basic
   block. */
IRBB* bbToIR_AMD64 ( UChar*           amd64code, 
                     Addr64           guest_rip_start, 
                     VexGuestExtents* vge, 
                     Bool             (*byte_accessible)(Addr64),
                     Bool             (*chase_into_ok)(Addr64),
                     Bool             host_bigendian,
                     VexSubArch       subarch_guest )
{
   Long       delta, size;
   Int        i, n_instrs, first_stmt_idx;
   Addr64     guest_next;
   Bool       resteerOK;
   DisResult  dres;
   IRStmt*    imark;
   static Int n_resteers = 0;
   Int        d_resteers = 0;

   /* check sanity .. */
   vassert(vex_control.guest_max_insns >= 1);
   vassert(vex_control.guest_max_insns < 500);
   vassert(vex_control.guest_chase_thresh >= 0);
   vassert(vex_control.guest_chase_thresh < vex_control.guest_max_insns);

   vassert(subarch_guest == VexSubArch_NONE);

   /* Start a new, empty extent. */
   vge->n_used  = 1;
   vge->base[0] = guest_rip_start;
   vge->len[0]  = 0;

   /* Set up globals. */
   host_is_bigendian = host_bigendian;
   guest_code        = amd64code;
   guest_rip_bbstart = guest_rip_start;
   irbb              = emptyIRBB();
   insn_verbose      = False;

   /* Delta keeps track of how far along the amd64code array we
      have so far gone. */
   delta             = 0;
   n_instrs          = 0;

   while (True) {
      vassert(n_instrs < vex_control.guest_max_insns);

      guest_next = 0;
      resteerOK 
         = toBool(
              n_instrs < vex_control.guest_chase_thresh
              /* we can't afford to have a resteer once we're on the
                 last extent slot. */
              && vge->n_used < 3
           );

      /* This is the %RIP of the instruction we're just about to deal
         with. */
      guest_rip_curr_instr = guest_rip_bbstart + delta;

      /* This is the irbb statement array index of the first stmt in
         this insn.  That will always be the instruction-mark
         descriptor. */
      first_stmt_idx = irbb->stmts_used;

      /* Add an instruction-mark statement.  We won't know until after
         disInstr how long the instruction is, so just put in a zero
         length and we'll fix it up later. */
      stmt( IRStmt_IMark( guest_rip_curr_instr, 0 ));

      if (n_instrs > 0) {
         /* for the first insn, the dispatch loop will have set
            %RIP, but for all the others we have to do it ourselves. */
         stmt( IRStmt_Put( OFFB_RIP, mkU64(guest_rip_curr_instr)) );
      }

      /* Do the instruction.  This may set insn_verbose to True, which
         needs to be annulled. */
      size = 0; /* just in case disInstr doesn't set it */
      guest_rip_next_assumed = 0;
      guest_rip_next_mustcheck = False;
      dres = disInstr( resteerOK, chase_into_ok, 
                       delta, subarch_guest, &size, &guest_next );
      insn_verbose = False;

      /* stay sane ... */
      vassert(size >= 0 && size <= 18);

      /* Fill in the insn-mark length field. */
      vassert(first_stmt_idx >= 0 && first_stmt_idx < irbb->stmts_used);
      imark = irbb->stmts[first_stmt_idx];
      vassert(imark);
      vassert(imark->tag == Ist_IMark);
      vassert(imark->Ist.IMark.len == 0);
      imark->Ist.IMark.len = toUInt(size);

      /* Print the resulting IR, if needed. */
      if (vex_traceflags & VEX_TRACE_FE) {
         for (i = first_stmt_idx; i < irbb->stmts_used; i++) {
            vex_printf("              ");
            ppIRStmt(irbb->stmts[i]);
            vex_printf("\n");
         }
      }

      /* If disInstr tried to figure out the next rip, check it got it
	 right.  Failure of this assertion is serious and denotes a
	 bug in disInstr. */
      if (guest_rip_next_mustcheck 
          && guest_rip_next_assumed != guest_rip_curr_instr+size) {
         vex_printf("\n");
         vex_printf("assumed next %%rip = 0x%llx\n", 
                    guest_rip_next_assumed );
         vex_printf(" actual next %%rip = 0x%llx\n", 
                    guest_rip_curr_instr+size );
         vpanic("bbToIR_AMD64: disInstr miscalculated next %rip");
      }

      if (dres == Dis_StopHere) {
         vassert(irbb->next != NULL);
         if (vex_traceflags & VEX_TRACE_FE) {
            vex_printf("              ");
            vex_printf( "goto {");
            ppIRJumpKind(irbb->jumpkind);
            vex_printf( "} ");
            ppIRExpr( irbb->next );
            vex_printf( "\n");
         }
      }

      delta += size;
      /* If vex_control.guest_max_insns is required to be < 500 and
	 each insn is at max 15 bytes long, this limit of 10000 then
	 seems reasonable since the max possible extent length will be
	 500 * 15 == 7500. */
      vassert(vge->len[vge->n_used-1] < 10000);
      vge->len[vge->n_used-1] 
         = toUShort(toUInt( vge->len[vge->n_used-1] + size ));
      n_instrs++;
      DIP("\n");

      if (!resteerOK) 
         vassert(dres != Dis_Resteer);
      if (dres != Dis_Resteer) 
         vassert(guest_next == 0);

      switch (dres) {
         case Dis_Continue:
            vassert(irbb->next == NULL);
            if (n_instrs < vex_control.guest_max_insns) {
               /* keep going */
            } else {
               irbb->next = mkU64(guest_rip_start+delta);
               return irbb;
            }
            break;
         case Dis_StopHere:
            vassert(irbb->next != NULL);
            return irbb;
         case Dis_Resteer:
            vassert(irbb->next == NULL);
            /* figure out a new delta to continue at. */
            vassert(chase_into_ok(guest_next));
            delta = guest_next - guest_rip_start;
            /* we now have to start a new extent slot. */
	    vge->n_used++;
	    vassert(vge->n_used <= 3);
            vge->base[vge->n_used-1] = guest_next;
            vge->len[vge->n_used-1] = 0;
            n_resteers++;
            d_resteers++;
            if (0 && (n_resteers & 0xFF) == 0)
            vex_printf("resteer[%d,%d] to 0x%llx (delta = %lld)\n",
                       n_resteers, d_resteers,
                       guest_next, delta);
            break;
      }
   }
}


/*------------------------------------------------------------*/
/*--- Helper bits and pieces for deconstructing the        ---*/
/*--- amd64 insn stream.                                   ---*/
/*------------------------------------------------------------*/

/* This is the AMD64 register encoding -- integer regs. */
#define R_RAX 0
#define R_RCX 1
#define R_RDX 2
#define R_RBX 3
#define R_RSP 4
#define R_RBP 5
#define R_RSI 6
#define R_RDI 7
#define R_R8  8
#define R_R9  9
#define R_R10 10
#define R_R11 11
#define R_R12 12
#define R_R13 13
#define R_R14 14
#define R_R15 15

//.. #define R_AL (0+R_EAX)
//.. #define R_AH (4+R_EAX)

/* This is the Intel register encoding -- segment regs. */
#define R_ES 0
#define R_CS 1
#define R_SS 2
#define R_DS 3
#define R_FS 4
#define R_GS 5


/* Various simple conversions */

static ULong extend_s_8to64 ( UChar x )
{
   return (ULong)((((Long)x) << 56) >> 56);
}

static ULong extend_s_16to64 ( UShort x )
{
   return (ULong)((((Long)x) << 48) >> 48);
}

static ULong extend_s_32to64 ( UInt x )
{
   return (ULong)((((Long)x) << 32) >> 32);
}

/* Figure out whether the mod and rm parts of a modRM byte refer to a
   register or memory.  If so, the byte will have the form 11XXXYYY,
   where YYY is the register number. */
inline
static Bool epartIsReg ( UChar mod_reg_rm )
{
   return toBool(0xC0 == (mod_reg_rm & 0xC0));
}

/* Extract the 'g' field from a modRM byte.  This only produces 3
   bits, which is not a complete register number.  You should avoid
   this function if at all possible. */
inline
static Int gregLO3ofRM ( UChar mod_reg_rm )
{
   return (Int)( (mod_reg_rm >> 3) & 7 );
}

/* Get a 8/16/32-bit unsigned value out of the insn stream. */

static UChar getUChar ( ULong delta )
{
   UChar v = guest_code[delta+0];
   return v;
}

//.. static UInt getUDisp16 ( ULong delta )
//.. {
//..    UInt v = guest_code[delta+1]; v <<= 8;
//..    v |= guest_code[delta+0];
//..    return v & 0xFFFF;
//.. }
//.. 
//.. static UInt getUDisp ( Int size, ULong delta )
//.. {
//..    switch (size) {
//..       case 4: return getUDisp32(delta);
//..       case 2: return getUDisp16(delta);
//..       case 1: return getUChar(delta);
//..       default: vpanic("getUDisp(x86)");
//..    }
//..    return 0; /*notreached*/
//.. }


/* Get a byte value out of the insn stream and sign-extend to 64
   bits. */
static Long getSDisp8 ( ULong delta )
{
   return extend_s_8to64( guest_code[delta] );
}

/* Get a 16-bit value out of the insn stream and sign-extend to 64
   bits. */
static Long getSDisp16 ( ULong delta )
{
   UInt v = guest_code[delta+1]; v <<= 8;
   v |= guest_code[delta+0];
   return extend_s_16to64( (UShort)v );
}

/* Get a 32-bit value out of the insn stream and sign-extend to 64
   bits. */
static Long getSDisp32 ( ULong delta )
{
   UInt v = guest_code[delta+3]; v <<= 8;
   v |= guest_code[delta+2]; v <<= 8;
   v |= guest_code[delta+1]; v <<= 8;
   v |= guest_code[delta+0];
   return extend_s_32to64( v );
}

/* Get a 64-bit value out of the insn stream. */
static Long getDisp64 ( ULong delta )
{
   ULong v = 0;
   v |= guest_code[delta+7]; v <<= 8;
   v |= guest_code[delta+6]; v <<= 8;
   v |= guest_code[delta+5]; v <<= 8;
   v |= guest_code[delta+4]; v <<= 8;
   v |= guest_code[delta+3]; v <<= 8;
   v |= guest_code[delta+2]; v <<= 8;
   v |= guest_code[delta+1]; v <<= 8;
   v |= guest_code[delta+0];
   return v;
}

/* Note: because AMD64 doesn't allow 64-bit literals, it is an error
   if this is called with size==8.  Should not happen. */
static Long getSDisp ( Int size, ULong delta )
{
   switch (size) {
      case 4: return getSDisp32(delta);
      case 2: return getSDisp16(delta);
      case 1: return getSDisp8(delta);
      default: vpanic("getSDisp(amd64)");
  }
}

static ULong mkSizeMask ( Int sz )
{
   switch (sz) {
      case 1: return 0x00000000000000FFULL;
      case 2: return 0x000000000000FFFFULL;
      case 4: return 0x00000000FFFFFFFFULL;
      case 8: return 0xFFFFFFFFFFFFFFFFULL;
      default: vpanic("mkSzMask(amd64)");
   }
}

static Int imin ( Int a, Int b )
{
   return (a < b) ? a : b;
}

static IRType szToITy ( Int n )
{
   switch (n) {
      case 1: return Ity_I8;
      case 2: return Ity_I16;
      case 4: return Ity_I32;
      case 8: return Ity_I64;
      default: vex_printf("\nszToITy(%d)\n", n);
               vpanic("szToITy(amd64)");
   }
}


/*------------------------------------------------------------*/
/*--- For dealing with prefixes.                           ---*/
/*------------------------------------------------------------*/

/* The idea is to pass around an int holding a bitmask summarising
   info from the prefixes seen on the current instruction, including
   info from the REX byte.  This info is used in various places, but
   most especially when making sense of register fields in
   instructions.

   The top 16 bits of the prefix are 0x3141, just as a hacky way
   to ensure it really is a valid prefix.

   Things you can safely assume about a well-formed prefix:
   * at most one segment-override bit (CS,DS,ES,FS,GS,SS) is set.
   * if REX is not present then REXW,REXR,REXX,REXB will read
     as zero.
   * F2 and F3 will not both be 1.
*/

typedef UInt  Prefix;

#define PFX_ASO   (1<<0)     /* address-size override present (0x67) */
#define PFX_66    (1<<1)     /* operand-size override-to-16 present (0x66) */
#define PFX_REX   (1<<2)     /* REX byte present (0x40 to 0x4F) */
#define PFX_REXW  (1<<3)     /* REX W bit, if REX present, else 0 */
#define PFX_REXR  (1<<4)     /* REX R bit, if REX present, else 0 */
#define PFX_REXX  (1<<5)     /* REX X bit, if REX present, else 0 */
#define PFX_REXB  (1<<6)     /* REX B bit, if REX present, else 0 */
#define PFX_LOCK  (1<<7)     /* bus LOCK prefix present (0xF0) */
#define PFX_F2    (1<<8)     /* REP/REPE/REPZ prefix present (0xF2) */
#define PFX_F3    (1<<9)     /* REPNE/REPNZ prefix present (0xF3) */
#define PFX_CS    (1<<10)    /* CS segment prefix present (0x2E) */
#define PFX_DS    (1<<11)    /* DS segment prefix present (0x3E) */
#define PFX_ES    (1<<12)    /* ES segment prefix present (0x26) */
#define PFX_FS    (1<<13)    /* FS segment prefix present (0x64) */
#define PFX_GS    (1<<14)    /* GS segment prefix present (0x65) */
#define PFX_SS    (1<<15)    /* SS segment prefix present (0x36) */

#define PFX_EMPTY 0x31410000

static Bool IS_VALID_PFX ( Prefix pfx ) {
   return toBool((pfx & 0xFFFF0000) == PFX_EMPTY);
}

static Bool haveREX ( Prefix pfx ) {
   return toBool(pfx & PFX_REX);
}

static Int getRexW ( Prefix pfx ) {
   return (pfx & PFX_REXW) ? 1 : 0;
}
/* Apparently unused.
static Int getRexR ( Prefix pfx ) {
   return (pfx & PFX_REXR) ? 1 : 0;
}
*/
static Int getRexX ( Prefix pfx ) {
   return (pfx & PFX_REXX) ? 1 : 0;
}
static Int getRexB ( Prefix pfx ) {
   return (pfx & PFX_REXB) ? 1 : 0;
}

/* Check a prefix doesn't have F2 or F3 set in it, since usually that
   completely changes what instruction it really is. */
static Bool haveF2orF3 ( Prefix pfx ) {
   return toBool((pfx & (PFX_F2|PFX_F3)) > 0);
}
static Bool haveF2 ( Prefix pfx ) {
   return toBool((pfx & PFX_F2) > 0);
}
static Bool haveF3 ( Prefix pfx ) {
   return toBool((pfx & PFX_F3) > 0);
}

/* Return True iff pfx has 66 set and F2 and F3 clear */
static Bool have66noF2noF3 ( Prefix pfx )
{
  return 
     toBool((pfx & (PFX_66|PFX_F2|PFX_F3)) == PFX_66);
}

/* Return True iff pfx has F2 set and 66 and F3 clear */
static Bool haveF2no66noF3 ( Prefix pfx )
{
  return 
     toBool((pfx & (PFX_66|PFX_F2|PFX_F3)) == PFX_F2);
}

/* Return True iff pfx has F3 set and 66 and F2 clear */
static Bool haveF3no66noF2 ( Prefix pfx )
{
  return 
     toBool((pfx & (PFX_66|PFX_F2|PFX_F3)) == PFX_F3);
}

/* Return True iff pfx has 66, F2 and F3 clear */
static Bool haveNo66noF2noF3 ( Prefix pfx )
{
  return 
     toBool((pfx & (PFX_66|PFX_F2|PFX_F3)) == 0);
}

/* Clear all the segment-override bits in a prefix. */
static Prefix clearSegBits ( Prefix p )
{
   return 
      p & ~(PFX_CS | PFX_DS | PFX_ES | PFX_FS | PFX_GS | PFX_SS);
}


/*------------------------------------------------------------*/
/*--- For dealing with integer registers                   ---*/
/*------------------------------------------------------------*/

/* This is somewhat complex.  The rules are:

   For 64, 32 and 16 bit register references, the e or g fields in the
   modrm bytes supply the low 3 bits of the register number.  The
   fourth (most-significant) bit of the register number is supplied by
   the REX byte, if it is present; else that bit is taken to be zero.

   The REX.R bit supplies the high bit corresponding to the g register
   field, and the REX.B bit supplies the high bit corresponding to the
   e register field (when the mod part of modrm indicates that modrm's
   e component refers to a register and not to memory).

   The REX.X bit supplies a high register bit for certain registers
   in SIB address modes, and is generally rarely used.

   For 8 bit register references, the presence of the REX byte itself
   has significance.  If there is no REX present, then the 3-bit
   number extracted from the modrm e or g field is treated as an index
   into the sequence %al %cl %dl %bl %ah %ch %dh %bh -- that is, the
   old x86 encoding scheme.

   But if there is a REX present, the register reference is
   interpreted in the same way as for 64/32/16-bit references: a high
   bit is extracted from REX, giving a 4-bit number, and the denoted
   register is the lowest 8 bits of the 16 integer registers denoted
   by the number.  In particular, values 3 through 7 of this sequence
   do not refer to %ah %ch %dh %bh but instead to the lowest 8 bits of
   %rsp %rbp %rsi %rdi.

   The REX.W bit has no bearing at all on register numbers.  Instead
   its presence indicates that the operand size is to be overridden
   from its default value (32 bits) to 64 bits instead.  This is in
   the same fashion that an 0x66 prefix indicates the operand size is
   to be overridden from 32 bits down to 16 bits.  When both REX.W and
   0x66 are present there is a conflict, and REX.W takes precedence.

   Rather than try to handle this complexity using a single huge
   function, several smaller ones are provided.  The aim is to make it
   as difficult as possible to screw up register decoding in a subtle
   and hard-to-track-down way.

   Because these routines fish around in the host's memory (that is,
   in the guest state area) for sub-parts of guest registers, their
   correctness depends on the host's endianness.  So far these
   routines only work for little-endian hosts.  Those for which
   endianness is important have assertions to ensure sanity.
*/


/* About the simplest question you can ask: where do the 64-bit
   integer registers live (in the guest state) ? */

static Int integerGuestReg64Offset ( UInt reg )
{
   switch (reg) {
      case R_RAX: return OFFB_RAX;
      case R_RCX: return OFFB_RCX;
      case R_RDX: return OFFB_RDX;
      case R_RBX: return OFFB_RBX;
      case R_RSP: return OFFB_RSP;
      case R_RBP: return OFFB_RBP;
      case R_RSI: return OFFB_RSI;
      case R_RDI: return OFFB_RDI;
      case R_R8:  return OFFB_R8;
      case R_R9:  return OFFB_R9;
      case R_R10: return OFFB_R10;
      case R_R11: return OFFB_R11;
      case R_R12: return OFFB_R12;
      case R_R13: return OFFB_R13;
      case R_R14: return OFFB_R14;
      case R_R15: return OFFB_R15;
      default: vpanic("integerGuestReg64Offset(amd64)");
   }
}


/* Produce the name of an integer register, for printing purposes.
   reg is a number in the range 0 .. 15 that has been generated from a
   3-bit reg-field number and a REX extension bit.  irregular denotes
   the case where sz==1 and no REX byte is present. */

static 
HChar* nameIReg ( Int sz, UInt reg, Bool irregular )
{
   static HChar* ireg64_names[16]
     = { "%rax", "%rcx", "%rdx", "%rbx", "%rsp", "%rbp", "%rsi", "%rdi",
         "%r8",  "%r9",  "%r10", "%r11", "%r12", "%r13", "%r14", "%r15" };
   static HChar* ireg32_names[16]
     = { "%eax", "%ecx", "%edx", "%ebx", "%esp", "%ebp", "%esi", "%edi",
         "%r8d", "%r9d", "%r10d","%r11d","%r12d","%r13d","%r14d","%r15d" };
   static HChar* ireg16_names[16]
     = { "%ax",  "%cx",  "%dx",  "%bx",  "%sp",  "%bp",  "%si",  "%di",
         "%r8w", "%r9w", "%r10w","%r11w","%r12w","%r13w","%r14w","%r15w" };
   static HChar* ireg8_names[16]
     = { "%al",  "%cl",  "%dl",  "%bl",  "%spl", "%bpl", "%sil", "%dil",
         "%r8b", "%r9b", "%r10b","%r11b","%r12b","%r13b","%r14b","%r15b" };
   static HChar* ireg8_irregular[8] 
     = { "%al", "%cl", "%dl", "%bl", "%ah", "%ch", "%dh", "%bh" };

   vassert(reg < 16);
   if (sz == 1) {
      if (irregular)
         vassert(reg < 8);
   } else {
      vassert(irregular == False);
   }

   switch (sz) {
      case 8: return ireg64_names[reg];
      case 4: return ireg32_names[reg];
      case 2: return ireg16_names[reg];
      case 1: if (irregular) {
                 return ireg8_irregular[reg];
              } else {
                 return ireg8_names[reg];
              }
      default: vpanic("nameIReg(amd64)");
   }
}

/* Using the same argument conventions as nameIReg, produce the
   guest state offset of an integer register. */

static 
Int offsetIReg ( Int sz, UInt reg, Bool irregular )
{
   vassert(reg < 16);
   if (sz == 1) {
      if (irregular)
         vassert(reg < 8);
   } else {
      vassert(irregular == False);
   }

   /* Deal with irregular case -- sz==1 and no REX present */
   if (sz == 1 && irregular) {
      switch (reg) {
         case R_RSP: return 1+ OFFB_RAX;
         case R_RBP: return 1+ OFFB_RCX;
         case R_RSI: return 1+ OFFB_RDX;
         case R_RDI: return 1+ OFFB_RBX;
         default:    break; /* use the normal case */
      }
   }

   /* Normal case */
   return integerGuestReg64Offset(reg);
}


/* Read the %CL register :: Ity_I8, for shift/rotate operations. */

static IRExpr* getIRegCL ( void )
{
   vassert(!host_is_bigendian);
   return IRExpr_Get( OFFB_RCX, Ity_I8 );
}


/* Write to the %AH register. */

static void putIRegAH ( IRExpr* e )
{
   vassert(!host_is_bigendian);
   vassert(typeOfIRExpr(irbb->tyenv, e) == Ity_I8);
   stmt( IRStmt_Put( OFFB_RAX+1, e ) );
}


/* Read/write various widths of %RAX, as it has various
   special-purpose uses. */

static HChar* nameIRegRAX ( Int sz )
{
   switch (sz) {
      case 1: return "%al";
      case 2: return "%ax";
      case 4: return "%eax";
      case 8: return "%rax";
      default: vpanic("nameIRegRAX(amd64)");
   }
}

static IRExpr* getIRegRAX ( Int sz )
{
   vassert(!host_is_bigendian);
   switch (sz) {
      case 1: return IRExpr_Get( OFFB_RAX, Ity_I8 );
      case 2: return IRExpr_Get( OFFB_RAX, Ity_I16 );
      case 4: return IRExpr_Get( OFFB_RAX, Ity_I32 );
      case 8: return IRExpr_Get( OFFB_RAX, Ity_I64 );
      default: vpanic("getIRegRAX(amd64)");
   }
}

static void putIRegRAX ( Int sz, IRExpr* e )
{
   IRType ty = typeOfIRExpr(irbb->tyenv, e);
   vassert(!host_is_bigendian);
   switch (sz) {
      case 8: vassert(ty == Ity_I64);
              stmt( IRStmt_Put( OFFB_RAX, e ));
              break;
      case 4: vassert(ty == Ity_I32);
              stmt( IRStmt_Put( OFFB_RAX, unop(Iop_32Uto64,e) ));
              break;
      case 2: vassert(ty == Ity_I16);
              stmt( IRStmt_Put( OFFB_RAX, e ));
              break;
      case 1: vassert(ty == Ity_I8);
              stmt( IRStmt_Put( OFFB_RAX, e ));
              break;
      default: vpanic("putIRegRAX(amd64)");
   }
}


/* Read/write various widths of %RDX, as it has various
   special-purpose uses. */

static IRExpr* getIRegRDX ( Int sz )
{
   vassert(!host_is_bigendian);
   switch (sz) {
      case 1: return IRExpr_Get( OFFB_RDX, Ity_I8 );
      case 2: return IRExpr_Get( OFFB_RDX, Ity_I16 );
      case 4: return IRExpr_Get( OFFB_RDX, Ity_I32 );
      case 8: return IRExpr_Get( OFFB_RDX, Ity_I64 );
      default: vpanic("getIRegRDX(amd64)");
   }
}

static void putIRegRDX ( Int sz, IRExpr* e )
{
   vassert(!host_is_bigendian);
   vassert(typeOfIRExpr(irbb->tyenv, e) == szToITy(sz));
   switch (sz) {
      case 8: stmt( IRStmt_Put( OFFB_RDX, e ));
              break;
      case 4: stmt( IRStmt_Put( OFFB_RDX, unop(Iop_32Uto64,e) ));
              break;
      case 2: stmt( IRStmt_Put( OFFB_RDX, e ));
              break;
      case 1: stmt( IRStmt_Put( OFFB_RDX, e ));
              break;
      default: vpanic("putIRegRDX(amd64)");
   }
}


/* Simplistic functions to deal with the integer registers as a
   straightforward bank of 16 64-bit regs. */

static IRExpr* getIReg64 ( UInt regno )
{
   return IRExpr_Get( integerGuestReg64Offset(regno),
                      Ity_I64 );
}

static void putIReg64 ( UInt regno, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I64);
   stmt( IRStmt_Put( integerGuestReg64Offset(regno), e ) );
}

static HChar* nameIReg64 ( UInt regno )
{
   return nameIReg( 8, regno, False );
}


/* Simplistic functions to deal with the lower halves of integer
   registers as a straightforward bank of 16 32-bit regs. */

static IRExpr* getIReg32 ( UInt regno )
{
   vassert(!host_is_bigendian);
   return IRExpr_Get( integerGuestReg64Offset(regno),
                      Ity_I32 );
}

static void putIReg32 ( UInt regno, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I32);
   stmt( IRStmt_Put( integerGuestReg64Offset(regno), 
                     unop(Iop_32Uto64,e) ) );
}

static HChar* nameIReg32 ( UInt regno )
{
   return nameIReg( 4, regno, False );
}


/* Sometimes what we know is a 3-bit register number, a REX byte, and
   which field of the REX byte is to be used to extend to a 4-bit
   number.  These functions cater for that situation.  
*/
static IRExpr* getIReg64rexX ( Prefix pfx, UInt lo3bits )
{
   vassert(lo3bits < 8);
   vassert(IS_VALID_PFX(pfx));
   return getIReg64( lo3bits | (getRexX(pfx) << 3) );
}

static HChar* nameIReg64rexX ( Prefix pfx, UInt lo3bits )
{
   vassert(lo3bits < 8);
   vassert(IS_VALID_PFX(pfx));
   return nameIReg( 8, lo3bits | (getRexX(pfx) << 3), False );
}

static HChar* nameIRegRexB ( Int sz, Prefix pfx, UInt lo3bits )
{
   vassert(lo3bits < 8);
   vassert(IS_VALID_PFX(pfx));
   vassert(sz == 8 || sz == 4 || sz == 2 || sz == 1);
   return nameIReg( sz, lo3bits | (getRexB(pfx) << 3), 
                        toBool(sz==1 && !haveREX(pfx)) );
}

static IRExpr* getIRegRexB ( Int sz, Prefix pfx, UInt lo3bits )
{
   vassert(lo3bits < 8);
   vassert(IS_VALID_PFX(pfx));
   vassert(sz == 8 || sz == 4 || sz == 2 || sz == 1);
   return IRExpr_Get(
             offsetIReg( sz, lo3bits | (getRexB(pfx) << 3), 
                             toBool(sz==1 && !haveREX(pfx)) ),
             szToITy(sz)
          );
}

static void putIRegRexB ( Int sz, Prefix pfx, UInt lo3bits, IRExpr* e )
{
   vassert(lo3bits < 8);
   vassert(IS_VALID_PFX(pfx));
   vassert(typeOfIRExpr(irbb->tyenv, e) == szToITy(sz));
   stmt( IRStmt_Put( 
            offsetIReg( sz, lo3bits | (getRexB(pfx) << 3), 
                            toBool(sz==1 && !haveREX(pfx)) ),
            sz==4 ? unop(Iop_32Uto64,e) : e
   ));
}


/* Functions for getting register numbers from modrm bytes and REX
   when we don't have to consider the complexities of integer subreg
   accesses.
*/
/* Extract the g reg field from a modRM byte, and augment it using the
   REX.R bit from the supplied REX byte.  The R bit usually is
   associated with the g register field.
*/
static UInt gregOfRexRM ( Prefix pfx, UChar mod_reg_rm )
{
   Int reg = (Int)( (mod_reg_rm >> 3) & 7 );
   reg += (pfx & PFX_REXR) ? 8 : 0;
   return reg;
}

/* Extract the e reg field from a modRM byte, and augment it using the
   REX.B bit from the supplied REX byte.  The B bit usually is
   associated with the e register field (when modrm indicates e is a
   register, that is).
*/
static UInt eregOfRexRM ( Prefix pfx, UChar mod_reg_rm )
{
   Int rm;
   vassert(epartIsReg(mod_reg_rm));
   rm = (Int)(mod_reg_rm & 0x7);
   rm += (pfx & PFX_REXB) ? 8 : 0;
   return rm;
}


/* General functions for dealing with integer register access. */

/* Produce the guest state offset for a reference to the 'g' register
   field in a modrm byte, taking into account REX (or its absence),
   and the size of the access.
*/
static UInt offsetIRegG ( Int sz, Prefix pfx, UChar mod_reg_rm )
{
   UInt reg;
   vassert(!host_is_bigendian);
   vassert(IS_VALID_PFX(pfx));
   vassert(sz == 8 || sz == 4 || sz == 2 || sz == 1);
   reg = gregOfRexRM( pfx, mod_reg_rm );
   return offsetIReg( sz, reg, toBool(sz == 1 && !haveREX(pfx)) );
}

static 
IRExpr* getIRegG ( Int sz, Prefix pfx, UChar mod_reg_rm )
{
   return IRExpr_Get( offsetIRegG( sz, pfx, mod_reg_rm ),
                      szToITy(sz) );
}

static 
void putIRegG ( Int sz, Prefix pfx, UChar mod_reg_rm, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == szToITy(sz));
   if (sz == 4) {
      e = unop(Iop_32Uto64,e);
   }
   stmt( IRStmt_Put( offsetIRegG( sz, pfx, mod_reg_rm ), e ) );
}

static
HChar* nameIRegG ( Int sz, Prefix pfx, UChar mod_reg_rm )
{
   return nameIReg( sz, gregOfRexRM(pfx,mod_reg_rm),
                        toBool(sz==1 && !haveREX(pfx)) );
}


/* Produce the guest state offset for a reference to the 'e' register
   field in a modrm byte, taking into account REX (or its absence),
   and the size of the access.  eregOfRexRM will assert if mod_reg_rm
   denotes a memory access rather than a register access.
*/
static UInt offsetIRegE ( Int sz, Prefix pfx, UChar mod_reg_rm )
{
   UInt reg;
   vassert(!host_is_bigendian);
   vassert(IS_VALID_PFX(pfx));
   vassert(sz == 8 || sz == 4 || sz == 2 || sz == 1);
   reg = eregOfRexRM( pfx, mod_reg_rm );
   return offsetIReg( sz, reg, toBool(sz == 1 && !haveREX(pfx)) );
}

static 
IRExpr* getIRegE ( Int sz, Prefix pfx, UChar mod_reg_rm )
{
   return IRExpr_Get( offsetIRegE( sz, pfx, mod_reg_rm ),
                      szToITy(sz) );
}

static 
void putIRegE ( Int sz, Prefix pfx, UChar mod_reg_rm, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == szToITy(sz));
   if (sz == 4) {
      e = unop(Iop_32Uto64,e);
   }
   stmt( IRStmt_Put( offsetIRegE( sz, pfx, mod_reg_rm ), e ) );
}

static
HChar* nameIRegE ( Int sz, Prefix pfx, UChar mod_reg_rm )
{
   return nameIReg( sz, eregOfRexRM(pfx,mod_reg_rm),
                        toBool(sz==1 && !haveREX(pfx)) );
}


/*------------------------------------------------------------*/
/*--- For dealing with XMM registers                       ---*/
/*------------------------------------------------------------*/

//.. static Int segmentGuestRegOffset ( UInt sreg )
//.. {
//..    switch (sreg) {
//..       case R_ES: return OFFB_ES;
//..       case R_CS: return OFFB_CS;
//..       case R_SS: return OFFB_SS;
//..       case R_DS: return OFFB_DS;
//..       case R_FS: return OFFB_FS;
//..       case R_GS: return OFFB_GS;
//..       default: vpanic("segmentGuestRegOffset(x86)");
//..    }
//.. }

static Int xmmGuestRegOffset ( UInt xmmreg )
{
   switch (xmmreg) {
      case 0:  return OFFB_XMM0;
      case 1:  return OFFB_XMM1;
      case 2:  return OFFB_XMM2;
      case 3:  return OFFB_XMM3;
      case 4:  return OFFB_XMM4;
      case 5:  return OFFB_XMM5;
      case 6:  return OFFB_XMM6;
      case 7:  return OFFB_XMM7;
      case 8:  return OFFB_XMM8;
      case 9:  return OFFB_XMM9;
      case 10: return OFFB_XMM10;
      case 11: return OFFB_XMM11;
      case 12: return OFFB_XMM12;
      case 13: return OFFB_XMM13;
      case 14: return OFFB_XMM14;
      case 15: return OFFB_XMM15;
      default: vpanic("xmmGuestRegOffset(amd64)");
   }
}

//.. /* Lanes of vector registers are always numbered from zero being the
//..    least significant lane (rightmost in the register).  */
//.. 
//.. static Int xmmGuestRegLane16offset ( UInt xmmreg, Int laneno )
//.. {
//..    /* Correct for little-endian host only. */
//..    vassert(!host_is_bigendian);
//..    vassert(laneno >= 0 && laneno < 8);
//..    return xmmGuestRegOffset( xmmreg ) + 2 * laneno;
//.. }

static Int xmmGuestRegLane32offset ( UInt xmmreg, Int laneno )
{
   /* Correct for little-endian host only. */
   vassert(!host_is_bigendian);
   vassert(laneno >= 0 && laneno < 4);
   return xmmGuestRegOffset( xmmreg ) + 4 * laneno;
}

static Int xmmGuestRegLane64offset ( UInt xmmreg, Int laneno )
{
   /* Correct for little-endian host only. */
   vassert(!host_is_bigendian);
   vassert(laneno >= 0 && laneno < 2);
   return xmmGuestRegOffset( xmmreg ) + 8 * laneno;
}

//.. static IRExpr* getSReg ( UInt sreg )
//.. {
//..    return IRExpr_Get( segmentGuestRegOffset(sreg), Ity_I16 );
//.. }
//.. 
//.. static void putSReg ( UInt sreg, IRExpr* e )
//.. {
//..    vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I16);
//..    stmt( IRStmt_Put( segmentGuestRegOffset(sreg), e ) );
//.. }

static IRExpr* getXMMReg ( UInt xmmreg )
{
   return IRExpr_Get( xmmGuestRegOffset(xmmreg), Ity_V128 );
}

static IRExpr* getXMMRegLane64 ( UInt xmmreg, Int laneno )
{
   return IRExpr_Get( xmmGuestRegLane64offset(xmmreg,laneno), Ity_I64 );
}

static IRExpr* getXMMRegLane64F ( UInt xmmreg, Int laneno )
{
   return IRExpr_Get( xmmGuestRegLane64offset(xmmreg,laneno), Ity_F64 );
}

static IRExpr* getXMMRegLane32 ( UInt xmmreg, Int laneno )
{
   return IRExpr_Get( xmmGuestRegLane32offset(xmmreg,laneno), Ity_I32 );
}

static IRExpr* getXMMRegLane32F ( UInt xmmreg, Int laneno )
{
   return IRExpr_Get( xmmGuestRegLane32offset(xmmreg,laneno), Ity_F32 );
}

static void putXMMReg ( UInt xmmreg, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_V128);
   stmt( IRStmt_Put( xmmGuestRegOffset(xmmreg), e ) );
}

static void putXMMRegLane64 ( UInt xmmreg, Int laneno, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I64);
   stmt( IRStmt_Put( xmmGuestRegLane64offset(xmmreg,laneno), e ) );
}

static void putXMMRegLane64F ( UInt xmmreg, Int laneno, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_F64);
   stmt( IRStmt_Put( xmmGuestRegLane64offset(xmmreg,laneno), e ) );
}

static void putXMMRegLane32F ( UInt xmmreg, Int laneno, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_F32);
   stmt( IRStmt_Put( xmmGuestRegLane32offset(xmmreg,laneno), e ) );
}

static void putXMMRegLane32 ( UInt xmmreg, Int laneno, IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I32);
   stmt( IRStmt_Put( xmmGuestRegLane32offset(xmmreg,laneno), e ) );
}

//.. static void putXMMRegLane16 ( UInt xmmreg, Int laneno, IRExpr* e )
//.. {
//..    vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I16);
//..    stmt( IRStmt_Put( xmmGuestRegLane16offset(xmmreg,laneno), e ) );
//.. }

static IRExpr* mkV128 ( UShort mask )
{
   return IRExpr_Const(IRConst_V128(mask));
}


/*------------------------------------------------------------*/
/*--- Helpers for %eflags.                                 ---*/
/*------------------------------------------------------------*/

/* -------------- Evaluating the flags-thunk. -------------- */

/* Build IR to calculate all the eflags from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression ::
   Ity_I64. */
static IRExpr* mk_amd64g_calculate_rflags_all ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I64),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I64),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I64),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I64) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I64,
           0/*regparm*/, 
           "amd64g_calculate_rflags_all", &amd64g_calculate_rflags_all,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}

/* Build IR to calculate some particular condition from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression ::
   Ity_Bit. */
static IRExpr* mk_amd64g_calculate_condition ( AMD64Condcode cond )
{
   IRExpr** args
      = mkIRExprVec_5( mkU64(cond),
                       IRExpr_Get(OFFB_CC_OP,   Ity_I64),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I64),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I64),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I64) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I64,
           0/*regparm*/, 
           "amd64g_calculate_condition", &amd64g_calculate_condition,
           args
        );
   /* Exclude the requested condition, OP and NDEP from definedness
      checking.  We're only interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<1) | (1<<4);
   return unop(Iop_32to1, unop(Iop_64to32, call));
}

/* Build IR to calculate just the carry flag from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression :: Ity_I64. */
static IRExpr* mk_amd64g_calculate_rflags_c ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I64),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I64),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I64),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I64) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I64,
           0/*regparm*/, 
           "amd64g_calculate_rflags_c", &amd64g_calculate_rflags_c,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}


/* -------------- Building the flags-thunk. -------------- */

/* The machinery in this section builds the flag-thunk following a
   flag-setting operation.  Hence the various setFlags_* functions.
*/

static Bool isAddSub ( IROp op8 )
{
   return toBool(op8 == Iop_Add8 || op8 == Iop_Sub8);
}

static Bool isLogic ( IROp op8 )
{
   return toBool(op8 == Iop_And8 || op8 == Iop_Or8 || op8 == Iop_Xor8);
}

/* U-widen 8/16/32/64 bit int expr to 64. */
static IRExpr* widenUto64 ( IRExpr* e )
{
   switch (typeOfIRExpr(irbb->tyenv,e)) {
      case Ity_I64: return e;
      case Ity_I32: return unop(Iop_32Uto64, e);
      case Ity_I16: return unop(Iop_32Uto64, unop(Iop_16Uto32,e));
      case Ity_I8:  return unop(Iop_32Uto64, unop(Iop_8Uto32,e));
      default: vpanic("widenUto64");
   }
}

/* S-widen 8/16/32/64 bit int expr to 32. */
static IRExpr* widenSto64 ( IRExpr* e )
{
   switch (typeOfIRExpr(irbb->tyenv,e)) {
      case Ity_I64: return e;
      case Ity_I32: return unop(Iop_32Sto64, e);
      case Ity_I16: return unop(Iop_32Sto64, unop(Iop_16Sto32,e));
      case Ity_I8:  return unop(Iop_32Sto64, unop(Iop_8Sto32,e));
      default: vpanic("widenSto64");
   }
}

/* Narrow 8/16/32/64 bit int expr to 8/16/32/64.  Clearly only some
   of these combinations make sense. */
static IRExpr* narrowTo ( IRType dst_ty, IRExpr* e )
{
   IRType src_ty = typeOfIRExpr(irbb->tyenv,e);
   if (src_ty == dst_ty)
      return e;
   if (src_ty == Ity_I32 && dst_ty == Ity_I16)
      return unop(Iop_32to16, e);
   if (src_ty == Ity_I32 && dst_ty == Ity_I8)
      return unop(Iop_32to8, e);
   if (src_ty == Ity_I64 && dst_ty == Ity_I32)
      return unop(Iop_64to32, e);
   if (src_ty == Ity_I64 && dst_ty == Ity_I16)
      return unop(Iop_32to16, unop(Iop_64to32, e));
   if (src_ty == Ity_I64 && dst_ty == Ity_I8)
      return unop(Iop_32to8, unop(Iop_64to32, e));

   vex_printf("\nsrc, dst tys are: ");
   ppIRType(src_ty);
   vex_printf(", ");
   ppIRType(dst_ty);
   vex_printf("\n");
   vpanic("narrowTo(amd64)");
}


/* Set the flags thunk OP, DEP1 and DEP2 fields.  The supplied op is
   auto-sized up to the real op. */

static 
void setFlags_DEP1_DEP2 ( IROp op8, IRTemp dep1, IRTemp dep2, IRType ty )
{
   Int ccOp = 0;
   switch (ty) {
      case Ity_I8:  ccOp = 0; break;
      case Ity_I16: ccOp = 1; break;
      case Ity_I32: ccOp = 2; break;
      case Ity_I64: ccOp = 3; break;
      default: vassert(0);
   }
   switch (op8) {
      case Iop_Add8: ccOp += AMD64G_CC_OP_ADDB;   break;
      case Iop_Sub8: ccOp += AMD64G_CC_OP_SUBB;   break;
      default:       ppIROp(op8);
                     vpanic("setFlags_DEP1_DEP2(amd64)");
   }
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(ccOp)) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto64(mkexpr(dep1))) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, widenUto64(mkexpr(dep2))) );
}


/* Set the OP and DEP1 fields only, and write zero to DEP2. */

static 
void setFlags_DEP1 ( IROp op8, IRTemp dep1, IRType ty )
{
   Int ccOp = 0;
   switch (ty) {
      case Ity_I8:  ccOp = 0; break;
      case Ity_I16: ccOp = 1; break;
      case Ity_I32: ccOp = 2; break;
      case Ity_I64: ccOp = 3; break;
      default: vassert(0);
   }
   switch (op8) {
      case Iop_Or8:
      case Iop_And8:
      case Iop_Xor8: ccOp += AMD64G_CC_OP_LOGICB; break;
      default:       ppIROp(op8);
                     vpanic("setFlags_DEP1(amd64)");
   }
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(ccOp)) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto64(mkexpr(dep1))) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0)) );
}


/* For shift operations, we put in the result and the undershifted
   result.  Except if the shift amount is zero, the thunk is left
   unchanged. */

static void setFlags_DEP1_DEP2_shift ( IROp    op64,
                                       IRTemp  res,
                                       IRTemp  resUS,
                                       IRType  ty,
                                       IRTemp  guard )
{
   Int ccOp = 0;
   switch (ty) {
      case Ity_I8:  ccOp = 0; break;
      case Ity_I16: ccOp = 1; break;
      case Ity_I32: ccOp = 2; break;
      case Ity_I64: ccOp = 3; break;
      default: vassert(0);
   }

   vassert(guard);

   /* Both kinds of right shifts are handled by the same thunk
      operation. */
   switch (op64) {
      case Iop_Shr64:
      case Iop_Sar64: ccOp += AMD64G_CC_OP_SHRB; break;
      case Iop_Shl64: ccOp += AMD64G_CC_OP_SHLB; break;
      default:        ppIROp(op64);
                      vpanic("setFlags_DEP1_DEP2_shift(amd64)");
   }

   /* DEP1 contains the result, DEP2 contains the undershifted value. */
   stmt( IRStmt_Put( OFFB_CC_OP,
                     IRExpr_Mux0X( mkexpr(guard),
                                   IRExpr_Get(OFFB_CC_OP,Ity_I64),
                                   mkU64(ccOp))) );
   stmt( IRStmt_Put( OFFB_CC_DEP1,
                     IRExpr_Mux0X( mkexpr(guard),
                                   IRExpr_Get(OFFB_CC_DEP1,Ity_I64),
                                   widenUto64(mkexpr(res)))) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, 
                     IRExpr_Mux0X( mkexpr(guard),
                                   IRExpr_Get(OFFB_CC_DEP2,Ity_I64),
                                   widenUto64(mkexpr(resUS)))) );
}


/* For the inc/dec case, we store in DEP1 the result value and in NDEP
   the former value of the carry flag, which unfortunately we have to
   compute. */

static void setFlags_INC_DEC ( Bool inc, IRTemp res, IRType ty )
{
   Int ccOp = inc ? AMD64G_CC_OP_INCB : AMD64G_CC_OP_DECB;

   switch (ty) {
      case Ity_I8:  ccOp += 0; break;
      case Ity_I16: ccOp += 1; break;
      case Ity_I32: ccOp += 2; break;
      case Ity_I64: ccOp += 3; break;
      default: vassert(0);
   }
   
   /* This has to come first, because calculating the C flag 
      may require reading all four thunk fields. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mk_amd64g_calculate_rflags_c()) );
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(ccOp)) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, mkexpr(res)) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0)) );
}


/* Multiplies are pretty much like add and sub: DEP1 and DEP2 hold the
   two arguments. */

static
void setFlags_MUL ( IRType ty, IRTemp arg1, IRTemp arg2, ULong base_op )
{
   switch (ty) {
      case Ity_I8:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU64(base_op+0) ) );
         break;
      case Ity_I16:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU64(base_op+1) ) );
         break;
      case Ity_I32:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU64(base_op+2) ) );
         break;
      case Ity_I64:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU64(base_op+3) ) );
         break;
      default:
         vpanic("setFlags_MUL(amd64)");
   }
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto64(mkexpr(arg1)) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, widenUto64(mkexpr(arg2)) ));
}


/* -------------- Condition codes. -------------- */

/* Condition codes, using the AMD encoding.  */

static HChar* name_AMD64Condcode ( AMD64Condcode cond )
{
   switch (cond) {
      case AMD64CondO:      return "o";
      case AMD64CondNO:     return "no";
      case AMD64CondB:      return "b";
      case AMD64CondNB:     return "ae"; /*"nb";*/
      case AMD64CondZ:      return "e"; /*"z";*/
      case AMD64CondNZ:     return "ne"; /*"nz";*/
      case AMD64CondBE:     return "be";
      case AMD64CondNBE:    return "a"; /*"nbe";*/
      case AMD64CondS:      return "s";
      case AMD64CondNS:     return "ns";
      case AMD64CondP:      return "p";
      case AMD64CondNP:     return "np";
      case AMD64CondL:      return "l";
      case AMD64CondNL:     return "ge"; /*"nl";*/
      case AMD64CondLE:     return "le";
      case AMD64CondNLE:    return "g"; /*"nle";*/
      case AMD64CondAlways: return "ALWAYS";
      default: vpanic("name_AMD64Condcode");
   }
}

static 
AMD64Condcode positiveIse_AMD64Condcode ( AMD64Condcode  cond,
                                          /*OUT*/Bool*   needInvert )
{
   vassert(cond >= AMD64CondO && cond <= AMD64CondNLE);
   if (cond & 1) {
      *needInvert = True;
      return cond-1;
   } else {
      *needInvert = False;
      return cond;
   }
}


/* -------------- Helpers for ADD/SUB with carry. -------------- */

/* Given ta1, ta2 and tres, compute tres = ADC(ta1,ta2) and set flags
   appropriately.
*/
static void helper_ADC ( Int sz,
                         IRTemp tres, IRTemp ta1, IRTemp ta2 )
{
   UInt    thunkOp;
   IRType  ty    = szToITy(sz);
   IRTemp  oldc  = newTemp(Ity_I64);
   IRTemp  oldcn = newTemp(ty);
   IROp    plus  = mkSizedOp(ty, Iop_Add8);
   IROp    xor   = mkSizedOp(ty, Iop_Xor8);

   switch (sz) {
      case 8:  thunkOp = AMD64G_CC_OP_ADCQ; break;
      case 4:  thunkOp = AMD64G_CC_OP_ADCL; break;
      case 2:  thunkOp = AMD64G_CC_OP_ADCW; break;
      case 1:  thunkOp = AMD64G_CC_OP_ADCB; break;
      default: vassert(0);
   }

   /* oldc = old carry flag, 0 or 1 */
   assign( oldc,  binop(Iop_And64,
                        mk_amd64g_calculate_rflags_c(),
                        mkU64(1)) );

   assign( oldcn, narrowTo(ty, mkexpr(oldc)) );

   assign( tres, binop(plus,
                       binop(plus,mkexpr(ta1),mkexpr(ta2)),
                       mkexpr(oldcn)) );

   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(thunkOp) ) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, mkexpr(ta1) ) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, binop(xor, mkexpr(ta2), 
                                              mkexpr(oldcn)) ) );
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkexpr(oldc) ) );
}


/* Given ta1, ta2 and tres, compute tres = SBB(ta1,ta2) and set flags
   appropriately.
*/
static void helper_SBB ( Int sz,
                         IRTemp tres, IRTemp ta1, IRTemp ta2 )
{
   UInt    thunkOp;
   IRType  ty    = szToITy(sz);
   IRTemp  oldc  = newTemp(Ity_I64);
   IRTemp  oldcn = newTemp(ty);
   IROp    minus = mkSizedOp(ty, Iop_Sub8);
   IROp    xor   = mkSizedOp(ty, Iop_Xor8);

   switch (sz) {
      case 8:  thunkOp = AMD64G_CC_OP_SBBQ; break;
      case 4:  thunkOp = AMD64G_CC_OP_SBBL; break;
      case 2:  thunkOp = AMD64G_CC_OP_SBBW; break;
      case 1:  thunkOp = AMD64G_CC_OP_SBBB; break;
      default: vassert(0);
   }

   /* oldc = old carry flag, 0 or 1 */
   assign( oldc, binop(Iop_And64,
                       mk_amd64g_calculate_rflags_c(),
                       mkU64(1)) );

   assign( oldcn, narrowTo(ty, mkexpr(oldc)) );

   assign( tres, binop(minus,
                       binop(minus,mkexpr(ta1),mkexpr(ta2)),
                       mkexpr(oldcn)) );

   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(thunkOp) ) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, mkexpr(ta1) ) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, binop(xor, mkexpr(ta2), 
                                              mkexpr(oldcn)) ) );
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkexpr(oldc) ) );
}


/* -------------- Helpers for disassembly printing. -------------- */

static HChar* nameGrp1 ( Int opc_aux )
{
   static HChar* grp1_names[8] 
     = { "add", "or", "adc", "sbb", "and", "sub", "xor", "cmp" };
   if (opc_aux < 0 || opc_aux > 7) vpanic("nameGrp1(amd64)");
   return grp1_names[opc_aux];
}

static HChar* nameGrp2 ( Int opc_aux )
{
   static HChar* grp2_names[8] 
     = { "rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar" };
   if (opc_aux < 0 || opc_aux > 7) vpanic("nameGrp2(amd64)");
   return grp2_names[opc_aux];
}

static HChar* nameGrp4 ( Int opc_aux )
{
   static HChar* grp4_names[8] 
     = { "inc", "dec", "???", "???", "???", "???", "???", "???" };
   if (opc_aux < 0 || opc_aux > 1) vpanic("nameGrp4(amd64)");
   return grp4_names[opc_aux];
}

static HChar* nameGrp5 ( Int opc_aux )
{
   static HChar* grp5_names[8] 
     = { "inc", "dec", "call*", "call*", "jmp*", "jmp*", "push", "???" };
   if (opc_aux < 0 || opc_aux > 6) vpanic("nameGrp5(amd64)");
   return grp5_names[opc_aux];
}

static HChar* nameGrp8 ( Int opc_aux )
{
   static HChar* grp8_names[8] 
      = { "???", "???", "???", "???", "bt", "bts", "btr", "btc" };
   if (opc_aux < 4 || opc_aux > 7) vpanic("nameGrp8(amd64)");
   return grp8_names[opc_aux];
}

//.. static HChar* nameSReg ( UInt sreg )
//.. {
//..    switch (sreg) {
//..       case R_ES: return "%es";
//..       case R_CS: return "%cs";
//..       case R_SS: return "%ss";
//..       case R_DS: return "%ds";
//..       case R_FS: return "%fs";
//..       case R_GS: return "%gs";
//..       default: vpanic("nameSReg(x86)");
//..    }
//.. }
//.. 
//.. static HChar* nameMMXReg ( Int mmxreg )
//.. {
//..    static HChar* mmx_names[8] 
//..      = { "%mm0", "%mm1", "%mm2", "%mm3", "%mm4", "%mm5", "%mm6", "%mm7" };
//..    if (mmxreg < 0 || mmxreg > 7) vpanic("nameMMXReg(x86,guest)");
//..    return mmx_names[mmxreg];
//.. }

static HChar* nameXMMReg ( Int xmmreg )
{
   static HChar* xmm_names[16] 
     = { "%xmm0",  "%xmm1",  "%xmm2",  "%xmm3", 
         "%xmm4",  "%xmm5",  "%xmm6",  "%xmm7", 
         "%xmm8",  "%xmm9",  "%xmm10", "%xmm11", 
         "%xmm12", "%xmm13", "%xmm14", "%xmm15" };
   if (xmmreg < 0 || xmmreg > 15) vpanic("nameXMMReg(amd64)");
   return xmm_names[xmmreg];
}
 
//.. static Char* nameMMXGran ( UChar gran )
//.. {
//..    switch (gran) {
//..       case 0: return "b";
//..       case 1: return "w";
//..       case 2: return "d";
//..       case 3: return "q";
//..       default: vpanic("nameMMXGran(x86,guest)");
//..    }
//.. }

static HChar nameISize ( Int size )
{
   switch (size) {
      case 8: return 'q';
      case 4: return 'l';
      case 2: return 'w';
      case 1: return 'b';
      default: vpanic("nameISize(amd64)");
   }
}


/*------------------------------------------------------------*/
/*--- JMP helpers                                          ---*/
/*------------------------------------------------------------*/

static void jmp_lit( IRJumpKind kind, Addr64 d64 )
{
  irbb->next     = mkU64(d64);
  irbb->jumpkind = kind;
}

static void jmp_treg( IRJumpKind kind, IRTemp t )
{
   irbb->next     = mkexpr(t);
   irbb->jumpkind = kind;
}

static 
void jcc_01 ( AMD64Condcode cond, Addr64 d64_false, Addr64 d64_true )
{
   Bool          invert;
   AMD64Condcode condPos;
   condPos = positiveIse_AMD64Condcode ( cond, &invert );
   if (invert) {
      stmt( IRStmt_Exit( mk_amd64g_calculate_condition(condPos),
                         Ijk_Boring,
                         IRConst_U64(d64_false) ) );
      irbb->next     = mkU64(d64_true);
      irbb->jumpkind = Ijk_Boring;
   } else {
      stmt( IRStmt_Exit( mk_amd64g_calculate_condition(condPos),
                         Ijk_Boring,
                         IRConst_U64(d64_true) ) );
      irbb->next     = mkU64(d64_false);
      irbb->jumpkind = Ijk_Boring;
   }
}


/*------------------------------------------------------------*/
/*--- Disassembling addressing modes                       ---*/
/*------------------------------------------------------------*/

static 
HChar* sorbTxt ( Prefix pfx )
{
   if (pfx & PFX_CS) return "%cs:";
   if (pfx & PFX_DS) return "%ds:";
   if (pfx & PFX_ES) return "%es:";
   if (pfx & PFX_FS) return "%fs:";
   if (pfx & PFX_GS) return "%gs:";
   if (pfx & PFX_SS) return "%ss:";
   return ""; /* no override */
}


/* 'virtual' is an IRExpr* holding a virtual address.  Convert it to a
   linear address by adding any required segment override as indicated
   by sorb. */
static
IRExpr* handleSegOverride ( Prefix pfx, IRExpr* virtual )
{
   if (pfx & PFX_FS) {
      /* Note that this is a linux-kernel specific hack that relies
         on the assumption that %fs is always zero. */
      /* return virtual + guest_FS_ZERO. */
      return binop(Iop_Add64, virtual, IRExpr_Get(OFFB_FS_ZERO, Ity_I64));
   }

   if (pfx & PFX_GS) {
      unimplemented("amd64 %gs segment override");
   }

   /* cs, ds, es and ss are simply ignored in 64-bit mode. */
   return virtual;
}

//.. {
//..    Int    sreg;
//..    IRType hWordTy;
//..    IRTemp ldt_ptr, gdt_ptr, seg_selector, r64;
//.. 
//..    if (sorb == 0)
//..       /* the common case - no override */
//..       return virtual;
//.. 
//..    switch (sorb) {
//..       case 0x3E: sreg = R_DS; break;
//..       case 0x26: sreg = R_ES; break;
//..       case 0x64: sreg = R_FS; break;
//..       case 0x65: sreg = R_GS; break;
//..       default: vpanic("handleSegOverride(x86,guest)");
//..    }
//.. 
//..    hWordTy = sizeof(HWord)==4 ? Ity_I32 : Ity_I64;
//.. 
//..    seg_selector = newTemp(Ity_I32);
//..    ldt_ptr      = newTemp(hWordTy);
//..    gdt_ptr      = newTemp(hWordTy);
//..    r64          = newTemp(Ity_I64);
//.. 
//..    assign( seg_selector, unop(Iop_16Uto32, getSReg(sreg)) );
//..    assign( ldt_ptr, IRExpr_Get( OFFB_LDT, hWordTy ));
//..    assign( gdt_ptr, IRExpr_Get( OFFB_GDT, hWordTy ));
//.. 
//..    /*
//..    Call this to do the translation and limit checks: 
//..    ULong x86g_use_seg_selector ( HWord ldt, HWord gdt,
//..                                  UInt seg_selector, UInt virtual_addr )
//..    */
//..    assign( 
//..       r64, 
//..       mkIRExprCCall( 
//..          Ity_I64, 
//..          0/*regparms*/, 
//..          "x86g_use_seg_selector", 
//..          &x86g_use_seg_selector, 
//..          mkIRExprVec_4( mkexpr(ldt_ptr), mkexpr(gdt_ptr), 
//..                         mkexpr(seg_selector), virtual)
//..       )
//..    );
//.. 
//..    /* If the high 32 of the result are non-zero, there was a 
//..       failure in address translation.  In which case, make a
//..       quick exit.
//..    */
//..    stmt( 
//..       IRStmt_Exit(
//..          binop(Iop_CmpNE32, unop(Iop_64HIto32, mkexpr(r64)), mkU32(0)),
//..          Ijk_MapFail,
//..          IRConst_U32( guest_eip_curr_instr )
//..       )
//..    );
//.. 
//..    /* otherwise, here's the translated result. */
//..    return unop(Iop_64to32, mkexpr(r64));
//.. }


/* Generate IR to calculate an address indicated by a ModRM and
   following SIB bytes.  The expression, and the number of bytes in
   the address mode, are returned (the latter in *len).  Note that
   this fn should not be called if the R/M part of the address denotes
   a register instead of memory.  If print_codegen is true, text of
   the addressing mode is placed in buf.

   The computed address is stored in a new tempreg, and the
   identity of the tempreg is returned.

   extra_bytes holds the number of bytes after the amode, as supplied
   by the caller.  This is needed to make sense of %rip-relative
   addresses.  Note that the value that *len is set to is only the
   length of the amode itself and does not include the value supplied
   in xtra_bytes.
 */

static IRTemp disAMode_copy2tmp ( IRExpr* addr64 )
{
   IRTemp tmp = newTemp(Ity_I64);
   assign( tmp, addr64 );
   return tmp;
}

static 
IRTemp disAMode ( Int* len, Prefix pfx, ULong delta, 
                  HChar* buf, Int extra_bytes )
{
   UChar mod_reg_rm = getUChar(delta);
   delta++;

   buf[0] = (UChar)0;
   vassert(extra_bytes >= 0 && extra_bytes < 10);

   /* squeeze out the reg field from mod_reg_rm, since a 256-entry
      jump table seems a bit excessive. 
   */
   mod_reg_rm &= 0xC7;                         /* is now XX000YYY */
   mod_reg_rm  = toUChar(mod_reg_rm | (mod_reg_rm >> 3));
                                               /* is now XX0XXYYY */
   mod_reg_rm &= 0x1F;                         /* is now 000XXYYY */
   switch (mod_reg_rm) {

      /* REX.B==0: (%rax) .. (%rdi), not including (%rsp) or (%rbp).
         REX.B==1: (%r8)  .. (%r15), not including (%r12) or (%r13).
      */
      case 0x00: case 0x01: case 0x02: case 0x03: 
      /* ! 04 */ /* ! 05 */ case 0x06: case 0x07:
         { UChar rm = toUChar(mod_reg_rm & 7);
           DIS(buf, "%s(%s)", sorbTxt(pfx), nameIRegRexB(8,pfx,rm));
           *len = 1;
           return disAMode_copy2tmp(
                  handleSegOverride(pfx, getIRegRexB(8,pfx,rm)));
         }

      /* REX.B==0: d8(%rax) ... d8(%rdi), not including d8(%rsp) 
         REX.B==1: d8(%r8)  ... d8(%r15), not including d8(%r12) 
      */
      case 0x08: case 0x09: case 0x0A: case 0x0B: 
      /* ! 0C */ case 0x0D: case 0x0E: case 0x0F:
         { UChar rm = toUChar(mod_reg_rm & 7);
           Long d   = getSDisp8(delta);
           if (d == 0) {
              DIS(buf, "%s(%s)", sorbTxt(pfx), nameIRegRexB(8,pfx,rm));
           } else {
              DIS(buf, "%s%lld(%s)", sorbTxt(pfx), d, nameIRegRexB(8,pfx,rm));
           }
           *len = 2;
           return disAMode_copy2tmp(
                  handleSegOverride(pfx,
                     binop(Iop_Add64,getIRegRexB(8,pfx,rm),mkU64(d))));
         }

      /* REX.B==0: d32(%rax) ... d32(%rdi), not including d32(%rsp)
         REX.B==1: d32(%r8)  ... d32(%r15), not including d32(%r12)
      */
      case 0x10: case 0x11: case 0x12: case 0x13: 
      /* ! 14 */ case 0x15: case 0x16: case 0x17:
         { UChar rm = toUChar(mod_reg_rm & 7);
           Long  d  = getSDisp32(delta);
           DIS(buf, "%s%lld(%s)", sorbTxt(pfx), d, nameIRegRexB(8,pfx,rm));
           *len = 5;
           return disAMode_copy2tmp(
                  handleSegOverride(pfx,
                     binop(Iop_Add64,getIRegRexB(8,pfx,rm),mkU64(d))));
         }

      /* REX.B==0: a register, %rax .. %rdi.  This shouldn't happen. */
      /* REX.B==1: a register, %r8  .. %r16.  This shouldn't happen. */
      case 0x18: case 0x19: case 0x1A: case 0x1B:
      case 0x1C: case 0x1D: case 0x1E: case 0x1F:
         vpanic("disAMode(amd64): not an addr!");

      /* RIP + disp32.  This assumes that guest_rip_curr_instr is set
         correctly at the start of handling each instruction. */
      case 0x05: 
         { Long d = getSDisp32(delta);
           *len = 5;
           DIS(buf, "%s%lld(%%rip)", sorbTxt(pfx), d);
           /* We need to know the next instruction's start address.
              Try and figure out what it is, record the guess, and ask
              the top-level driver logic (bbToIR_AMD64) to check we
              guessed right, after the instruction is completely
              decoded. */
           guest_rip_next_mustcheck = True;
           guest_rip_next_assumed = guest_rip_bbstart 
                                    + delta+4 + extra_bytes;
           return disAMode_copy2tmp( 
                     handleSegOverride(pfx, 
                        binop(Iop_Add64, mkU64(guest_rip_next_assumed), 
                                         mkU64(d))));
         }

      case 0x04: {
         /* SIB, with no displacement.  Special cases:
            -- %rsp cannot act as an index value.  
               If index_r indicates %rsp, zero is used for the index.
            -- when mod is zero and base indicates RBP or R13, base is 
               instead a 32-bit sign-extended literal.
            It's all madness, I tell you.  Extract %index, %base and 
            scale from the SIB byte.  The value denoted is then:
               | %index == %RSP && (%base == %RBP || %base == %R13)
               = d32 following SIB byte
               | %index == %RSP && !(%base == %RBP || %base == %R13)
               = %base
               | %index != %RSP && (%base == %RBP || %base == %R13)
               = d32 following SIB byte + (%index << scale)
               | %index != %RSP && !(%base == %RBP || %base == %R13)
               = %base + (%index << scale)
         */
         UChar sib     = getUChar(delta);
         UChar scale   = toUChar((sib >> 6) & 3);
         UChar index_r = toUChar((sib >> 3) & 7);
         UChar base_r  = toUChar(sib & 7);
         /* correct since #(R13) == 8 + #(RBP) */
         Bool  base_is_BPor13 = toBool(base_r == R_RBP);
         Bool  index_is_SP    = toBool(index_r == R_RSP && 0==getRexX(pfx));
         delta++;

         if ((!index_is_SP) && (!base_is_BPor13)) {
            if (scale == 0) {
               DIS(buf, "%s(%s,%s)", sorbTxt(pfx), 
                         nameIRegRexB(8,pfx,base_r), 
                         nameIReg64rexX(pfx,index_r));
            } else {
               DIS(buf, "%s(%s,%s,%d)", sorbTxt(pfx), 
                         nameIRegRexB(8,pfx,base_r), 
                         nameIReg64rexX(pfx,index_r), 1<<scale);
            }
            *len = 2;
            return
               disAMode_copy2tmp( 
               handleSegOverride(pfx,
                  binop(Iop_Add64, 
                        getIRegRexB(8,pfx,base_r),
                        binop(Iop_Shl64, getIReg64rexX(pfx,index_r),
                              mkU8(scale)))));
         }

         if ((!index_is_SP) && base_is_BPor13) {
            Long d = getSDisp32(delta);
            DIS(buf, "%s%lld(,%s,%d)", sorbTxt(pfx), d, 
                      nameIReg64rexX(pfx,index_r), 1<<scale);
            *len = 6;
            return
               disAMode_copy2tmp(
               handleSegOverride(pfx, 
                  binop(Iop_Add64,
                        binop(Iop_Shl64, getIReg64rexX(pfx,index_r), 
                                         mkU8(scale)),
                        mkU64(d))));
         }

         if (index_is_SP && (!base_is_BPor13)) {
            DIS(buf, "%s(%s)", sorbTxt(pfx), nameIRegRexB(8,pfx,base_r));
            *len = 2;
            return disAMode_copy2tmp(
                   handleSegOverride(pfx, getIRegRexB(8,pfx,base_r)));
         }

         if (index_is_SP && base_is_BPor13) {
            Long d = getSDisp32(delta);
            DIS(buf, "%s%lld", sorbTxt(pfx), d);
            *len = 6;
            return disAMode_copy2tmp(
                   handleSegOverride(pfx, mkU64(d)));
         }

         vassert(0);
      }

      /* SIB, with 8-bit displacement.  Special cases:
         -- %esp cannot act as an index value.  
            If index_r indicates %esp, zero is used for the index.
         Denoted value is:
            | %index == %ESP
            = d8 + %base
            | %index != %ESP
            = d8 + %base + (%index << scale)
      */
      case 0x0C: {
         UChar sib     = getUChar(delta);
         UChar scale   = toUChar((sib >> 6) & 3);
         UChar index_r = toUChar((sib >> 3) & 7);
         UChar base_r  = toUChar(sib & 7);
         Long d        = getSDisp8(delta+1);

         if (index_r == R_RSP && 0==getRexX(pfx)) {
            DIS(buf, "%s%lld(%s)", sorbTxt(pfx), 
                                   d, nameIRegRexB(8,pfx,base_r));
            *len = 3;
            return disAMode_copy2tmp(
                   handleSegOverride(pfx, 
                      binop(Iop_Add64, getIRegRexB(8,pfx,base_r), mkU64(d)) ));
         } else {
            if (scale == 0) {
               DIS(buf, "%s%lld(%s,%s)", sorbTxt(pfx), d, 
                         nameIRegRexB(8,pfx,base_r), 
                         nameIReg64rexX(pfx,index_r));
            } else {
               DIS(buf, "%s%lld(%s,%s,%d)", sorbTxt(pfx), d, 
                         nameIRegRexB(8,pfx,base_r), 
                         nameIReg64rexX(pfx,index_r), 1<<scale);
            }
            *len = 3;
            return 
                disAMode_copy2tmp(
                handleSegOverride(pfx,
                  binop(Iop_Add64,
                        binop(Iop_Add64, 
                              getIRegRexB(8,pfx,base_r), 
                              binop(Iop_Shl64, 
                                    getIReg64rexX(pfx,index_r), mkU8(scale))),
                        mkU64(d))));
         }
         vassert(0); /*NOTREACHED*/
      }

      /* SIB, with 32-bit displacement.  Special cases:
         -- %rsp cannot act as an index value.  
            If index_r indicates %rsp, zero is used for the index.
         Denoted value is:
            | %index == %RSP
            = d32 + %base
            | %index != %RSP
            = d32 + %base + (%index << scale)
      */
      case 0x14: {
         UChar sib     = getUChar(delta);
         UChar scale   = toUChar((sib >> 6) & 3);
         UChar index_r = toUChar((sib >> 3) & 7);
         UChar base_r  = toUChar(sib & 7);
         Long d        = getSDisp32(delta+1);

         if (index_r == R_RSP && 0==getRexX(pfx)) {
            DIS(buf, "%s%lld(%s)", sorbTxt(pfx), 
                                   d, nameIRegRexB(8,pfx,base_r));
            *len = 6;
            return disAMode_copy2tmp(
                   handleSegOverride(pfx, 
                      binop(Iop_Add64, getIRegRexB(8,pfx,base_r), mkU64(d)) ));
         } else {
            if (scale == 0) {
               DIS(buf, "%s%lld(%s,%s)", sorbTxt(pfx), d, 
                         nameIRegRexB(8,pfx,base_r), 
                         nameIReg64rexX(pfx,index_r));
            } else {
               DIS(buf, "%s%lld(%s,%s,%d)", sorbTxt(pfx), d, 
                         nameIRegRexB(8,pfx,base_r), 
                         nameIReg64rexX(pfx,index_r), 1<<scale);
            }
            *len = 6;
            return 
                disAMode_copy2tmp(
                handleSegOverride(pfx,
                  binop(Iop_Add64,
                        binop(Iop_Add64, 
                              getIRegRexB(8,pfx,base_r), 
                              binop(Iop_Shl64, 
                                    getIReg64rexX(pfx,index_r), mkU8(scale))),
                        mkU64(d))));
         }
         vassert(0); /*NOTREACHED*/
      }

      default:
         vpanic("disAMode(amd64)");
         return 0; /*notreached*/
   }
}


/* Figure out the number of (insn-stream) bytes constituting the amode
   beginning at delta.  Is useful for getting hold of literals beyond
   the end of the amode before it has been disassembled.  */

static UInt lengthAMode ( Prefix pfx, ULong delta )
{
   UChar mod_reg_rm = getUChar(delta);
   delta++;

   /* squeeze out the reg field from mod_reg_rm, since a 256-entry
      jump table seems a bit excessive. 
   */
   mod_reg_rm &= 0xC7;                         /* is now XX000YYY */
   mod_reg_rm  = toUChar(mod_reg_rm | (mod_reg_rm >> 3));
                                               /* is now XX0XXYYY */
   mod_reg_rm &= 0x1F;                         /* is now 000XXYYY */
   switch (mod_reg_rm) {

      /* REX.B==0: (%rax) .. (%rdi), not including (%rsp) or (%rbp).
         REX.B==1: (%r8)  .. (%r15), not including (%r12) or (%r13).
      */
      case 0x00: case 0x01: case 0x02: case 0x03: 
      /* ! 04 */ /* ! 05 */ case 0x06: case 0x07:
         return 1;

      /* REX.B==0: d8(%rax) ... d8(%rdi), not including d8(%rsp) 
         REX.B==1: d8(%r8)  ... d8(%r15), not including d8(%r12) 
      */
      case 0x08: case 0x09: case 0x0A: case 0x0B: 
      /* ! 0C */ case 0x0D: case 0x0E: case 0x0F:
         return 2;

      /* REX.B==0: d32(%rax) ... d32(%rdi), not including d32(%rsp)
         REX.B==1: d32(%r8)  ... d32(%r15), not including d32(%r12)
      */
      case 0x10: case 0x11: case 0x12: case 0x13: 
      /* ! 14 */ case 0x15: case 0x16: case 0x17:
         return 5;

      /* REX.B==0: a register, %rax .. %rdi.  This shouldn't happen. */
      /* REX.B==1: a register, %r8  .. %r16.  This shouldn't happen. */
      /* Not an address, but still handled. */
      case 0x18: case 0x19: case 0x1A: case 0x1B:
      case 0x1C: case 0x1D: case 0x1E: case 0x1F:
         return 1;

      /* RIP + disp32. */
      case 0x05: 
         return 5;

      case 0x04: {
         /* SIB, with no displacement. */
         UChar sib     = getUChar(delta);
         UChar base_r  = toUChar(sib & 7);
         /* correct since #(R13) == 8 + #(RBP) */
         Bool  base_is_BPor13 = toBool(base_r == R_RBP);

         if (base_is_BPor13) {
            return 6;
         } else {
            return 2;
         }
      }

      /* SIB, with 8-bit displacement. */
      case 0x0C:
         return 3;

      /* SIB, with 32-bit displacement. */
      case 0x14:
         return 6;

      default:
         vpanic("lengthAMode(amd64)");
         return 0; /*notreached*/
   }
}


/*------------------------------------------------------------*/
/*--- Disassembling common idioms                          ---*/
/*------------------------------------------------------------*/

/* Handle binary integer instructions of the form
      op E, G  meaning
      op reg-or-mem, reg
   Is passed the a ptr to the modRM byte, the actual operation, and the
   data size.  Returns the address advanced completely over this
   instruction.

   E(src) is reg-or-mem
   G(dst) is reg.

   If E is reg, -->    GET %G,  tmp
                       OP %E,   tmp
                       PUT tmp, %G
 
   If E is mem and OP is not reversible, 
                -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpa
                       GET %G, tmp2
                       OP tmpa, tmp2
                       PUT tmp2, %G

   If E is mem and OP is reversible
                -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpa
                       OP %G, tmpa
                       PUT tmpa, %G
*/
static
ULong dis_op2_E_G ( Prefix      pfx,
                    Bool        addSubCarry,
                    IROp        op8, 
                    Bool        keep,
                    Int         size, 
                    ULong       delta0,
                    HChar*      t_amd64opc )
{
   HChar   dis_buf[50];
   Int     len;
   IRType  ty   = szToITy(size);
   IRTemp  dst1 = newTemp(ty);
   IRTemp  src  = newTemp(ty);
   IRTemp  dst0 = newTemp(ty);
   UChar   rm   = getUChar(delta0);
   IRTemp  addr = IRTemp_INVALID;

   /* addSubCarry == True indicates the intended operation is
      add-with-carry or subtract-with-borrow. */
   if (addSubCarry) {
      vassert(op8 == Iop_Add8 || op8 == Iop_Sub8);
      vassert(keep);
   }

   if (epartIsReg(rm)) {
      /* Specially handle XOR reg,reg, because that doesn't really
         depend on reg, and doing the obvious thing potentially
         generates a spurious value check failure due to the bogus
         dependency. */
      if ((op8 == Iop_Xor8 || (op8 == Iop_Sub8 && addSubCarry))
          && offsetIRegG(size,pfx,rm) == offsetIRegE(size,pfx,rm)) {
         vassert(0); /* awaiting test case */
         if (op8 == Iop_Sub8)
            vex_printf("vex amd64->IR: sbb %%r,%%r optimisation(1)\n");
	 putIRegG(size,pfx,rm, mkU(ty,0));
      }

      assign( dst0, getIRegG(size,pfx,rm) );
      assign( src,  getIRegE(size,pfx,rm) );

      if (addSubCarry && op8 == Iop_Add8) {
         vassert(0); /* awaiting test case */
         helper_ADC( size, dst1, dst0, src );
         putIRegG(size, pfx, rm, mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         vassert(0); /* awaiting test case */
         helper_SBB( size, dst1, dst0, src );
         putIRegG(size, pfx, rm, mkexpr(dst1));
      } else {
         assign( dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            putIRegG(size, pfx, rm, mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_amd64opc, nameISize(size), 
                          nameIRegE(size,pfx,rm),
                          nameIRegG(size,pfx,rm));
      return 1+delta0;
   } else {
      /* E refers to memory */
      addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      assign( dst0, getIRegG(size,pfx,rm) );
      assign( src,  loadLE(szToITy(size), mkexpr(addr)) );

      if (addSubCarry && op8 == Iop_Add8) {
         vassert(0); /* awaiting test case */
         helper_ADC( size, dst1, dst0, src );
         putIRegG(size, pfx, rm, mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         vassert(0); /* awaiting test case */
         helper_SBB( size, dst1, dst0, src );
         putIRegG(size, pfx, rm, mkexpr(dst1));
      } else {
         assign( dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            putIRegG(size, pfx, rm, mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_amd64opc, nameISize(size), 
                          dis_buf, nameIRegG(size, pfx, rm));
      return len+delta0;
   }
}



/* Handle binary integer instructions of the form
      op G, E  meaning
      op reg, reg-or-mem
   Is passed the a ptr to the modRM byte, the actual operation, and the
   data size.  Returns the address advanced completely over this
   instruction.

   G(src) is reg.
   E(dst) is reg-or-mem

   If E is reg, -->    GET %E,  tmp
                       OP %G,   tmp
                       PUT tmp, %E
 
   If E is mem, -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpv
                       OP %G, tmpv
                       ST tmpv, (tmpa)
*/
static
ULong dis_op2_G_E ( Prefix      pfx,
                    Bool        addSubCarry,
                    IROp        op8, 
                    Bool        keep,
                    Int         size, 
                    ULong       delta0,
                    HChar*      t_amd64opc )
{
   HChar   dis_buf[50];
   Int     len;
   IRType  ty   = szToITy(size);
   IRTemp  dst1 = newTemp(ty);
   IRTemp  src  = newTemp(ty);
   IRTemp  dst0 = newTemp(ty);
   UChar   rm   = getUChar(delta0);
   IRTemp  addr = IRTemp_INVALID;

   /* addSubCarry == True indicates the intended operation is
      add-with-carry or subtract-with-borrow. */
   if (addSubCarry) {
      vassert(op8 == Iop_Add8 || op8 == Iop_Sub8);
      vassert(keep);
   }

   if (epartIsReg(rm)) {
      /* Specially handle XOR reg,reg, because that doesn't really
         depend on reg, and doing the obvious thing potentially
         generates a spurious value check failure due to the bogus
         dependency.  Ditto SBB reg,reg. */
      if ((op8 == Iop_Xor8 || (op8 == Iop_Sub8 && addSubCarry))
          && offsetIRegG(size,pfx,rm) == offsetIRegE(size,pfx,rm)) {
         putIRegE(size,pfx,rm, mkU(ty,0));
      }

      assign(dst0, getIRegE(size,pfx,rm));
      assign(src,  getIRegG(size,pfx,rm));

      if (addSubCarry && op8 == Iop_Add8) {
         helper_ADC( size, dst1, dst0, src );
         putIRegE(size, pfx, rm, mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         helper_SBB( size, dst1, dst0, src );
         putIRegE(size, pfx, rm, mkexpr(dst1));
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            putIRegE(size, pfx, rm, mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_amd64opc, nameISize(size), 
                          nameIRegG(size,pfx,rm),
                          nameIRegE(size,pfx,rm));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      assign(dst0, loadLE(ty,mkexpr(addr)));
      assign(src,  getIRegG(size,pfx,rm));

      if (addSubCarry && op8 == Iop_Add8) {
         vassert(0); /* awaiting test case */
         helper_ADC( size, dst1, dst0, src );
         storeLE(mkexpr(addr), mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         vassert(0); /* awaiting test case */
         helper_SBB( size, dst1, dst0, src );
         storeLE(mkexpr(addr), mkexpr(dst1));
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            storeLE(mkexpr(addr), mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_amd64opc, nameISize(size), 
                          nameIRegG(size,pfx,rm), dis_buf);
      return len+delta0;
   }
}


/* Handle move instructions of the form
      mov E, G  meaning
      mov reg-or-mem, reg
   Is passed the a ptr to the modRM byte, and the data size.  Returns
   the address advanced completely over this instruction.

   E(src) is reg-or-mem
   G(dst) is reg.

   If E is reg, -->    GET %E,  tmpv
                       PUT tmpv, %G
 
   If E is mem  -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpb
                       PUT tmpb, %G
*/
static
ULong dis_mov_E_G ( Prefix      pfx,
                    Int         size, 
                    ULong       delta0 )
{
   Int len;
   UChar rm = getUChar(delta0);
   HChar dis_buf[50];

   if (epartIsReg(rm)) {
      putIRegG(size, pfx, rm, getIRegE(size, pfx, rm));
      DIP("mov%c %s,%s\n", nameISize(size),
                           nameIRegE(size,pfx,rm),
                           nameIRegG(size,pfx,rm));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      IRTemp addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      putIRegG(size, pfx, rm, loadLE(szToITy(size), mkexpr(addr)));
      DIP("mov%c %s,%s\n", nameISize(size), 
                           dis_buf,
                           nameIRegG(size,pfx,rm));
      return delta0+len;
   }
}


/* Handle move instructions of the form
      mov G, E  meaning
      mov reg, reg-or-mem
   Is passed the a ptr to the modRM byte, and the data size.  Returns
   the address advanced completely over this instruction.

   G(src) is reg.
   E(dst) is reg-or-mem

   If E is reg, -->    GET %G,  tmp
                       PUT tmp, %E
 
   If E is mem, -->    (getAddr E) -> tmpa
                       GET %G, tmpv
                       ST tmpv, (tmpa) 
*/
static
ULong dis_mov_G_E ( Prefix      pfx,
                    Int         size, 
                    ULong       delta0 )
{
   Int len;
   UChar rm = getUChar(delta0);
   HChar dis_buf[50];

   if (epartIsReg(rm)) {
      putIRegE(size, pfx, rm, getIRegG(size, pfx, rm));
      DIP("mov%c %s,%s\n", nameISize(size),
                           nameIRegG(size,pfx,rm),
                           nameIRegE(size,pfx,rm));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      IRTemp addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      storeLE( mkexpr(addr), getIRegG(size, pfx, rm) );
      DIP("mov%c %s,%s\n", nameISize(size), 
                           nameIRegG(size,pfx,rm), 
                           dis_buf);
      return len+delta0;
   }
}


/* op $immediate, AL/AX/EAX/RAX. */
static
ULong dis_op_imm_A ( Int    size,
                     IROp   op8,
                     Bool   keep,
                     ULong  delta,
                     HChar* t_amd64opc )
{
   Int    size4 = imin(size,4);
   IRType ty    = szToITy(size);
   IRTemp dst0  = newTemp(ty);
   IRTemp src   = newTemp(ty);
   IRTemp dst1  = newTemp(ty);
   Long  lit    = getSDisp(size4,delta);
   assign(dst0, getIRegRAX(size));
   assign(src,  mkU(ty,lit & mkSizeMask(size)));
   assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
   if (isAddSub(op8))
      setFlags_DEP1_DEP2(op8, dst0, src, ty);
   else
   if (isLogic(op8))
      setFlags_DEP1(op8, dst1, ty);
   else
      vpanic("dis_op_imm_A(amd64)");

   if (keep)
      putIRegRAX(size, mkexpr(dst1));

   DIP("%s%c $%lld, %s\n", t_amd64opc, nameISize(size), 
                           lit, nameIRegRAX(size));
   return delta+size4;
}


/* Sign- and Zero-extending moves. */
static
ULong dis_movx_E_G ( Prefix pfx,
                     ULong delta, Int szs, Int szd, Bool sign_extend )
{
   UChar rm = getUChar(delta);
   if (epartIsReg(rm)) {
      putIRegG(szd, pfx, rm,
                    doScalarWidening(
                       szs,szd,sign_extend,
                       getIRegE(szs,pfx,rm)));
      DIP("mov%c%c%c %s,%s\n", sign_extend ? 's' : 'z',
                               nameISize(szs), 
                               nameISize(szd),
                               nameIRegE(szs,pfx,rm),
                               nameIRegG(szd,pfx,rm));
      return 1+delta;
   }

   /* E refers to memory */    
   {
      Int    len;
      HChar  dis_buf[50];
      IRTemp addr = disAMode ( &len, pfx, delta, dis_buf, 0 );
      putIRegG(szd, pfx, rm,
                    doScalarWidening(
                       szs,szd,sign_extend, 
                       loadLE(szToITy(szs),mkexpr(addr))));
      DIP("mov%c%c%c %s,%s\n", sign_extend ? 's' : 'z',
                               nameISize(szs), 
                               nameISize(szd),
                               dis_buf, 
                               nameIRegG(szd,pfx,rm));
      return len+delta;
   }
}


/* Generate code to divide ArchRegs RDX:RAX / EDX:EAX / DX:AX / AX by
   the 64 / 32 / 16 / 8 bit quantity in the given IRTemp.  */
static
void codegen_div ( Int sz, IRTemp t, Bool signed_divide )
{
   /* special-case the 64-bit case */
   if (sz == 8) {
      IROp   op     = signed_divide ? Iop_DivModS128to64 
                                    : Iop_DivModU128to64;
      IRTemp src128 = newTemp(Ity_I128);
      IRTemp dst128 = newTemp(Ity_I128);
      assign( src128, binop(Iop_64HLto128, 
                            getIReg64(R_RDX), 
                            getIReg64(R_RAX)) );
      assign( dst128, binop(op, mkexpr(src128), mkexpr(t)) );
      putIReg64( R_RAX, unop(Iop_128to64,mkexpr(dst128)) );
      putIReg64( R_RDX, unop(Iop_128HIto64,mkexpr(dst128)) );
   } else {
      IROp   op    = signed_divide ? Iop_DivModS64to32 
                                   : Iop_DivModU64to32;
      IRTemp src64 = newTemp(Ity_I64);
      IRTemp dst64 = newTemp(Ity_I64);
      switch (sz) {
      case 4:
         assign( src64, 
                 binop(Iop_32HLto64, getIRegRDX(4), getIRegRAX(4)) );
         assign( dst64, 
                 binop(op, mkexpr(src64), mkexpr(t)) );
         putIRegRAX( 4, unop(Iop_64to32,mkexpr(dst64)) );
         putIRegRDX( 4, unop(Iop_64HIto32,mkexpr(dst64)) );
         break;
      case 2: {
         IROp widen3264 = signed_divide ? Iop_32Sto64 : Iop_32Uto64;
         IROp widen1632 = signed_divide ? Iop_16Sto32 : Iop_16Uto32;
         assign( src64, unop(widen3264,
                             binop(Iop_16HLto32, 
                                   getIRegRDX(2), 
                                   getIRegRAX(2))) );
         assign( dst64, binop(op, mkexpr(src64), unop(widen1632,mkexpr(t))) );
         putIRegRAX( 2, unop(Iop_32to16,unop(Iop_64to32,mkexpr(dst64))) );
         putIRegRDX( 2, unop(Iop_32to16,unop(Iop_64HIto32,mkexpr(dst64))) );
         break;
      }
      case 1: {
         IROp widen3264 = signed_divide ? Iop_32Sto64 : Iop_32Uto64;
         IROp widen1632 = signed_divide ? Iop_16Sto32 : Iop_16Uto32;
         IROp widen816  = signed_divide ? Iop_8Sto16  : Iop_8Uto16;
         assign( src64, unop(widen3264, 
                        unop(widen1632, getIRegRAX(2))) );
         assign( dst64, 
                 binop(op, mkexpr(src64), 
                           unop(widen1632, unop(widen816, mkexpr(t)))) );
         putIRegRAX( 1, unop(Iop_16to8, 
                        unop(Iop_32to16,
                        unop(Iop_64to32,mkexpr(dst64)))) );
         putIRegAH( unop(Iop_16to8, 
                    unop(Iop_32to16,
                    unop(Iop_64HIto32,mkexpr(dst64)))) );
         break;
      }
      default: 
         vpanic("codegen_div(amd64)");
      }
   }
}

static 
ULong dis_Grp1 ( Prefix pfx,
                 ULong delta, UChar modrm, 
                 Int am_sz, Int d_sz, Int sz, Long d64 )
{
   Int     len;
   HChar   dis_buf[50];
   IRType  ty   = szToITy(sz);
   IRTemp  dst1 = newTemp(ty);
   IRTemp  src  = newTemp(ty);
   IRTemp  dst0 = newTemp(ty);
   IRTemp  addr = IRTemp_INVALID;
   IROp    op8  = Iop_INVALID;
   ULong   mask = mkSizeMask(sz);

   switch (gregLO3ofRM(modrm)) {
      case 0: op8 = Iop_Add8; break;  case 1: op8 = Iop_Or8;  break;
      case 2: break;  // ADC
      case 3: break;  // SBB
      case 4: op8 = Iop_And8; break;  case 5: op8 = Iop_Sub8; break;
      case 6: op8 = Iop_Xor8; break;  case 7: op8 = Iop_Sub8; break;
      default: vpanic("dis_Grp1(amd64): unhandled case");
   }

   if (epartIsReg(modrm)) {
      vassert(am_sz == 1);

      assign(dst0, getIRegE(sz,pfx,modrm));
      assign(src,  mkU(ty,d64 & mask));

      if (gregLO3ofRM(modrm) == 2 /* ADC */) {
         helper_ADC( sz, dst1, dst0, src );
      } else 
      if (gregLO3ofRM(modrm) == 3 /* SBB */) {
         helper_SBB( sz, dst1, dst0, src );
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
      }

      if (gregLO3ofRM(modrm) < 7)
         putIRegE(sz, pfx, modrm, mkexpr(dst1));

      delta += (am_sz + d_sz);
      DIP("%s%c $%lld, %s\n", 
          nameGrp1(gregLO3ofRM(modrm)), nameISize(sz), d64, 
          nameIRegE(sz,pfx,modrm));
   } else {
      addr = disAMode ( &len, pfx, delta, dis_buf, /*xtra*/d_sz );

      assign(dst0, loadLE(ty,mkexpr(addr)));
      assign(src, mkU(ty,d64 & mask));

      if (gregLO3ofRM(modrm) == 2 /* ADC */) {
         helper_ADC( sz, dst1, dst0, src );
      } else 
      if (gregLO3ofRM(modrm) == 3 /* SBB */) {
         vassert(0); /* awaiting test case */
         helper_SBB( sz, dst1, dst0, src );
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
      }

      if (gregLO3ofRM(modrm) < 7)
          storeLE(mkexpr(addr), mkexpr(dst1));

      delta += (len+d_sz);
      DIP("%s%c $%lld, %s\n", 
          nameGrp1(gregLO3ofRM(modrm)), nameISize(sz),
          d64, dis_buf);
   }
   return delta;
}


/* Group 2 extended opcodes.  shift_expr must be an 8-bit typed
   expression. */

static
ULong dis_Grp2 ( Prefix pfx,
                 ULong delta, UChar modrm,
                 Int am_sz, Int d_sz, Int sz, IRExpr* shift_expr,
                 HChar* shift_expr_txt )
{
   /* delta on entry points at the modrm byte. */
   HChar  dis_buf[50];
   Int    len;
   Bool   isShift, isRotate, isRotateRC;
   IRType ty    = szToITy(sz);
   IRTemp dst0  = newTemp(ty);
   IRTemp dst1  = newTemp(ty);
   IRTemp addr  = IRTemp_INVALID;

   vassert(sz == 1 || sz == 2 || sz == 4 || sz == 8);

   /* Put value to shift/rotate in dst0. */
   if (epartIsReg(modrm)) {
      assign(dst0, getIRegE(sz, pfx, modrm));
      delta += (am_sz + d_sz);
   } else {
      addr = disAMode ( &len, pfx, delta, dis_buf, 0 );
      assign(dst0, loadLE(ty,mkexpr(addr)));
      delta += len + d_sz;
   }

   isShift = False;
   switch (gregLO3ofRM(modrm)) { case 4: case 5: case 7: isShift = True; }

   isRotate = False;
   switch (gregLO3ofRM(modrm)) { case 0: case 1: isRotate = True; }

   isRotateRC = toBool(gregLO3ofRM(modrm) == 3);

   if (!isShift && !isRotate && !isRotateRC) {
      vex_printf("\ncase %d\n", gregLO3ofRM(modrm));
      vpanic("dis_Grp2(Reg): unhandled case(amd64)");
   }

   if (isRotateRC) {
      vpanic("dis_Grp2(Reg,amd64): unhandled case(RotateRC)");
      vassert(0);
//..       /* call a helper; this insn is so ridiculous it does not deserve
//..          better */
//..       IRTemp   r64  = newTemp(Ity_I64);
//..       IRExpr** args 
//..          = mkIRExprVec_4( widenUto32(mkexpr(dst0)), /* thing to rotate */
//..                           widenUto32(shift_expr),   /* rotate amount */
//..                           widenUto32(mk_x86g_calculate_eflags_all()),
//..                           mkU32(sz) );
//..       assign( r64, mkIRExprCCall(
//..                       Ity_I64, 
//..                       0/*regparm*/, 
//..                       "x86g_calculate_RCR", &x86g_calculate_RCR,
//..                       args
//..                    )
//..             );
//..       /* new eflags in hi half r64; new value in lo half r64 */
//..       assign( dst1, narrowTo(ty, unop(Iop_64to32, mkexpr(r64))) );
//..       stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
//..       stmt( IRStmt_Put( OFFB_CC_DEP1, unop(Iop_64HIto32, mkexpr(r64)) ));
//..       stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
   }

   if (isShift) {

      IRTemp pre64     = newTemp(Ity_I64);
      IRTemp res64     = newTemp(Ity_I64);
      IRTemp res64ss   = newTemp(Ity_I64);
      IRTemp shift_amt = newTemp(Ity_I8);
      UChar  mask      = toUChar(sz==8 ? 63 : 31);
      IROp   op64;

      switch (gregLO3ofRM(modrm)) { 
         case 4: op64 = Iop_Shl64; break;
         case 5: op64 = Iop_Shr64; break;
         case 7: op64 = Iop_Sar64; break;
         default: vpanic("dis_Grp2:shift"); break;
      }

      /* Widen the value to be shifted to 64 bits, do the shift, and
         narrow back down.  This seems surprisingly long-winded, but
         unfortunately the AMD semantics requires that 8/16/32-bit
         shifts give defined results for shift values all the way up
         to 32, and this seems the simplest way to do it.  It has the
         advantage that the only IR level shifts generated are of 64
         bit values, and the shift amount is guaranteed to be in the
         range 0 .. 63, thereby observing the IR semantics requiring
         all shift values to be in the range 0 .. 2^word_size-1. 

         Therefore the shift amount is masked with 63 for 64-bit shifts
         and 31 for all others.
      */
      /* shift_amt = shift_expr & MASK, regardless of operation size */
      assign( shift_amt, binop(Iop_And8, shift_expr, mkU8(mask)) );

      /* suitably widen the value to be shifted to 64 bits. */
      assign( pre64, op64==Iop_Sar64 ? widenSto64(mkexpr(dst0))
                                     : widenUto64(mkexpr(dst0)) );

      /* res64 = pre64 `shift` shift_amt */
      assign( res64, binop(op64, mkexpr(pre64), mkexpr(shift_amt)) );

      /* res64ss = pre64 `shift` ((shift_amt - 1) & MASK) */
      assign( res64ss,
              binop(op64,
                    mkexpr(pre64), 
                    binop(Iop_And8,
                          binop(Iop_Sub8,
                                mkexpr(shift_amt), mkU8(1)),
                          mkU8(mask))) );

      /* Build the flags thunk. */
      setFlags_DEP1_DEP2_shift(op64, res64, res64ss, ty, shift_amt);

      /* Narrow the result back down. */
      assign( dst1, narrowTo(ty, mkexpr(res64)) );

   } /* if (isShift) */

   else 
   if (isRotate) {
      Int    ccOp      = ty==Ity_I8 ? 0 : (ty==Ity_I16 ? 1 
                                        : (ty==Ity_I32 ? 2 : 3));
      Bool   left      = toBool(gregLO3ofRM(modrm) == 0);
      IRTemp rot_amt   = newTemp(Ity_I8);
      IRTemp rot_amt64 = newTemp(Ity_I8);
      IRTemp oldFlags  = newTemp(Ity_I64);
      UChar  mask      = toUChar(sz==8 ? 63 : 31);

      /* rot_amt = shift_expr & mask */
      /* By masking the rotate amount thusly, the IR-level Shl/Shr
         expressions never shift beyond the word size and thus remain
         well defined. */
      assign(rot_amt64, binop(Iop_And8, shift_expr, mkU8(mask)));

      if (ty == Ity_I64)
         assign(rot_amt, mkexpr(rot_amt64));
      else
         assign(rot_amt, binop(Iop_And8, mkexpr(rot_amt64), mkU8(8*sz-1)));

      if (left) {

         /* dst1 = (dst0 << rot_amt) | (dst0 >>u (wordsize-rot_amt)) */
         assign(dst1, 
            binop( mkSizedOp(ty,Iop_Or8),
                   binop( mkSizedOp(ty,Iop_Shl8), 
                          mkexpr(dst0),
                          mkexpr(rot_amt)
                   ),
                   binop( mkSizedOp(ty,Iop_Shr8), 
                          mkexpr(dst0), 
                          binop(Iop_Sub8,mkU8(8*sz), mkexpr(rot_amt))
                   )
            )
         );
         ccOp += AMD64G_CC_OP_ROLB;

      } else { /* right */

         /* dst1 = (dst0 >>u rot_amt) | (dst0 << (wordsize-rot_amt)) */
         assign(dst1, 
            binop( mkSizedOp(ty,Iop_Or8),
                   binop( mkSizedOp(ty,Iop_Shr8), 
                          mkexpr(dst0),
                          mkexpr(rot_amt)
                   ),
                   binop( mkSizedOp(ty,Iop_Shl8), 
                          mkexpr(dst0), 
                          binop(Iop_Sub8,mkU8(8*sz), mkexpr(rot_amt))
                   )
            )
         );
         ccOp += AMD64G_CC_OP_RORB;

      }

      /* dst1 now holds the rotated value.  Build flag thunk.  We
         need the resulting value for this, and the previous flags.
         Except don't set it if the rotate count is zero. */

      assign(oldFlags, mk_amd64g_calculate_rflags_all());

      /* CC_DEP1 is the rotated value.  CC_NDEP is flags before. */
      stmt( IRStmt_Put( OFFB_CC_OP,
                        IRExpr_Mux0X( mkexpr(rot_amt64),
                                      IRExpr_Get(OFFB_CC_OP,Ity_I64),
                                      mkU64(ccOp))) );
      stmt( IRStmt_Put( OFFB_CC_DEP1, 
                        IRExpr_Mux0X( mkexpr(rot_amt64),
                                      IRExpr_Get(OFFB_CC_DEP1,Ity_I64),
                                      widenUto64(mkexpr(dst1)))) );
      stmt( IRStmt_Put( OFFB_CC_DEP2, 
                        IRExpr_Mux0X( mkexpr(rot_amt64),
                                      IRExpr_Get(OFFB_CC_DEP2,Ity_I64),
                                      mkU64(0))) );
      stmt( IRStmt_Put( OFFB_CC_NDEP, 
                        IRExpr_Mux0X( mkexpr(rot_amt64),
                                      IRExpr_Get(OFFB_CC_NDEP,Ity_I64),
                                      mkexpr(oldFlags))) );
   } /* if (isRotate) */

   /* Save result, and finish up. */
   if (epartIsReg(modrm)) {
      putIRegE(sz, pfx, modrm, mkexpr(dst1));
      if (vex_traceflags & VEX_TRACE_FE) {
         vex_printf("%s%c ",
                    nameGrp2(gregLO3ofRM(modrm)), nameISize(sz) );
         if (shift_expr_txt)
            vex_printf("%s", shift_expr_txt);
         else
            ppIRExpr(shift_expr);
         vex_printf(", %s\n", nameIRegE(sz,pfx,modrm));
      }
   } else {
      storeLE(mkexpr(addr), mkexpr(dst1));
      if (vex_traceflags & VEX_TRACE_FE) {
         vex_printf("%s%c ",
                    nameGrp2(gregLO3ofRM(modrm)), nameISize(sz) );
         if (shift_expr_txt)
            vex_printf("%s", shift_expr_txt);
         else
            ppIRExpr(shift_expr);
         vex_printf(", %s\n", dis_buf);
      }
   }
   return delta;
}


/* Group 8 extended opcodes (but BT/BTS/BTC/BTR only). */
static
ULong dis_Grp8_Imm ( Prefix pfx,
                     ULong delta, UChar modrm,
                     Int am_sz, Int sz, ULong src_val,
                     Bool* decode_OK )
{
   /* src_val denotes a d8.
      And delta on entry points at the modrm byte. */

   IRType ty     = szToITy(sz);
   IRTemp t2     = newTemp(Ity_I64);
   IRTemp t2m    = newTemp(Ity_I64);
   IRTemp t_addr = IRTemp_INVALID;
   HChar  dis_buf[50];
   ULong  mask;

   /* we're optimists :-) */
   *decode_OK = True;

   /* Limit src_val -- the bit offset -- to something within a word.
      The Intel docs say that literal offsets larger than a word are
      masked in this way. */
   switch (sz) {
      case 2:  src_val &= 15; break;
      case 4:  src_val &= 31; break;
      case 8:  src_val &= 63; break;
      default: *decode_OK = False; return delta;
   }

   /* Invent a mask suitable for the operation. */
   switch (gregLO3ofRM(modrm)) {
      case 4: /* BT */  mask = 0;               break;
      case 5: /* BTS */ mask = 1 << src_val;    break;
      case 6: /* BTR */ mask = ~(1 << src_val); break;
      case 7: /* BTC */ mask = 1 << src_val;    break;
         /* If this needs to be extended, probably simplest to make a
            new function to handle the other cases (0 .. 3).  The
            Intel docs do however not indicate any use for 0 .. 3, so
            we don't expect this to happen. */
      default: *decode_OK = False; return delta;
   }

   /* Fetch the value to be tested and modified into t2, which is
      64-bits wide regardless of sz. */
   if (epartIsReg(modrm)) {
      vassert(am_sz == 1);
      assign( t2, widenUto64(getIRegE(sz, pfx, modrm)) );
      delta += (am_sz + 1);
      DIP("%s%c $0x%llx, %s\n", nameGrp8(gregLO3ofRM(modrm)), 
                                nameISize(sz),
                                src_val, nameIRegE(sz,pfx,modrm));
   } else {
      Int len;
      t_addr = disAMode ( &len, pfx, delta, dis_buf, 1 );
      delta  += (len+1);
      assign( t2, widenUto64(loadLE(ty, mkexpr(t_addr))) );
      DIP("%s%c $0x%llx, %s\n", nameGrp8(gregLO3ofRM(modrm)), 
                                nameISize(sz),
                                src_val, dis_buf);
   }

   /* Copy relevant bit from t2 into the carry flag. */
   /* Flags: C=selected bit, O,S,Z,A,P undefined, so are set to zero. */
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(AMD64G_CC_OP_COPY) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0) ));
   stmt( IRStmt_Put( 
            OFFB_CC_DEP1,
            binop(Iop_And64,
                  binop(Iop_Shr64, mkexpr(t2), mkU8(src_val)),
                  mkU64(1))
       ));

   /* Compute the new value into t2m, if non-BT. */
   switch (gregLO3ofRM(modrm)) {
      case 4: /* BT */
         break;
      case 5: /* BTS */
         assign( t2m, binop(Iop_Or64, mkU64(mask), mkexpr(t2)) );
         break;
      case 6: /* BTR */
         assign( t2m, binop(Iop_And64, mkU64(mask), mkexpr(t2)) );
         break;
      case 7: /* BTC */
         assign( t2m, binop(Iop_Xor64, mkU64(mask), mkexpr(t2)) );
         break;
     default: 
         vassert(0);
   }

   /* Write the result back, if non-BT. */
   if (gregLO3ofRM(modrm) != 4 /* BT */) {
      if (epartIsReg(modrm)) {
	putIRegE(sz, pfx, modrm, narrowTo(ty, mkexpr(t2m)));
      } else {
	storeLE(mkexpr(t_addr), narrowTo(ty, mkexpr(t2m)));
      }
   }

   return delta;
}


/* Signed/unsigned widening multiply.  Generate IR to multiply the
   value in RAX/EAX/AX/AL by the given IRTemp, and park the result in
   RDX:RAX/EDX:EAX/DX:AX/AX.
*/
static void codegen_mulL_A_D ( Int sz, Bool syned, 
                               IRTemp tmp, HChar* tmp_txt )
{
   IRType ty = szToITy(sz);
   IRTemp t1 = newTemp(ty);

   assign( t1, getIRegRAX(sz) );

   switch (ty) {
      case Ity_I64: {
         IRTemp res128  = newTemp(Ity_I128);
         IRTemp resHi   = newTemp(Ity_I64);
         IRTemp resLo   = newTemp(Ity_I64);
         IROp   mulOp   = syned ? Iop_MullS64 : Iop_MullU64;
         UInt   tBaseOp = syned ? AMD64G_CC_OP_SMULQ : AMD64G_CC_OP_UMULQ;
         setFlags_MUL ( Ity_I64, t1, tmp, tBaseOp );
         assign( res128, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_128HIto64,mkexpr(res128)));
         assign( resLo, unop(Iop_128to64,mkexpr(res128)));
         putIReg64(R_RDX, mkexpr(resHi));
         putIReg64(R_RAX, mkexpr(resLo));
         break;
      }
      case Ity_I32: {
         IRTemp res64   = newTemp(Ity_I64);
         IRTemp resHi   = newTemp(Ity_I32);
         IRTemp resLo   = newTemp(Ity_I32);
         IROp   mulOp   = syned ? Iop_MullS32 : Iop_MullU32;
         UInt   tBaseOp = syned ? AMD64G_CC_OP_SMULB : AMD64G_CC_OP_UMULB;
         setFlags_MUL ( Ity_I32, t1, tmp, tBaseOp );
         assign( res64, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_64HIto32,mkexpr(res64)));
         assign( resLo, unop(Iop_64to32,mkexpr(res64)));
         putIRegRDX(4, mkexpr(resHi));
         putIRegRAX(4, mkexpr(resLo));
         break;
      }
      case Ity_I16: {
         IRTemp res32   = newTemp(Ity_I32);
         IRTemp resHi   = newTemp(Ity_I16);
         IRTemp resLo   = newTemp(Ity_I16);
         IROp   mulOp   = syned ? Iop_MullS16 : Iop_MullU16;
         UInt   tBaseOp = syned ? AMD64G_CC_OP_SMULB : AMD64G_CC_OP_UMULB;
         setFlags_MUL ( Ity_I16, t1, tmp, tBaseOp );
         assign( res32, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_32HIto16,mkexpr(res32)));
         assign( resLo, unop(Iop_32to16,mkexpr(res32)));
         putIRegRDX(2, mkexpr(resHi));
         putIRegRAX(2, mkexpr(resLo));
         break;
      }
      case Ity_I8: {
         IRTemp res16   = newTemp(Ity_I16);
         IRTemp resHi   = newTemp(Ity_I8);
         IRTemp resLo   = newTemp(Ity_I8);
         IROp   mulOp   = syned ? Iop_MullS8 : Iop_MullU8;
         UInt   tBaseOp = syned ? AMD64G_CC_OP_SMULB : AMD64G_CC_OP_UMULB;
         setFlags_MUL ( Ity_I8, t1, tmp, tBaseOp );
         assign( res16, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_16HIto8,mkexpr(res16)));
         assign( resLo, unop(Iop_16to8,mkexpr(res16)));
         putIRegRAX(2, mkexpr(res16));
         break;
      }
      default:
         ppIRType(ty);
         vpanic("codegen_mulL_A_D(amd64)");
   }
   DIP("%s%c %s\n", syned ? "imul" : "mul", nameISize(sz), tmp_txt);
}


/* Group 3 extended opcodes. */
static 
ULong dis_Grp3 ( Prefix pfx, Int sz, ULong delta )
{
   Long    d64;
   UChar   modrm;
   HChar   dis_buf[50];
   Int     len;
   IRTemp  addr;
   IRType  ty = szToITy(sz);
   IRTemp  t1 = newTemp(ty);
   IRTemp dst1, src, dst0;
   modrm = getUChar(delta);
   if (epartIsReg(modrm)) {
      switch (gregLO3ofRM(modrm)) {
         case 0: { /* TEST */
            delta++; 
            d64 = getSDisp(imin(4,sz), delta); 
            delta += imin(4,sz);
            dst1 = newTemp(ty);
            assign(dst1, binop(mkSizedOp(ty,Iop_And8),
                               getIRegE(sz,pfx,modrm),
                               mkU(ty, d64 & mkSizeMask(sz))));
            setFlags_DEP1( Iop_And8, dst1, ty );
            DIP("test%c $%lld, %s\n", 
                nameISize(sz), d64, 
                nameIRegE(sz, pfx, modrm));
            break;
         }
         case 2: /* NOT */
            delta++;
            putIRegE(sz, pfx, modrm,
                              unop(mkSizedOp(ty,Iop_Not8),
                                   getIRegE(sz, pfx, modrm)));
            DIP("not%c %s\n", nameISize(sz), 
                              nameIRegE(sz, pfx, modrm));
            break;
         case 3: /* NEG */
            delta++;
            dst0 = newTemp(ty);
            src  = newTemp(ty);
            dst1 = newTemp(ty);
            assign(dst0, mkU(ty,0));
            assign(src,  getIRegE(sz, pfx, modrm));
            assign(dst1, binop(mkSizedOp(ty,Iop_Sub8), mkexpr(dst0), mkexpr(src)));
            setFlags_DEP1_DEP2(Iop_Sub8, dst0, src, ty);
            putIRegE(sz, pfx, modrm, mkexpr(dst1));
            DIP("neg%c %s\n", nameISize(sz), nameIRegE(sz, pfx, modrm));
            break;
         case 4: /* MUL (unsigned widening) */
            delta++;
            src = newTemp(ty);
            assign(src, getIRegE(sz,pfx,modrm));
            codegen_mulL_A_D ( sz, False, src,
                               nameIRegE(sz,pfx,modrm) );
            break;
         case 5: /* IMUL (signed widening) */
            delta++;
            src = newTemp(ty);
            assign(src, getIRegE(sz,pfx,modrm));
            codegen_mulL_A_D ( sz, True, src,
                               nameIRegE(sz,pfx,modrm) );
            break;
         case 6: /* DIV */
            delta++;
            assign( t1, getIRegE(sz, pfx, modrm) );
            codegen_div ( sz, t1, False );
            DIP("div%c %s\n", nameISize(sz), 
                              nameIRegE(sz, pfx, modrm));
            break;
         case 7: /* IDIV */
            delta++;
            assign( t1, getIRegE(sz, pfx, modrm) );
            codegen_div ( sz, t1, True );
            DIP("idiv%c %s\n", nameISize(sz), 
                               nameIRegE(sz, pfx, modrm));
            break;
         default: 
            vex_printf(
               "unhandled Grp3(R) case %d\n", (Int)gregLO3ofRM(modrm));
            vpanic("Grp3(amd64)");
      }
   } else {
      addr = disAMode ( &len, pfx, delta, dis_buf,
                        /* we have to inform disAMode of any immediate
			   bytes used */
                        gregLO3ofRM(modrm)==0/*TEST*/
                           ? imin(4,sz)
                           : 0
                      );
      t1   = newTemp(ty);
      delta += len;
      assign(t1, loadLE(ty,mkexpr(addr)));
      switch (gregLO3ofRM(modrm)) {
         case 0: { /* TEST */
            d64 = getSDisp(imin(4,sz), delta); 
            delta += imin(4,sz);
            dst1 = newTemp(ty);
            assign(dst1, binop(mkSizedOp(ty,Iop_And8),
                               mkexpr(t1), 
                               mkU(ty, d64 & mkSizeMask(sz))));
            setFlags_DEP1( Iop_And8, dst1, ty );
            DIP("test%c $%lld, %s\n", nameISize(sz), d64, dis_buf);
            break;
         }
         /* probably OK, but awaiting test case */
         case 2: /* NOT */
            storeLE( mkexpr(addr), unop(mkSizedOp(ty,Iop_Not8), mkexpr(t1)));
            DIP("not%c %s\n", nameISize(sz), dis_buf);
            break;
         case 3: /* NEG */
            dst0 = newTemp(ty);
            src  = newTemp(ty);
            dst1 = newTemp(ty);
            assign(dst0, mkU(ty,0));
            assign(src,  mkexpr(t1));
            assign(dst1, binop(mkSizedOp(ty,Iop_Sub8), mkexpr(dst0), mkexpr(src)));
            setFlags_DEP1_DEP2(Iop_Sub8, dst0, src, ty);
            storeLE( mkexpr(addr), mkexpr(dst1) );
            DIP("neg%c %s\n", nameISize(sz), dis_buf);
            break;
         case 4: /* MUL (unsigned widening) */
            codegen_mulL_A_D ( sz, False, t1, dis_buf );
            break;
         case 5: /* IMUL */
            codegen_mulL_A_D ( sz, True, t1, dis_buf );
            break;
         case 6: /* DIV */
            codegen_div ( sz, t1, False );
            DIP("div%c %s\n", nameISize(sz), dis_buf);
            break;
         case 7: /* IDIV */
            codegen_div ( sz, t1, True );
            DIP("idiv%c %s\n", nameISize(sz), dis_buf);
            break;
         default: 
            vex_printf(
               "unhandled Grp3(M) case %d\n", (Int)gregLO3ofRM(modrm));
            vpanic("Grp3(amd64)");
      }
   }
   return delta;
}


/* Group 4 extended opcodes. */
static
ULong dis_Grp4 ( Prefix pfx, ULong delta )
{
   Int   alen;
   UChar modrm;
   HChar dis_buf[50];
   IRType ty = Ity_I8;
   IRTemp t1 = newTemp(ty);
   IRTemp t2 = newTemp(ty);

   modrm = getUChar(delta);
   if (epartIsReg(modrm)) {
      assign(t1, getIRegE(1, pfx, modrm));
      switch (gregLO3ofRM(modrm)) {
         case 0: /* INC */
            assign(t2, binop(Iop_Add8, mkexpr(t1), mkU8(1)));
            putIRegE(1, pfx, modrm, mkexpr(t2));
            setFlags_INC_DEC( True, t2, ty );
            break;
         case 1: /* DEC */
            assign(t2, binop(Iop_Sub8, mkexpr(t1), mkU8(1)));
            putIRegE(1, pfx, modrm, mkexpr(t2));
            setFlags_INC_DEC( False, t2, ty );
            break;
         default: 
            vex_printf(
               "unhandled Grp4(R) case %d\n", (Int)gregLO3ofRM(modrm));
            vpanic("Grp4(amd64,R)");
      }
      delta++;
      DIP("%sb %s\n", nameGrp4(gregLO3ofRM(modrm)),
                      nameIRegE(1, pfx, modrm));
   } else {
      IRTemp addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
      assign( t1, loadLE(ty, mkexpr(addr)) );
      switch (gregLO3ofRM(modrm)) {
         case 0: /* INC */
            assign(t2, binop(Iop_Add8, mkexpr(t1), mkU8(1)));
            storeLE( mkexpr(addr), mkexpr(t2) );
            setFlags_INC_DEC( True, t2, ty );
            break;
         case 1: /* DEC */
            assign(t2, binop(Iop_Sub8, mkexpr(t1), mkU8(1)));
            storeLE( mkexpr(addr), mkexpr(t2) );
            setFlags_INC_DEC( False, t2, ty );
            break;
         default: 
            vex_printf(
               "unhandled Grp4(M) case %d\n", (Int)gregLO3ofRM(modrm));
            vpanic("Grp4(amd64,M)");
      }
      delta += alen;
      DIP("%sb %s\n", nameGrp4(gregLO3ofRM(modrm)), dis_buf);
   }
   return delta;
}


/* Group 5 extended opcodes. */
static
ULong dis_Grp5 ( Prefix pfx, Int sz, ULong delta, DisResult* whatNext )
{
   Int     len;
   UChar   modrm;
   HChar   dis_buf[50];
   IRTemp  addr = IRTemp_INVALID;
   IRType  ty = szToITy(sz);
   IRTemp  t1 = newTemp(ty);
   IRTemp  t2 = IRTemp_INVALID;
   IRTemp  t3 = IRTemp_INVALID;
   Bool    showSz = True;

   modrm = getUChar(delta);
   if (epartIsReg(modrm)) {
      assign(t1, getIRegE(sz,pfx,modrm));
      switch (gregLO3ofRM(modrm)) {
         case 0: /* INC */
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Add8),
                             mkexpr(t1), mkU(ty,1)));
            setFlags_INC_DEC( True, t2, ty );
            putIRegE(sz,pfx,modrm, mkexpr(t2));
            break;
         case 1: /* DEC */
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Sub8),
                             mkexpr(t1), mkU(ty,1)));
            setFlags_INC_DEC( False, t2, ty );
            putIRegE(sz,pfx,modrm, mkexpr(t2));
            break;
         case 2: /* call Ev */
            /* Ignore any sz value and operate as if sz==8. */
            vassert(sz == 4);
            sz = 8;
            t3 = newTemp(Ity_I64);
            assign(t3, getIRegE(sz,pfx,modrm));
            t2 = newTemp(Ity_I64);
            assign(t2, binop(Iop_Sub64, getIReg64(R_RSP), mkU64(8)));
            putIReg64(R_RSP, mkexpr(t2));
            storeLE( mkexpr(t2), mkU64(guest_rip_bbstart+delta+1));
            jmp_treg(Ijk_Call,t3);
            *whatNext = Dis_StopHere;
            showSz = False;
            break;
         case 4: /* jmp Ev */
            /* Ignore any sz value and operate as if sz==8. */
            vassert(sz == 4);
            sz = 8;
            t3 = newTemp(Ity_I64);
            assign(t3, getIRegE(sz,pfx,modrm));
            jmp_treg(Ijk_Boring,t3);
            *whatNext = Dis_StopHere;
            showSz = False;
            break;
         default: 
            vex_printf(
               "unhandled Grp5(R) case %d\n", (Int)gregLO3ofRM(modrm));
            vpanic("Grp5(amd64)");
      }
      delta++;
      DIP("%s%c %s\n", nameGrp5(gregLO3ofRM(modrm)),
                       showSz ? nameISize(sz) : ' ', 
                       nameIRegE(sz, pfx, modrm));
   } else {
      addr = disAMode ( &len, pfx, delta, dis_buf, 0 );
      if (gregLO3ofRM(modrm) != 2 && gregLO3ofRM(modrm) != 4
                                  && gregLO3ofRM(modrm) != 6) {
         assign(t1, loadLE(ty,mkexpr(addr)));
      }
      switch (gregLO3ofRM(modrm)) {
         case 0: /* INC */ 
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Add8),
                             mkexpr(t1), mkU(ty,1)));
            setFlags_INC_DEC( True, t2, ty );
            storeLE(mkexpr(addr),mkexpr(t2));
            break;
         case 1: /* DEC */ 
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Sub8),
                             mkexpr(t1), mkU(ty,1)));
            setFlags_INC_DEC( False, t2, ty );
            storeLE(mkexpr(addr),mkexpr(t2));
            break;
         case 2: /* call Ev */
            /* Ignore any sz value and operate as if sz==8. */
            vassert(sz == 4);
            sz = 8;
            t3 = newTemp(Ity_I64);
            assign(t3, loadLE(Ity_I64,mkexpr(addr)));
            t2 = newTemp(Ity_I64);
            assign(t2, binop(Iop_Sub64, getIReg64(R_RSP), mkU64(8)));
            putIReg64(R_RSP, mkexpr(t2));
            storeLE( mkexpr(t2), mkU64(guest_rip_bbstart+delta+len));
            jmp_treg(Ijk_Call,t3);
            *whatNext = Dis_StopHere;
            showSz = False;
            break;
         case 4: /* JMP Ev */
            /* Ignore any sz value and operate as if sz==8. */
            vassert(sz == 4);
            sz = 8;
            t3 = newTemp(Ity_I64);
            assign(t3, loadLE(Ity_I64,mkexpr(addr)));
            jmp_treg(Ijk_Boring,t3);
            *whatNext = Dis_StopHere;
            showSz = False;
            break;
         case 6: /* PUSH Ev */
            /* There is no encoding for 32-bit operand size; hence ... */
            if (sz == 4) sz = 8;
            vassert(sz == 8 || sz == 2);
            if (sz == 8) {
               t3 = newTemp(Ity_I64);
               assign(t3, loadLE(Ity_I64,mkexpr(addr)));
               t2 = newTemp(Ity_I64);
               assign( t2, binop(Iop_Sub64,getIReg64(R_RSP),mkU64(sz)) );
               putIReg64(R_RSP, mkexpr(t2) );
               storeLE( mkexpr(t2), mkexpr(t3) );
               break;
	    } else {
               goto unhandled; /* awaiting test case */
	    }
         default: 
         unhandled:
            vex_printf(
               "unhandled Grp5(M) case %d\n", (Int)gregLO3ofRM(modrm));
            vpanic("Grp5(amd64)");
      }
      delta += len;
      DIP("%s%c %s\n", nameGrp5(gregLO3ofRM(modrm)),
                       showSz ? nameISize(sz) : ' ', 
                       dis_buf);
   }
   return delta;
}


/*------------------------------------------------------------*/
/*--- Disassembling string ops (including REP prefixes)    ---*/
/*------------------------------------------------------------*/

/* Code shared by all the string ops */
static
void dis_string_op_increment ( Int sz, IRTemp t_inc )
{
   UChar logSz;
   if (sz == 8 || sz == 4 || sz == 2) {
      logSz = 1;
      if (sz == 4) logSz = 2;
      if (sz == 8) logSz = 3;
      assign( t_inc, 
              binop(Iop_Shl64, IRExpr_Get( OFFB_DFLAG, Ity_I64 ),
                               mkU8(logSz) ) );
   } else {
      assign( t_inc, 
              IRExpr_Get( OFFB_DFLAG, Ity_I64 ) );
   }
}

static
void dis_string_op( void (*dis_OP)( Int, IRTemp ), 
                    Int sz, HChar* name, Prefix pfx )
{
   IRTemp t_inc = newTemp(Ity_I64);
   /* Really we ought to inspect the override prefixes, but we don't.
      The following assertion catches any resulting sillyness. */
   vassert(pfx == clearSegBits(pfx));
   dis_string_op_increment(sz, t_inc);
   dis_OP( sz, t_inc );
   DIP("%s%c\n", name, nameISize(sz));
}

static 
void dis_MOVS ( Int sz, IRTemp t_inc )
{
   IRType ty = szToITy(sz);
   IRTemp td = newTemp(Ity_I64);   /* RDI */
   IRTemp ts = newTemp(Ity_I64);   /* RSI */

   assign( td, getIReg64(R_RDI) );
   assign( ts, getIReg64(R_RSI) );

   storeLE( mkexpr(td), loadLE(ty,mkexpr(ts)) );

   putIReg64( R_RDI, binop(Iop_Add64, mkexpr(td), mkexpr(t_inc)) );
   putIReg64( R_RSI, binop(Iop_Add64, mkexpr(ts), mkexpr(t_inc)) );
}

//.. //-- static 
//.. //-- void dis_LODS ( UCodeBlock* cb, Int sz, Int t_inc )
//.. //-- {
//.. //--    Int ta = newTemp(cb);   /* EAX */
//.. //--    Int ts = newTemp(cb);   /* ESI */
//.. //-- 
//.. //--    uInstr2(cb, GET,    4, ArchReg, R_ESI, TempReg, ts);
//.. //--    uInstr2(cb, LOAD,  sz, TempReg, ts,    TempReg, ta);
//.. //--    uInstr2(cb, PUT,   sz, TempReg, ta,    ArchReg, R_EAX);
//.. //-- 
//.. //--    uInstr2(cb, ADD,   4, TempReg, t_inc, TempReg, ts);
//.. //--    uInstr2(cb, PUT,   4, TempReg, ts,    ArchReg, R_ESI);
//.. //-- }

static 
void dis_STOS ( Int sz, IRTemp t_inc )
{
   IRType ty = szToITy(sz);
   IRTemp ta = newTemp(ty);        /* rAX */
   IRTemp td = newTemp(Ity_I64);   /* RDI */

   assign( ta, getIRegRAX(sz) );

   assign( td, getIReg64(R_RDI) );

   storeLE( mkexpr(td), mkexpr(ta) );

   putIReg64( R_RDI, binop(Iop_Add64, mkexpr(td), mkexpr(t_inc)) );
}

static 
void dis_CMPS ( Int sz, IRTemp t_inc )
{
   IRType ty  = szToITy(sz);
   IRTemp tdv = newTemp(ty);      /* (RDI) */
   IRTemp tsv = newTemp(ty);      /* (RSI) */
   IRTemp td  = newTemp(Ity_I64); /*  RDI  */
   IRTemp ts  = newTemp(Ity_I64); /*  RSI  */

   assign( td, getIReg64(R_RDI) );

   assign( ts, getIReg64(R_RSI) );

   assign( tdv, loadLE(ty,mkexpr(td)) );

   assign( tsv, loadLE(ty,mkexpr(ts)) );

   setFlags_DEP1_DEP2 ( Iop_Sub8, tsv, tdv, ty );

   putIReg64(R_RDI, binop(Iop_Add64, mkexpr(td), mkexpr(t_inc)) );

   putIReg64(R_RSI, binop(Iop_Add64, mkexpr(ts), mkexpr(t_inc)) );
}

static 
void dis_SCAS ( Int sz, IRTemp t_inc )
{
   IRType ty  = szToITy(sz);
   IRTemp ta  = newTemp(ty);       /*  rAX  */
   IRTemp td  = newTemp(Ity_I64);  /*  RDI  */
   IRTemp tdv = newTemp(ty);       /* (RDI) */

   assign( ta, getIRegRAX(sz) );

   assign( td, getIReg64(R_RDI) );

   assign( tdv, loadLE(ty,mkexpr(td)) );

   setFlags_DEP1_DEP2 ( Iop_Sub8, ta, tdv, ty );

   putIReg64(R_RDI, binop(Iop_Add64, mkexpr(td), mkexpr(t_inc)) );
}


/* Wrap the appropriate string op inside a REP/REPE/REPNE.  We assume
   the insn is the last one in the basic block, and so emit a jump to
   the next insn, rather than just falling through. */
static 
void dis_REP_op ( AMD64Condcode cond,
                  void (*dis_OP)(Int, IRTemp),
                  Int sz, Addr64 rip, Addr64 rip_next, HChar* name,
                  Prefix pfx )
{
   IRTemp t_inc = newTemp(Ity_I64);
   IRTemp tc    = newTemp(Ity_I64);  /*  RCX  */

   /* Really we ought to inspect the override prefixes, but we don't.
      The following assertion catches any resulting sillyness. */
   vassert(pfx == clearSegBits(pfx));

   assign( tc, getIReg64(R_RCX) );

   stmt( IRStmt_Exit( binop(Iop_CmpEQ64,mkexpr(tc),mkU64(0)),
                      Ijk_Boring,
                      IRConst_U64(rip_next) ) );

   putIReg64(R_RCX, binop(Iop_Sub64, mkexpr(tc), mkU64(1)) );

   dis_string_op_increment(sz, t_inc);
   dis_OP (sz, t_inc);

   if (cond == AMD64CondAlways) {
      jmp_lit(Ijk_Boring,rip);
   } else {
      stmt( IRStmt_Exit( mk_amd64g_calculate_condition(cond),
                         Ijk_Boring,
                         IRConst_U64(rip) ) );
      jmp_lit(Ijk_Boring,rip_next);
   }
   DIP("%s%c\n", name, nameISize(sz));
}


/*------------------------------------------------------------*/
/*--- Arithmetic, etc.                                     ---*/
/*------------------------------------------------------------*/

/* IMUL E, G.  Supplied eip points to the modR/M byte. */
static
ULong dis_mul_E_G ( Prefix      pfx,
                    Int         size, 
                    ULong       delta0 )
{
   Int    alen;
   HChar  dis_buf[50];
   UChar  rm = getUChar(delta0);
   IRType ty = szToITy(size);
   IRTemp te = newTemp(ty);
   IRTemp tg = newTemp(ty);
   IRTemp resLo = newTemp(ty);

   assign( tg, getIRegG(size, pfx, rm) );
   if (epartIsReg(rm)) {
      assign( te, getIRegE(size, pfx, rm) );
   } else {
      IRTemp addr = disAMode( &alen, pfx, delta0, dis_buf, 0 );
      assign( te, loadLE(ty,mkexpr(addr)) );
   }

   setFlags_MUL ( ty, te, tg, AMD64G_CC_OP_SMULB );

   assign( resLo, binop( mkSizedOp(ty, Iop_Mul8), mkexpr(te), mkexpr(tg) ) );

   putIRegG(size, pfx, rm, mkexpr(resLo) );

   if (epartIsReg(rm)) {
      DIP("imul%c %s, %s\n", nameISize(size), 
                             nameIRegE(size,pfx,rm),
                             nameIRegG(size,pfx,rm));
      return 1+delta0;
   } else {
      DIP("imul%c %s, %s\n", nameISize(size), 
                             dis_buf, 
                             nameIRegG(size,pfx,rm));
      return alen+delta0;
   }
}


/* IMUL I * E -> G.  Supplied rip points to the modR/M byte. */
static
ULong dis_imul_I_E_G ( Prefix      pfx,
                       Int         size, 
                       ULong       delta,
                       Int         litsize )
{
   Long   d64;
   Int    alen;
   HChar  dis_buf[50];
   UChar  rm = getUChar(delta);
   IRType ty = szToITy(size);
   IRTemp te = newTemp(ty);
   IRTemp tl = newTemp(ty);
   IRTemp resLo = newTemp(ty);

   vassert(/*size == 1 ||*/ size == 2 || size == 4 || size == 8);

   if (epartIsReg(rm)) {
      assign(te, getIRegE(size, pfx, rm));
      delta++;
   } else {
      IRTemp addr = disAMode( &alen, pfx, delta, dis_buf, 
                                     imin(4,litsize) );
      assign(te, loadLE(ty, mkexpr(addr)));
      delta += alen;
   }
   d64 = getSDisp(imin(4,litsize),delta);
   delta += imin(4,litsize);

   d64 &= mkSizeMask(size);
   assign(tl, mkU(ty,d64));

   assign( resLo, binop( mkSizedOp(ty, Iop_Mul8), mkexpr(te), mkexpr(tl) ));

   setFlags_MUL ( ty, te, tl, AMD64G_CC_OP_SMULB );

   putIRegG(size, pfx, rm, mkexpr(resLo));

   DIP("imul%c $%lld, %s, %s\n", 
       nameISize(size), d64, 
       ( epartIsReg(rm) ? nameIRegE(size,pfx,rm) : dis_buf ),
       nameIRegG(size,pfx,rm) );
   return delta;
}


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- x87 FLOATING POINT INSTRUCTIONS                      ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

/* --- Helper functions for dealing with the register stack. --- */

/* --- Set the emulation-warning pseudo-register. --- */

static void put_emwarn ( IRExpr* e /* :: Ity_I32 */ )
{
   vassert(typeOfIRExpr(irbb->tyenv, e) == Ity_I32);
   stmt( IRStmt_Put( OFFB_EMWARN, e ) );
}

/* --- Produce an IRExpr* denoting a 64-bit QNaN. --- */

static IRExpr* mkQNaN64 ( void )
{
  /* QNaN is 0 2047 1 0(51times) 
     == 0b 11111111111b 1 0(51times)
     == 0x7FF8 0000 0000 0000
   */
   return IRExpr_Const(IRConst_F64i(0x7FF8000000000000ULL));
}

/* --------- Get/put the top-of-stack pointer :: Ity_I32 --------- */

static IRExpr* get_ftop ( void )
{
   return IRExpr_Get( OFFB_FTOP, Ity_I32 );
}

static void put_ftop ( IRExpr* e )
{
   vassert(typeOfIRExpr(irbb->tyenv, e) == Ity_I32);
   stmt( IRStmt_Put( OFFB_FTOP, e ) );
}

//.. /* --------- Get/put the C3210 bits. --------- */
//.. 
//.. static IRExpr* get_C3210 ( void )
//.. {
//..    return IRExpr_Get( OFFB_FC3210, Ity_I32 );
//.. }
//.. 
//.. static void put_C3210 ( IRExpr* e )
//.. {
//..    stmt( IRStmt_Put( OFFB_FC3210, e ) );
//.. }

/* --------- Get/put the FPU rounding mode. --------- */
static IRExpr* /* :: Ity_I32 */ get_fpround ( void )
{
   return unop(Iop_64to32, IRExpr_Get( OFFB_FPROUND, Ity_I64 ));
}

//.. static void put_fpround ( IRExpr* /* :: Ity_I32 */ e )
//.. {
//..    vassert(typeOfIRExpr(irbb->tyenv, e) == Ity_I32);
//..    stmt( IRStmt_Put( OFFB_FPROUND, unop(Iop_32Uto64,e) ) );
//.. }


/* --------- Synthesise a 2-bit FPU rounding mode. --------- */
/* Produces a value in 0 .. 3, which is encoded as per the type
   IRRoundingMode.  Since the guest_FPROUND value is also encoded as
   per IRRoundingMode, we merely need to get it and mask it for
   safety.
*/
static IRExpr* /* :: Ity_I32 */ get_roundingmode ( void )
{
   return binop( Iop_And32, get_fpround(), mkU32(3) );
}


/* --------- Get/set FP register tag bytes. --------- */

/* Given i, and some expression e, generate 'ST_TAG(i) = e'. */

static void put_ST_TAG ( Int i, IRExpr* value )
{
   IRArray* descr;
   vassert(typeOfIRExpr(irbb->tyenv, value) == Ity_I8);
   descr = mkIRArray( OFFB_FPTAGS, Ity_I8, 8 );
   stmt( IRStmt_PutI( descr, get_ftop(), i, value ) );
}

/* Given i, generate an expression yielding 'ST_TAG(i)'.  This will be
   zero to indicate "Empty" and nonzero to indicate "NonEmpty".  */

static IRExpr* get_ST_TAG ( Int i )
{
   IRArray* descr = mkIRArray( OFFB_FPTAGS, Ity_I8, 8 );
   return IRExpr_GetI( descr, get_ftop(), i );
}


/* --------- Get/set FP registers. --------- */

/* Given i, and some expression e, emit 'ST(i) = e' and set the
   register's tag to indicate the register is full.  The previous
   state of the register is not checked. */

static void put_ST_UNCHECKED ( Int i, IRExpr* value )
{
   IRArray* descr;
   vassert(typeOfIRExpr(irbb->tyenv, value) == Ity_F64);
   descr = mkIRArray( OFFB_FPREGS, Ity_F64, 8 );
   stmt( IRStmt_PutI( descr, get_ftop(), i, value ) );
   /* Mark the register as in-use. */
   put_ST_TAG(i, mkU8(1));
}

/* Given i, and some expression e, emit
      ST(i) = is_full(i) ? NaN : e
   and set the tag accordingly.
*/

static void put_ST ( Int i, IRExpr* value )
{
   put_ST_UNCHECKED( i,
                     IRExpr_Mux0X( get_ST_TAG(i),
                                   /* 0 means empty */
                                   value,
                                   /* non-0 means full */
                                   mkQNaN64()
                   )
   );
}


/* Given i, generate an expression yielding 'ST(i)'. */

static IRExpr* get_ST_UNCHECKED ( Int i )
{
   IRArray* descr = mkIRArray( OFFB_FPREGS, Ity_F64, 8 );
   return IRExpr_GetI( descr, get_ftop(), i );
}


/* Given i, generate an expression yielding 
  is_full(i) ? ST(i) : NaN
*/

static IRExpr* get_ST ( Int i )
{
   return
      IRExpr_Mux0X( get_ST_TAG(i),
                    /* 0 means empty */
                    mkQNaN64(),
                    /* non-0 means full */
                    get_ST_UNCHECKED(i));
}


/* Adjust FTOP downwards by one register. */

static void fp_push ( void )
{
   put_ftop( binop(Iop_Sub32, get_ftop(), mkU32(1)) );
}

/* Adjust FTOP upwards by one register, and mark the vacated register
   as empty.  */

static void fp_pop ( void )
{
   put_ST_TAG(0, mkU8(0));
   put_ftop( binop(Iop_Add32, get_ftop(), mkU32(1)) );
}

//.. /* Clear the C2 bit of the FPU status register, for
//..    sin/cos/tan/sincos. */
//.. 
//.. static void clear_C2 ( void )
//.. {
//..    put_C3210( binop(Iop_And32, get_C3210(), mkU32(~X86G_FC_MASK_C2)) );
//.. }
//.. 
//.. 
//.. /* ------------------------------------------------------- */
//.. /* Given all that stack-mangling junk, we can now go ahead
//..    and describe FP instructions. 
//.. */
//.. 
//.. /* ST(0) = ST(0) `op` mem64/32(addr)
//..    Need to check ST(0)'s tag on read, but not on write.
//.. */
//.. static
//.. void fp_do_op_mem_ST_0 ( IRTemp addr, UChar* op_txt, UChar* dis_buf, 
//..                          IROp op, Bool dbl )
//.. {
//..    DIP("f%s%c %s\n", op_txt, dbl?'l':'s', dis_buf);
//..    if (dbl) {
//..       put_ST_UNCHECKED(0, 
//..          binop( op, 
//..                 get_ST(0), 
//..                 loadLE(Ity_F64,mkexpr(addr))
//..          ));
//..    } else {
//..       put_ST_UNCHECKED(0, 
//..          binop( op, 
//..                 get_ST(0), 
//..                 unop(Iop_F32toF64, loadLE(Ity_F32,mkexpr(addr)))
//..          ));
//..    }
//.. }


/* ST(0) = mem64/32(addr) `op` ST(0)
   Need to check ST(0)'s tag on read, but not on write.
*/
static
void fp_do_oprev_mem_ST_0 ( IRTemp addr, HChar* op_txt, HChar* dis_buf, 
                            IROp op, Bool dbl )
{
   DIP("f%s%c %s\n", op_txt, dbl?'l':'s', dis_buf);
   if (dbl) {
      put_ST_UNCHECKED(0, 
         binop( op, 
                loadLE(Ity_F64,mkexpr(addr)),
                get_ST(0)
         ));
   } else {
      put_ST_UNCHECKED(0, 
         binop( op, 
                unop(Iop_F32toF64, loadLE(Ity_F32,mkexpr(addr))),
                get_ST(0)
         ));
   }
}


/* ST(dst) = ST(dst) `op` ST(src).
   Check dst and src tags when reading but not on write.
*/
static
void fp_do_op_ST_ST ( HChar* op_txt, IROp op, UInt st_src, UInt st_dst,
                      Bool pop_after )
{
   DIP("f%s%s st(%u), st(%u)\n", op_txt, pop_after?"p":"", st_src, st_dst );
   put_ST_UNCHECKED( 
      st_dst, 
      binop(op, get_ST(st_dst), get_ST(st_src) ) 
   );
   if (pop_after)
      fp_pop();
}

/* ST(dst) = ST(src) `op` ST(dst).
   Check dst and src tags when reading but not on write.
*/
static
void fp_do_oprev_ST_ST ( HChar* op_txt, IROp op, UInt st_src, UInt st_dst,
                         Bool pop_after )
{
   DIP("f%s%s st(%u), st(%u)\n", op_txt, pop_after?"p":"", st_src, st_dst );
   put_ST_UNCHECKED( 
      st_dst, 
      binop(op, get_ST(st_src), get_ST(st_dst) ) 
   );
   if (pop_after)
      fp_pop();
}

/* %rflags(Z,P,C) = UCOMI( st(0), st(i) ) */
static void fp_do_ucomi_ST0_STi ( UInt i, Bool pop_after )
{
   DIP("fucomi%s %%st(0),%%st(%u)\n", pop_after ? "p" : "", i);
   /* This is a bit of a hack (and isn't really right).  It sets
      Z,P,C,O correctly, but forces A and S to zero, whereas the Intel
      documentation implies A and S are unchanged. 
   */
   /* It's also fishy in that it is used both for COMIP and
      UCOMIP, and they aren't the same (although similar). */
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(AMD64G_CC_OP_COPY) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0) ));
   stmt( IRStmt_Put( 
            OFFB_CC_DEP1,
            binop( Iop_And64,
                   unop( Iop_32Uto64,
                         binop(Iop_CmpF64, get_ST(0), get_ST(i))),
                   mkU64(0x45)
        )));
   if (pop_after)
      fp_pop();
}


static
ULong dis_FPU ( /*OUT*/Bool* decode_ok, 
                Prefix pfx, ULong delta )
{
   Int    len;
   UInt   r_src, r_dst;
   HChar  dis_buf[50];
   IRTemp t1, t2;

   /* On entry, delta points at the second byte of the insn (the modrm
      byte).*/
   UChar first_opcode = getUChar(delta-1);
   UChar modrm        = getUChar(delta+0);

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xD8 opcodes +-+-+-+-+-+-+-+ */

   if (first_opcode == 0xD8) {
      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
           specifies an address. */
         IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;

         switch (gregLO3ofRM(modrm)) {

//..             case 0: /* FADD single-real */
//..                fp_do_op_mem_ST_0 ( addr, "add", dis_buf, Iop_AddF64, False );
//..                break;
//.. 
//..             case 1: /* FMUL single-real */
//..                fp_do_op_mem_ST_0 ( addr, "mul", dis_buf, Iop_MulF64, False );
//..                break;
//.. 
//..             case 2: /* FCOM single-real */
//..                DIP("fcoms %s\n", dis_buf);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, 
//..                                       get_ST(0),
//..                                       unop(Iop_F32toF64, 
//..                                            loadLE(Ity_F32,mkexpr(addr)))),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                break;  
//.. 
//..             case 3: /* FCOMP single-real */
//..                DIP("fcomps %s\n", dis_buf);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, 
//..                                       get_ST(0),
//..                                       unop(Iop_F32toF64, 
//..                                            loadLE(Ity_F32,mkexpr(addr)))),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                fp_pop();
//..                break;  
//.. 
//..             case 4: /* FSUB single-real */
//..                fp_do_op_mem_ST_0 ( addr, "sub", dis_buf, Iop_SubF64, False );
//..                break;

            case 5: /* FSUBR single-real */
               fp_do_oprev_mem_ST_0 ( addr, "subr", dis_buf, Iop_SubF64, False );
               break;

//..             case 6: /* FDIV single-real */
//..                fp_do_op_mem_ST_0 ( addr, "div", dis_buf, Iop_DivF64, False );
//..                break;
//.. 
//..             case 7: /* FDIVR single-real */
//..                fp_do_oprev_mem_ST_0 ( addr, "divr", dis_buf, Iop_DivF64, False );
//..                break;

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xD8\n");
               goto decode_fail;
         }
      } else {
         delta++;
         switch (modrm) {

            case 0xC0 ... 0xC7: /* FADD %st(?),%st(0) */
               fp_do_op_ST_ST ( "add", Iop_AddF64, modrm - 0xC0, 0, False );
               break;

            case 0xC8 ... 0xCF: /* FMUL %st(?),%st(0) */
               fp_do_op_ST_ST ( "mul", Iop_MulF64, modrm - 0xC8, 0, False );
               break;

//.. #if 1
//..             /* Dunno if this is right */
//..             case 0xD0 ... 0xD7: /* FCOM %st(?),%st(0) */
//..                r_dst = (UInt)modrm - 0xD0;
//..                DIP("fcom %%st(0),%%st(%d)\n", r_dst);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, get_ST(0), get_ST(r_dst)),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                break;
//.. #endif
//.. #if 1
//..             /* Dunno if this is right */
//..             case 0xD8 ... 0xDF: /* FCOMP %st(?),%st(0) */
//..                r_dst = (UInt)modrm - 0xD8;
//..                DIP("fcomp %%st(0),%%st(%d)\n", r_dst);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, get_ST(0), get_ST(r_dst)),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                fp_pop();
//..                break;
//.. #endif
            case 0xE0 ... 0xE7: /* FSUB %st(?),%st(0) */
               fp_do_op_ST_ST ( "sub", Iop_SubF64, modrm - 0xE0, 0, False );
               break;

//..             case 0xE8 ... 0xEF: /* FSUBR %st(?),%st(0) */
//..                fp_do_oprev_ST_ST ( "subr", Iop_SubF64, modrm - 0xE8, 0, False );
//..                break;

            case 0xF0 ... 0xF7: /* FDIV %st(?),%st(0) */
               fp_do_op_ST_ST ( "div", Iop_DivF64, modrm - 0xF0, 0, False );
               break;

//..             case 0xF8 ... 0xFF: /* FDIVR %st(?),%st(0) */
//..                fp_do_oprev_ST_ST ( "divr", Iop_DivF64, modrm - 0xF8, 0, False );
//..                break;

            default:
               goto decode_fail;
         }
      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xD9 opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xD9) {
      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
            specifies an address. */
         IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;

         switch (gregLO3ofRM(modrm)) {

            case 0: /* FLD single-real */
               DIP("flds %s\n", dis_buf);
               fp_push();
               put_ST(0, unop(Iop_F32toF64,
                              loadLE(Ity_F32, mkexpr(addr))));
               break;

            case 2: /* FST single-real */
               DIP("fsts %s\n", dis_buf);
               storeLE(mkexpr(addr),
                       binop(Iop_F64toF32, get_roundingmode(), get_ST(0)));
               break;

            case 3: /* FSTP single-real */
               DIP("fstps %s\n", dis_buf);
               storeLE(mkexpr(addr), 
                       binop(Iop_F64toF32, get_roundingmode(), get_ST(0)));
               fp_pop();
               break;

//..             case 4: { /* FLDENV m108 */
//..                /* Uses dirty helper: 
//..                      VexEmWarn x86g_do_FLDENV ( VexGuestX86State*, Addr32 ) */
//..                IRTemp   ew = newTemp(Ity_I32);
//..                IRDirty* d  = unsafeIRDirty_0_N ( 
//..                                 0/*regparms*/, 
//..                                 "x86g_dirtyhelper_FLDENV", 
//..                                 &x86g_dirtyhelper_FLDENV,
//..                                 mkIRExprVec_1( mkexpr(addr) )
//..                              );
//..                d->needsBBP = True;
//..                d->tmp      = ew;
//..                /* declare we're reading memory */
//..                d->mFx   = Ifx_Read;
//..                d->mAddr = mkexpr(addr);
//..                d->mSize = 28;
//.. 
//..                /* declare we're writing guest state */
//..                d->nFxState = 5;
//.. 
//..                d->fxState[0].fx     = Ifx_Write;
//..                d->fxState[0].offset = OFFB_FTOP;
//..                d->fxState[0].size   = sizeof(UInt);
//.. 
//..                d->fxState[1].fx     = Ifx_Write;
//..                d->fxState[1].offset = OFFB_FPREGS;
//..                d->fxState[1].size   = 8 * sizeof(ULong);
//.. 
//..                d->fxState[2].fx     = Ifx_Write;
//..                d->fxState[2].offset = OFFB_FPTAGS;
//..                d->fxState[2].size   = 8 * sizeof(UChar);
//.. 
//..                d->fxState[3].fx     = Ifx_Write;
//..                d->fxState[3].offset = OFFB_FPROUND;
//..                d->fxState[3].size   = sizeof(UInt);
//.. 
//..                d->fxState[4].fx     = Ifx_Write;
//..                d->fxState[4].offset = OFFB_FC3210;
//..                d->fxState[4].size   = sizeof(UInt);
//.. 
//..                stmt( IRStmt_Dirty(d) );
//.. 
//..                /* ew contains any emulation warning we may need to
//..                   issue.  If needed, side-exit to the next insn,
//..                   reporting the warning, so that Valgrind's dispatcher
//..                   sees the warning. */
//..                put_emwarn( mkexpr(ew) );
//..                stmt( 
//..                   IRStmt_Exit(
//..                      binop(Iop_CmpNE32, mkexpr(ew), mkU32(0)),
//..                      Ijk_EmWarn,
//..                      IRConst_U32( ((Addr32)guest_eip_bbstart)+delta)
//..                   )
//..                );
//.. 
//..                DIP("fldenv %s\n", dis_buf);
//..                break;
//..             }
//.. 
//..             case 5: {/* FLDCW */
//..                /* The only thing we observe in the control word is the
//..                   rounding mode.  Therefore, pass the 16-bit value
//..                   (x87 native-format control word) to a clean helper,
//..                   getting back a 64-bit value, the lower half of which
//..                   is the FPROUND value to store, and the upper half of
//..                   which is the emulation-warning token which may be
//..                   generated.
//..                */
//..                /* ULong x86h_check_fldcw ( UInt ); */
//..                IRTemp t64 = newTemp(Ity_I64);
//..                IRTemp ew = newTemp(Ity_I32);
//..                DIP("fldcw %s\n", dis_buf);
//..                assign( t64, mkIRExprCCall(
//..                                Ity_I64, 0/*regparms*/, 
//..                                "x86g_check_fldcw",
//..                                &x86g_check_fldcw, 
//..                                mkIRExprVec_1( 
//..                                   unop( Iop_16Uto32, 
//..                                         loadLE(Ity_I16, mkexpr(addr)))
//..                                )
//..                             )
//..                      );
//.. 
//..                put_fpround( unop(Iop_64to32, mkexpr(t64)) );
//..                assign( ew, unop(Iop_64HIto32, mkexpr(t64) ) );
//..                put_emwarn( mkexpr(ew) );
//..                /* Finally, if an emulation warning was reported,
//..                   side-exit to the next insn, reporting the warning,
//..                   so that Valgrind's dispatcher sees the warning. */
//..                stmt( 
//..                   IRStmt_Exit(
//..                      binop(Iop_CmpNE32, mkexpr(ew), mkU32(0)),
//..                      Ijk_EmWarn,
//..                      IRConst_U32( ((Addr32)guest_eip_bbstart)+delta)
//..                   )
//..                );
//..                break;
//..             }
//.. 
//..             case 6: { /* FNSTENV m28 */
//..                /* Uses dirty helper: 
//..                      void x86g_do_FSTENV ( VexGuestX86State*, UInt ) */
//..                IRDirty* d = unsafeIRDirty_0_N ( 
//..                                0/*regparms*/, 
//..                                "x86g_dirtyhelper_FSTENV", 
//..                                &x86g_dirtyhelper_FSTENV,
//..                                mkIRExprVec_1( mkexpr(addr) )
//..                             );
//..                d->needsBBP = True;
//..                /* declare we're writing memory */
//..                d->mFx   = Ifx_Write;
//..                d->mAddr = mkexpr(addr);
//..                d->mSize = 28;
//.. 
//..                /* declare we're reading guest state */
//..                d->nFxState = 4;
//.. 
//..                d->fxState[0].fx     = Ifx_Read;
//..                d->fxState[0].offset = OFFB_FTOP;
//..                d->fxState[0].size   = sizeof(UInt);
//.. 
//..                d->fxState[1].fx     = Ifx_Read;
//..                d->fxState[1].offset = OFFB_FPTAGS;
//..                d->fxState[1].size   = 8 * sizeof(UChar);
//.. 
//..                d->fxState[2].fx     = Ifx_Read;
//..                d->fxState[2].offset = OFFB_FPROUND;
//..                d->fxState[2].size   = sizeof(UInt);
//.. 
//..                d->fxState[3].fx     = Ifx_Read;
//..                d->fxState[3].offset = OFFB_FC3210;
//..                d->fxState[3].size   = sizeof(UInt);
//.. 
//..                stmt( IRStmt_Dirty(d) );
//.. 
//..                DIP("fnstenv %s\n", dis_buf);
//..                break;
//..             }
//.. 
//..             case 7: /* FNSTCW */
//..               /* Fake up a native x87 FPU control word.  The only
//..                  thing it depends on is FPROUND[1:0], so call a clean
//..                  helper to cook it up. */
//..                /* UInt x86h_create_fpucw ( UInt fpround ) */
//..                DIP("fnstcw %s\n", dis_buf);
//..                storeLE(
//..                   mkexpr(addr), 
//..                   unop( Iop_32to16, 
//..                         mkIRExprCCall(
//..                            Ity_I32, 0/*regp*/,
//..                            "x86g_create_fpucw", &x86g_create_fpucw, 
//..                            mkIRExprVec_1( get_fpround() ) 
//..                         ) 
//..                   ) 
//..                );
//..                break;

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xD9\n");
               goto decode_fail;
         }

      } else {
         delta++;
         switch (modrm) {

            case 0xC0 ... 0xC7: /* FLD %st(?) */
               r_src = (UInt)modrm - 0xC0;
               DIP("fld %%st(%u)\n", r_src);
               t1 = newTemp(Ity_F64);
               assign(t1, get_ST(r_src));
               fp_push();
               put_ST(0, mkexpr(t1));
               break;

            case 0xC8 ... 0xCF: /* FXCH %st(?) */
               r_src = (UInt)modrm - 0xC8;
               DIP("fxch %%st(%u)\n", r_src);
               t1 = newTemp(Ity_F64);
               t2 = newTemp(Ity_F64);
               assign(t1, get_ST(0));
               assign(t2, get_ST(r_src));
               put_ST_UNCHECKED(0, mkexpr(t2));
               put_ST_UNCHECKED(r_src, mkexpr(t1));
               break;

            case 0xE0: /* FCHS */
               DIP("fchs\n");
               put_ST_UNCHECKED(0, unop(Iop_NegF64, get_ST(0)));
               break;

            case 0xE1: /* FABS */
               DIP("fabs\n");
               put_ST_UNCHECKED(0, unop(Iop_AbsF64, get_ST(0)));
               break;

//..             case 0xE5: { /* FXAM */
//..                /* This is an interesting one.  It examines %st(0),
//..                   regardless of whether the tag says it's empty or not.
//..                   Here, just pass both the tag (in our format) and the
//..                   value (as a double, actually a ULong) to a helper
//..                   function. */
//..                IRExpr** args
//..                   = mkIRExprVec_2( unop(Iop_8Uto32, get_ST_TAG(0)),
//..                                    unop(Iop_ReinterpF64asI64, 
//..                                         get_ST_UNCHECKED(0)) );
//..                put_C3210(mkIRExprCCall(
//..                             Ity_I32, 
//..                             0/*regparm*/, 
//..                             "x86g_calculate_FXAM", &x86g_calculate_FXAM,
//..                             args
//..                         ));
//..                DIP("fxam\n");
//..                break;
//..             }

            case 0xE8: /* FLD1 */
               DIP("fld1\n");
               fp_push();
               /* put_ST(0, IRExpr_Const(IRConst_F64(1.0))); */
               put_ST(0, IRExpr_Const(IRConst_F64i(0x3ff0000000000000ULL)));
               break;

//..             case 0xE9: /* FLDL2T */
//..                DIP("fldl2t\n");
//..                fp_push();
//..                /* put_ST(0, IRExpr_Const(IRConst_F64(3.32192809488736234781))); */
//..                put_ST(0, IRExpr_Const(IRConst_F64i(0x400a934f0979a371ULL)));
//..                break;
//.. 
//..             case 0xEA: /* FLDL2E */
//..                DIP("fldl2e\n");
//..                fp_push();
//..                /* put_ST(0, IRExpr_Const(IRConst_F64(1.44269504088896340739))); */
//..                put_ST(0, IRExpr_Const(IRConst_F64i(0x3ff71547652b82feULL)));
//..                break;
//.. 
//..             case 0xEB: /* FLDPI */
//..                DIP("fldpi\n");
//..                fp_push();
//..                /* put_ST(0, IRExpr_Const(IRConst_F64(3.14159265358979323851))); */
//..                put_ST(0, IRExpr_Const(IRConst_F64i(0x400921fb54442d18ULL)));
//..                break;
//.. 
//..             case 0xEC: /* FLDLG2 */
//..                DIP("fldlg2\n");
//..                fp_push();
//..                /* put_ST(0, IRExpr_Const(IRConst_F64(0.301029995663981143))); */
//..                put_ST(0, IRExpr_Const(IRConst_F64i(0x3fd34413509f79ffULL)));
//..                break;
//.. 
//..             case 0xED: /* FLDLN2 */
//..                DIP("fldln2\n");
//..                fp_push();
//..                /* put_ST(0, IRExpr_Const(IRConst_F64(0.69314718055994530942))); */
//..                put_ST(0, IRExpr_Const(IRConst_F64i(0x3fe62e42fefa39efULL)));
//..                break;

            case 0xEE: /* FLDZ */
               DIP("fldz\n");
               fp_push();
               /* put_ST(0, IRExpr_Const(IRConst_F64(0.0))); */
               put_ST(0, IRExpr_Const(IRConst_F64i(0x0000000000000000ULL)));
               break;

//..             case 0xF0: /* F2XM1 */
//..                DIP("f2xm1\n");
//..                put_ST_UNCHECKED(0, unop(Iop_2xm1F64, get_ST(0)));
//..                break;
//.. 
//..             case 0xF1: /* FYL2X */
//..                DIP("fyl2x\n");
//..                put_ST_UNCHECKED(1, binop(Iop_Yl2xF64,
//..                                          get_ST(1), get_ST(0)));
//..                fp_pop();
//..                break;
//.. 
//..             case 0xF2: /* FPTAN */
//..                DIP("ftan\n");
//..                put_ST_UNCHECKED(0, unop(Iop_TanF64, get_ST(0)));
//..                fp_push();
//..                put_ST(0, IRExpr_Const(IRConst_F64(1.0)));
//..                clear_C2(); /* HACK */
//..                break;
//.. 
//..             case 0xF3: /* FPATAN */
//..                DIP("fpatan\n");
//..                put_ST_UNCHECKED(1, binop(Iop_AtanF64,
//..                                          get_ST(1), get_ST(0)));
//..                fp_pop();
//..                break;
//.. 
//..             case 0xF5: { /* FPREM1 -- IEEE compliant */
//..                IRTemp a1 = newTemp(Ity_F64);
//..                IRTemp a2 = newTemp(Ity_F64);
//..                DIP("fprem1\n");
//..                /* Do FPREM1 twice, once to get the remainder, and once
//..                   to get the C3210 flag values. */
//..                assign( a1, get_ST(0) );
//..                assign( a2, get_ST(1) );
//..                put_ST_UNCHECKED(0, binop(Iop_PRem1F64,
//..                                          mkexpr(a1), mkexpr(a2)));
//..                put_C3210( binop(Iop_PRem1C3210F64, mkexpr(a1), mkexpr(a2)) );
//..                break;
//..             }
//.. 
//..             case 0xF7: /* FINCSTP */
//..                DIP("fprem\n");
//..                put_ftop( binop(Iop_Add32, get_ftop(), mkU32(1)) );
//..                break;
//.. 
//..             case 0xF8: { /* FPREM -- not IEEE compliant */
//..                IRTemp a1 = newTemp(Ity_F64);
//..                IRTemp a2 = newTemp(Ity_F64);
//..                DIP("fprem\n");
//..                /* Do FPREM twice, once to get the remainder, and once
//..                   to get the C3210 flag values. */
//..                assign( a1, get_ST(0) );
//..                assign( a2, get_ST(1) );
//..                put_ST_UNCHECKED(0, binop(Iop_PRemF64,
//..                                          mkexpr(a1), mkexpr(a2)));
//..                put_C3210( binop(Iop_PRemC3210F64, mkexpr(a1), mkexpr(a2)) );
//..                break;
//..             }
//.. 
//..             case 0xF9: /* FYL2XP1 */
//..                DIP("fyl2xp1\n");
//..                put_ST_UNCHECKED(1, binop(Iop_Yl2xp1F64,
//..                                          get_ST(1), get_ST(0)));
//..                fp_pop();
//..                break;
//.. 
//..             case 0xFA: /* FSQRT */
//..                DIP("fsqrt\n");
//..                put_ST_UNCHECKED(0, unop(Iop_SqrtF64, get_ST(0)));
//..                break;
//.. 
//..             case 0xFB: { /* FSINCOS */
//..                IRTemp a1 = newTemp(Ity_F64);
//..                assign( a1, get_ST(0) );
//..                DIP("fsincos\n");
//..                put_ST_UNCHECKED(0, unop(Iop_SinF64, mkexpr(a1)));
//..                fp_push();
//..                put_ST(0, unop(Iop_CosF64, mkexpr(a1)));
//..                clear_C2(); /* HACK */
//..                break;
//..             }
//.. 
//..             case 0xFC: /* FRNDINT */
//..                DIP("frndint\n");
//..                put_ST_UNCHECKED(0,
//..                   binop(Iop_RoundF64, get_roundingmode(), get_ST(0)) );
//..                break;
//.. 
//..             case 0xFD: /* FSCALE */
//..                DIP("fscale\n");
//..                put_ST_UNCHECKED(0, binop(Iop_ScaleF64,
//..                                          get_ST(0), get_ST(1)));
//..                break;
//.. 
//..             case 0xFE: /* FSIN */
//..                DIP("fsin\n");
//..                put_ST_UNCHECKED(0, unop(Iop_SinF64, get_ST(0)));
//..                clear_C2(); /* HACK */
//..                break;
//.. 
//..             case 0xFF: /* FCOS */
//..                DIP("fcos\n");
//..                put_ST_UNCHECKED(0, unop(Iop_CosF64, get_ST(0)));
//..                clear_C2(); /* HACK */
//..                break;

            default:
               goto decode_fail;
         }
      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xDA opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xDA) {

      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
            specifies an address. */
         //IROp   fop;
         //IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;
         switch (gregLO3ofRM(modrm)) {

//..             case 0: /* FIADD m32int */ /* ST(0) += m32int */
//..                DIP("fiaddl %s\n", dis_buf);
//..                fop = Iop_AddF64;
//..                goto do_fop_m32;
//.. 
//..             case 1: /* FIMUL m32int */ /* ST(0) *= m32int */
//..                DIP("fimull %s\n", dis_buf);
//..                fop = Iop_MulF64;
//..                goto do_fop_m32;
//.. 
//..             case 4: /* FISUB m32int */ /* ST(0) -= m32int */
//..                DIP("fisubl %s\n", dis_buf);
//..                fop = Iop_SubF64;
//..                goto do_fop_m32;
//.. 
//..             case 5: /* FISUBR m32int */ /* ST(0) = m32int - ST(0) */
//..                DIP("fisubrl %s\n", dis_buf);
//..                fop = Iop_SubF64;
//..                goto do_foprev_m32;
//.. 
//..             case 6: /* FIDIV m32int */ /* ST(0) /= m32int */
//..                DIP("fisubl %s\n", dis_buf);
//..                fop = Iop_DivF64;
//..                goto do_fop_m32;
//.. 
//..             case 7: /* FIDIVR m32int */ /* ST(0) = m32int / ST(0) */
//..                DIP("fidivrl %s\n", dis_buf);
//..                fop = Iop_DivF64;
//..                goto do_foprev_m32;
//.. 
//..             do_fop_m32:
//..                put_ST_UNCHECKED(0, 
//..                   binop(fop, 
//..                         get_ST(0),
//..                         unop(Iop_I32toF64,
//..                              loadLE(Ity_I32, mkexpr(addr)))));
//..                break;
//.. 
//..             do_foprev_m32:
//..                put_ST_UNCHECKED(0, 
//..                   binop(fop, 
//..                         unop(Iop_I32toF64,
//..                              loadLE(Ity_I32, mkexpr(addr))),
//..                         get_ST(0)));
//..                break;

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xDA\n");
               goto decode_fail;
         }

      } else {

         delta++;
         switch (modrm) {

//..             case 0xC0 ... 0xC7: /* FCMOVB ST(i), ST(0) */
//..                r_src = (UInt)modrm - 0xC0;
//..                DIP("fcmovb %%st(%d), %%st(0)\n", r_src);
//..                put_ST_UNCHECKED(0, 
//..                                 IRExpr_Mux0X( 
//..                                     unop(Iop_1Uto8,
//..                                          mk_x86g_calculate_condition(X86CondB)), 
//..                                     get_ST(0), get_ST(r_src)) );
//..                break;

            case 0xC8 ... 0xCF: /* FCMOVE(Z) ST(i), ST(0) */
               r_src = (UInt)modrm - 0xC8;
               DIP("fcmovz %%st(%u), %%st(0)\n", r_src);
               put_ST_UNCHECKED(0, 
                                IRExpr_Mux0X( 
                                    unop(Iop_1Uto8,
                                         mk_amd64g_calculate_condition(AMD64CondZ)), 
                                    get_ST(0), get_ST(r_src)) );
               break;

            case 0xD0 ... 0xD7: /* FCMOVBE ST(i), ST(0) */
               r_src = (UInt)modrm - 0xD0;
               DIP("fcmovbe %%st(%u), %%st(0)\n", r_src);
               put_ST_UNCHECKED(0, 
                                IRExpr_Mux0X( 
                                    unop(Iop_1Uto8,
                                         mk_amd64g_calculate_condition(AMD64CondBE)), 
                                    get_ST(0), get_ST(r_src)) );
               break;

//..             case 0xE9: /* FUCOMPP %st(0),%st(1) */
//..                DIP("fucompp %%st(0),%%st(1)\n");
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, get_ST(0), get_ST(1)),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                fp_pop();
//..                fp_pop();
//..                break;

            default:
               goto decode_fail;
         }

      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xDB opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xDB) {
      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
            specifies an address. */
         IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;

         switch (gregLO3ofRM(modrm)) {

            case 0: /* FILD m32int */
               DIP("fildl %s\n", dis_buf);
               fp_push();
               put_ST(0, unop(Iop_I32toF64,
                              loadLE(Ity_I32, mkexpr(addr))));
               break;

//..             case 2: /* FIST m32 */
//..                DIP("fistl %s\n", dis_buf);
//..                storeLE( mkexpr(addr), 
//..                         binop(Iop_F64toI32, get_roundingmode(), get_ST(0)) );
//..                break;

            case 3: /* FISTP m32 */
               DIP("fistpl %s\n", dis_buf);
               storeLE( mkexpr(addr), 
                        binop(Iop_F64toI32, get_roundingmode(), get_ST(0)) );
               fp_pop();
               break;

            case 5: { /* FLD extended-real */
               /* Uses dirty helper: 
                     ULong amd64g_loadF80le ( ULong )
                  addr holds the address.  First, do a dirty call to
                  get hold of the data. */
               IRTemp   val  = newTemp(Ity_I64);
               IRExpr** args = mkIRExprVec_1 ( mkexpr(addr) );

               IRDirty* d = unsafeIRDirty_1_N ( 
                               val, 
                               0/*regparms*/, 
                               "amd64g_loadF80le", &amd64g_loadF80le, 
                               args 
                            );
               /* declare that we're reading memory */
               d->mFx   = Ifx_Read;
               d->mAddr = mkexpr(addr);
               d->mSize = 10;

               /* execute the dirty call, dumping the result in val. */
               stmt( IRStmt_Dirty(d) );
               fp_push();
               put_ST(0, unop(Iop_ReinterpI64asF64, mkexpr(val)));

               DIP("fldt %s\n", dis_buf);
               break;
            }

            case 7: { /* FSTP extended-real */
               /* Uses dirty helper: 
                     void amd64g_storeF80le ( ULong addr, ULong data ) 
               */
               IRExpr** args 
                  = mkIRExprVec_2( mkexpr(addr), 
                                   unop(Iop_ReinterpF64asI64, get_ST(0)) );

               IRDirty* d = unsafeIRDirty_0_N ( 
                               0/*regparms*/, 
                               "amd64g_storeF80le", &amd64g_storeF80le,
                               args 
                            );
               /* declare we're writing memory */
               d->mFx   = Ifx_Write;
               d->mAddr = mkexpr(addr);
               d->mSize = 10;

               /* execute the dirty call. */
               stmt( IRStmt_Dirty(d) );
               fp_pop();

               DIP("fstpt\n %s", dis_buf);
               break;
            }

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xDB\n");
               goto decode_fail;
         }

      } else {

         delta++;
         switch (modrm) {

//..             case 0xC0 ... 0xC7: /* FCMOVNB ST(i), ST(0) */
//..                r_src = (UInt)modrm - 0xC0;
//..                DIP("fcmovnb %%st(%d), %%st(0)\n", r_src);
//..                put_ST_UNCHECKED(0, 
//..                                 IRExpr_Mux0X( 
//..                                     unop(Iop_1Uto8,
//..                                          mk_x86g_calculate_condition(X86CondNB)), 
//..                                     get_ST(0), get_ST(r_src)) );
//..                break;

            case 0xC8 ... 0xCF: /* FCMOVNE(NZ) ST(i), ST(0) */
               r_src = (UInt)modrm - 0xC8;
               DIP("fcmovnz %%st(%u), %%st(0)\n", r_src);
               put_ST_UNCHECKED(
                  0, 
                  IRExpr_Mux0X( 
                     unop(Iop_1Uto8,
                          mk_amd64g_calculate_condition(AMD64CondNZ)), 
                     get_ST(0), 
                     get_ST(r_src)
                  )
               );
               break;

            case 0xD0 ... 0xD7: /* FCMOVNBE ST(i), ST(0) */
               r_src = (UInt)modrm - 0xD0;
               DIP("fcmovnbe %%st(%u), %%st(0)\n", r_src);
               put_ST_UNCHECKED(
                  0, 
                  IRExpr_Mux0X( 
                     unop(Iop_1Uto8,
                          mk_amd64g_calculate_condition(AMD64CondNBE)), 
                     get_ST(0), 
                     get_ST(r_src)
                  ) 
               );
               break;

//..             case 0xE2:
//..                DIP("fnclex\n");
//..                break;
//.. 
//..             case 0xE3: {
//..                /* Uses dirty helper: 
//..                      void x86g_do_FINIT ( VexGuestX86State* ) */
//..                IRDirty* d  = unsafeIRDirty_0_N ( 
//..                                 0/*regparms*/, 
//..                                 "x86g_dirtyhelper_FINIT", 
//..                                 &x86g_dirtyhelper_FINIT,
//..                                 mkIRExprVec_0()
//..                              );
//..                d->needsBBP = True;
//.. 
//..                /* declare we're writing guest state */
//..                d->nFxState = 5;
//.. 
//..                d->fxState[0].fx     = Ifx_Write;
//..                d->fxState[0].offset = OFFB_FTOP;
//..                d->fxState[0].size   = sizeof(UInt);
//.. 
//..                d->fxState[1].fx     = Ifx_Write;
//..                d->fxState[1].offset = OFFB_FPREGS;
//..                d->fxState[1].size   = 8 * sizeof(ULong);
//.. 
//..                d->fxState[2].fx     = Ifx_Write;
//..                d->fxState[2].offset = OFFB_FPTAGS;
//..                d->fxState[2].size   = 8 * sizeof(UChar);
//.. 
//..                d->fxState[3].fx     = Ifx_Write;
//..                d->fxState[3].offset = OFFB_FPROUND;
//..                d->fxState[3].size   = sizeof(UInt);
//.. 
//..                d->fxState[4].fx     = Ifx_Write;
//..                d->fxState[4].offset = OFFB_FC3210;
//..                d->fxState[4].size   = sizeof(UInt);
//.. 
//..                stmt( IRStmt_Dirty(d) );
//.. 
//..                DIP("fninit\n");
//..                break;
//..             }

            case 0xE8 ... 0xEF: /* FUCOMI %st(0),%st(?) */
               fp_do_ucomi_ST0_STi( (UInt)modrm - 0xE8, False );
               break;

//..             case 0xF0 ... 0xF7: /* FCOMI %st(0),%st(?) */
//..                fp_do_ucomi_ST0_STi( (UInt)modrm - 0xF0, False );
//..                break;

            default:
               goto decode_fail;
         }
      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xDC opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xDC) {
      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
            specifies an address. */
         IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;

         switch (gregLO3ofRM(modrm)) {

//..             case 0: /* FADD double-real */
//..                fp_do_op_mem_ST_0 ( addr, "add", dis_buf, Iop_AddF64, True );
//..                break;
//.. 
//..             case 1: /* FMUL double-real */
//..                fp_do_op_mem_ST_0 ( addr, "mul", dis_buf, Iop_MulF64, True );
//..                break;
//.. 
//..             case 2: /* FCOM double-real */
//..                DIP("fcoml %s\n", dis_buf);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, 
//..                                       get_ST(0),
//..                                       loadLE(Ity_F64,mkexpr(addr))),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                break;  
//.. 
//..             case 3: /* FCOMP double-real */
//..                DIP("fcompl %s\n", dis_buf);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, 
//..                                       get_ST(0),
//..                                       loadLE(Ity_F64,mkexpr(addr))),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                fp_pop();
//..                break;  
//.. 
//..             case 4: /* FSUB double-real */
//..                fp_do_op_mem_ST_0 ( addr, "sub", dis_buf, Iop_SubF64, True );
//..                break;

            case 5: /* FSUBR double-real */
               fp_do_oprev_mem_ST_0 ( addr, "subr", dis_buf, Iop_SubF64, True );
               break;

//..             case 6: /* FDIV double-real */
//..                fp_do_op_mem_ST_0 ( addr, "div", dis_buf, Iop_DivF64, True );
//..                break;
//.. 
//..             case 7: /* FDIVR double-real */
//..                fp_do_oprev_mem_ST_0 ( addr, "divr", dis_buf, Iop_DivF64, True );
//..                break;

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xDC\n");
               goto decode_fail;
         }

      } else {

         delta++;
         switch (modrm) {

            case 0xC0 ... 0xC7: /* FADD %st(0),%st(?) */
               fp_do_op_ST_ST ( "add", Iop_AddF64, 0, modrm - 0xC0, False );
               break;

            case 0xC8 ... 0xCF: /* FMUL %st(0),%st(?) */
               fp_do_op_ST_ST ( "mul", Iop_MulF64, 0, modrm - 0xC8, False );
               break;

            case 0xE0 ... 0xE7: /* FSUBR %st(0),%st(?) */
               fp_do_oprev_ST_ST ( "subr", Iop_SubF64, 0, modrm - 0xE0, False );
               break;

//..             case 0xE8 ... 0xEF: /* FSUB %st(0),%st(?) */
//..                fp_do_op_ST_ST ( "sub", Iop_SubF64, 0, modrm - 0xE8, False );
//..                break;
//.. 
//..             case 0xF0 ... 0xF7: /* FDIVR %st(0),%st(?) */
//..                fp_do_oprev_ST_ST ( "divr", Iop_DivF64, 0, modrm - 0xF0, False );
//..                break;

            case 0xF8 ... 0xFF: /* FDIV %st(0),%st(?) */
               fp_do_op_ST_ST ( "div", Iop_DivF64, 0, modrm - 0xF8, False );
               break;

            default:
               goto decode_fail;
         }

      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xDD opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xDD) {

      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
            specifies an address. */
         IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;

         switch (gregLO3ofRM(modrm)) {

            case 0: /* FLD double-real */
               DIP("fldl %s\n", dis_buf);
               fp_push();
               put_ST(0, IRExpr_LDle(Ity_F64, mkexpr(addr)));
               break;

            case 2: /* FST double-real */
               DIP("fstl %s\n", dis_buf);
               storeLE(mkexpr(addr), get_ST(0));
               break;

            case 3: /* FSTP double-real */
               DIP("fstpl %s\n", dis_buf);
               storeLE(mkexpr(addr), get_ST(0));
               fp_pop();
               break;

//..             case 4: { /* FRSTOR m108 */
//..                /* Uses dirty helper: 
//..                      VexEmWarn x86g_do_FRSTOR ( VexGuestX86State*, Addr32 ) */
//..                IRTemp   ew = newTemp(Ity_I32);
//..                IRDirty* d  = unsafeIRDirty_0_N ( 
//..                                 0/*regparms*/, 
//..                                 "x86g_dirtyhelper_FRSTOR", 
//..                                 &x86g_dirtyhelper_FRSTOR,
//..                                 mkIRExprVec_1( mkexpr(addr) )
//..                              );
//..                d->needsBBP = True;
//..                d->tmp      = ew;
//..                /* declare we're reading memory */
//..                d->mFx   = Ifx_Read;
//..                d->mAddr = mkexpr(addr);
//..                d->mSize = 108;
//.. 
//..                /* declare we're writing guest state */
//..                d->nFxState = 5;
//.. 
//..                d->fxState[0].fx     = Ifx_Write;
//..                d->fxState[0].offset = OFFB_FTOP;
//..                d->fxState[0].size   = sizeof(UInt);
//.. 
//..                d->fxState[1].fx     = Ifx_Write;
//..                d->fxState[1].offset = OFFB_FPREGS;
//..                d->fxState[1].size   = 8 * sizeof(ULong);
//.. 
//..                d->fxState[2].fx     = Ifx_Write;
//..                d->fxState[2].offset = OFFB_FPTAGS;
//..                d->fxState[2].size   = 8 * sizeof(UChar);
//.. 
//..                d->fxState[3].fx     = Ifx_Write;
//..                d->fxState[3].offset = OFFB_FPROUND;
//..                d->fxState[3].size   = sizeof(UInt);
//.. 
//..                d->fxState[4].fx     = Ifx_Write;
//..                d->fxState[4].offset = OFFB_FC3210;
//..                d->fxState[4].size   = sizeof(UInt);
//.. 
//..                stmt( IRStmt_Dirty(d) );
//.. 
//..                /* ew contains any emulation warning we may need to
//..                   issue.  If needed, side-exit to the next insn,
//..                   reporting the warning, so that Valgrind's dispatcher
//..                   sees the warning. */
//..                put_emwarn( mkexpr(ew) );
//..                stmt( 
//..                   IRStmt_Exit(
//..                      binop(Iop_CmpNE32, mkexpr(ew), mkU32(0)),
//..                      Ijk_EmWarn,
//..                      IRConst_U32( ((Addr32)guest_eip_bbstart)+delta)
//..                   )
//..                );
//.. 
//..                DIP("frstor %s\n", dis_buf);
//..                break;
//..             }
//.. 
//..             case 6: { /* FNSAVE m108 */
//..                /* Uses dirty helper: 
//..                      void x86g_do_FSAVE ( VexGuestX86State*, UInt ) */
//..                IRDirty* d = unsafeIRDirty_0_N ( 
//..                                0/*regparms*/, 
//..                                "x86g_dirtyhelper_FSAVE", 
//..                                &x86g_dirtyhelper_FSAVE,
//..                                mkIRExprVec_1( mkexpr(addr) )
//..                             );
//..                d->needsBBP = True;
//..                /* declare we're writing memory */
//..                d->mFx   = Ifx_Write;
//..                d->mAddr = mkexpr(addr);
//..                d->mSize = 108;
//.. 
//..                /* declare we're reading guest state */
//..                d->nFxState = 5;
//.. 
//..                d->fxState[0].fx     = Ifx_Read;
//..                d->fxState[0].offset = OFFB_FTOP;
//..                d->fxState[0].size   = sizeof(UInt);
//.. 
//..                d->fxState[1].fx     = Ifx_Read;
//..                d->fxState[1].offset = OFFB_FPREGS;
//..                d->fxState[1].size   = 8 * sizeof(ULong);
//.. 
//..                d->fxState[2].fx     = Ifx_Read;
//..                d->fxState[2].offset = OFFB_FPTAGS;
//..                d->fxState[2].size   = 8 * sizeof(UChar);
//.. 
//..                d->fxState[3].fx     = Ifx_Read;
//..                d->fxState[3].offset = OFFB_FPROUND;
//..                d->fxState[3].size   = sizeof(UInt);
//.. 
//..                d->fxState[4].fx     = Ifx_Read;
//..                d->fxState[4].offset = OFFB_FC3210;
//..                d->fxState[4].size   = sizeof(UInt);
//.. 
//..                stmt( IRStmt_Dirty(d) );
//.. 
//..                DIP("fnsave %s\n", dis_buf);
//..                break;
//..             }

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xDD\n");
               goto decode_fail;
         }
      } else {
         delta++;
         switch (modrm) {

//..             case 0xD0 ... 0xD7: /* FST %st(0),%st(?) */
//..                r_dst = (UInt)modrm - 0xD0;
//..                DIP("fst %%st(0),%%st(%d)\n", r_dst);
//..                /* P4 manual says: "If the destination operand is a
//..                   non-empty register, the invalid-operation exception
//..                   is not generated.  Hence put_ST_UNCHECKED. */
//..                put_ST_UNCHECKED(r_dst, get_ST(0));
//..                break;

            case 0xD8 ... 0xDF: /* FSTP %st(0),%st(?) */
               r_dst = (UInt)modrm - 0xD8;
               DIP("fstp %%st(0),%%st(%u)\n", r_dst);
               /* P4 manual says: "If the destination operand is a
                  non-empty register, the invalid-operation exception
                  is not generated.  Hence put_ST_UNCHECKED. */
               put_ST_UNCHECKED(r_dst, get_ST(0));
               fp_pop();
               break;

//..             case 0xE0 ... 0xE7: /* FUCOM %st(0),%st(?) */
//..                r_dst = (UInt)modrm - 0xE0;
//..                DIP("fucom %%st(0),%%st(%d)\n", r_dst);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, get_ST(0), get_ST(r_dst)),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                break;
//.. 
//..             case 0xE8 ... 0xEF: /* FUCOMP %st(0),%st(?) */
//..                r_dst = (UInt)modrm - 0xE8;
//..                DIP("fucomp %%st(0),%%st(%d)\n", r_dst);
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, get_ST(0), get_ST(r_dst)),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                fp_pop();
//..                break;

            default:
               goto decode_fail;
         }
      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xDE opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xDE) {

      if (modrm < 0xC0) {

//..          /* bits 5,4,3 are an opcode extension, and the modRM also
//..             specifies an address. */
//..          IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
//..          delta += len;
//.. 
//..          switch (gregLO3ofRM(modrm)) {
//.. 
//..             case 0: /* FIADD m16int */ /* ST(0) += m16int */
//..                DIP("fiaddw %s\n", dis_buf);
//..                fop = Iop_AddF64;
//..                goto do_fop_m16;
//.. 
//..             case 1: /* FIMUL m16int */ /* ST(0) *= m16int */
//..                DIP("fimulw %s\n", dis_buf);
//..                fop = Iop_MulF64;
//..                goto do_fop_m16;
//.. 
//..             case 4: /* FISUB m16int */ /* ST(0) -= m16int */
//..                DIP("fisubw %s\n", dis_buf);
//..                fop = Iop_SubF64;
//..                goto do_fop_m16;
//.. 
//..             case 5: /* FISUBR m16int */ /* ST(0) = m16int - ST(0) */
//..                DIP("fisubrw %s\n", dis_buf);
//..                fop = Iop_SubF64;
//..                goto do_foprev_m16;
//.. 
//..             case 6: /* FIDIV m16int */ /* ST(0) /= m16int */
//..                DIP("fisubw %s\n", dis_buf);
//..                fop = Iop_DivF64;
//..                goto do_fop_m16;
//.. 
//..             case 7: /* FIDIVR m16int */ /* ST(0) = m16int / ST(0) */
//..                DIP("fidivrw %s\n", dis_buf);
//..                fop = Iop_DivF64;
//..                goto do_foprev_m16;
//.. 
//..             do_fop_m16:
//..                put_ST_UNCHECKED(0, 
//..                   binop(fop, 
//..                         get_ST(0),
//..                         unop(Iop_I32toF64,
//..                              unop(Iop_16Sto32, 
//..                                   loadLE(Ity_I16, mkexpr(addr))))));
//..                break;
//.. 
//..             do_foprev_m16:
//..                put_ST_UNCHECKED(0, 
//..                   binop(fop, 
//..                         unop(Iop_I32toF64,
//..                              unop(Iop_16Sto32, 
//..                                   loadLE(Ity_I16, mkexpr(addr)))),
//..                         get_ST(0)));
//..                break;
//.. 
//..             default:
//..                vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
//..                vex_printf("first_opcode == 0xDE\n");
//..                goto decode_fail;
//..          }

      } else {

         delta++;
         switch (modrm) {

            case 0xC0 ... 0xC7: /* FADDP %st(0),%st(?) */
               fp_do_op_ST_ST ( "add", Iop_AddF64, 0, modrm - 0xC0, True );
               break;

            case 0xC8 ... 0xCF: /* FMULP %st(0),%st(?) */
               fp_do_op_ST_ST ( "mul", Iop_MulF64, 0, modrm - 0xC8, True );
               break;

//..             case 0xD9: /* FCOMPP %st(0),%st(1) */
//..                DIP("fuompp %%st(0),%%st(1)\n");
//..                /* This forces C1 to zero, which isn't right. */
//..                put_C3210( 
//..                    binop( Iop_And32,
//..                           binop(Iop_Shl32, 
//..                                 binop(Iop_CmpF64, get_ST(0), get_ST(1)),
//..                                 mkU8(8)),
//..                           mkU32(0x4500)
//..                    ));
//..                fp_pop();
//..                fp_pop();
//..                break;

            case 0xE0 ... 0xE7: /* FSUBRP %st(0),%st(?) */
               fp_do_oprev_ST_ST ( "subr", Iop_SubF64, 0,  modrm - 0xE0, True );
               break;

            case 0xE8 ... 0xEF: /* FSUBP %st(0),%st(?) */
               fp_do_op_ST_ST ( "sub", Iop_SubF64, 0,  modrm - 0xE8, True );
               break;

            case 0xF0 ... 0xF7: /* FDIVRP %st(0),%st(?) */
               fp_do_oprev_ST_ST ( "divr", Iop_DivF64, 0, modrm - 0xF0, True );
               break;

            case 0xF8 ... 0xFF: /* FDIVP %st(0),%st(?) */
               fp_do_op_ST_ST ( "div", Iop_DivF64, 0, modrm - 0xF8, True );
               break;

            default: 
               goto decode_fail;
         }

      }
   }

   /* -+-+-+-+-+-+-+-+-+-+-+-+ 0xDF opcodes +-+-+-+-+-+-+-+ */
   else
   if (first_opcode == 0xDF) {

      if (modrm < 0xC0) {

         /* bits 5,4,3 are an opcode extension, and the modRM also
            specifies an address. */
         IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
         delta += len;

         switch (gregLO3ofRM(modrm)) {

            case 0: /* FILD m16int */
               DIP("fildw %s\n", dis_buf);
               fp_push();
               put_ST(0, unop(Iop_I32toF64,
                              unop(Iop_16Sto32,
                                   loadLE(Ity_I16, mkexpr(addr)))));
               break;

//..             case 2: /* FIST m16 */
//..                DIP("fistp %s\n", dis_buf);
//..                storeLE( mkexpr(addr), 
//..                         binop(Iop_F64toI16, get_roundingmode(), get_ST(0)) );
//..                break;
//.. 
//..             case 3: /* FISTP m16 */
//..                DIP("fistps %s\n", dis_buf);
//..                storeLE( mkexpr(addr), 
//..                         binop(Iop_F64toI16, get_roundingmode(), get_ST(0)) );
//..                fp_pop();
//..                break;

            case 5: /* FILD m64 */
               DIP("fildll %s\n", dis_buf);
               fp_push();
               put_ST(0, binop(Iop_I64toF64,
                               get_roundingmode(),
                               loadLE(Ity_I64, mkexpr(addr))));
               break;

//..             case 7: /* FISTP m64 */
//..                DIP("fistpll %s\n", dis_buf);
//..                storeLE( mkexpr(addr), 
//..                         binop(Iop_F64toI64, get_roundingmode(), get_ST(0)) );
//..                fp_pop();
//..                break;

            default:
               vex_printf("unhandled opc_aux = 0x%2x\n", gregLO3ofRM(modrm));
               vex_printf("first_opcode == 0xDF\n");
               goto decode_fail;
         }

      } else {

         delta++;
         switch (modrm) {

            case 0xC0: /* FFREEP %st(0) */
               DIP("ffreep %%st(%d)\n", 0);
               put_ST_TAG ( 0, mkU8(0) );
               fp_pop();
               break;

//..             case 0xE0: /* FNSTSW %ax */
//..                DIP("fnstsw %%ax\n");
//..                /* Invent a plausible-looking FPU status word value and
//..                   dump it in %AX:
//..                      ((ftop & 7) << 11) | (c3210 & 0x4700)
//..                */
//..                putIReg(2, R_EAX,
//..                   unop(Iop_32to16,
//..                        binop(Iop_Or32,
//..                              binop(Iop_Shl32, 
//..                                    binop(Iop_And32, get_ftop(), mkU32(7)), 
//..                                    mkU8(11)),
//..                              binop(Iop_And32, get_C3210(), mkU32(0x4700))
//..                )));
//..                break;

            case 0xE8 ... 0xEF: /* FUCOMIP %st(0),%st(?) */
               fp_do_ucomi_ST0_STi( (UInt)modrm - 0xE8, True );
               break;

//..             case 0xF0 ... 0xF7: /* FCOMIP %st(0),%st(?) */
//..                /* not really right since COMIP != UCOMIP */
//..                fp_do_ucomi_ST0_STi( (UInt)modrm - 0xF0, True );
//..                break;

            default: 
               goto decode_fail;
         }
      }

   }

   else
      goto decode_fail;

   *decode_ok = True;
   return delta;

  decode_fail:
   *decode_ok = False;
   return delta;
}


//.. /*------------------------------------------------------------*/
//.. /*---                                                      ---*/
//.. /*--- MMX INSTRUCTIONS                                     ---*/
//.. /*---                                                      ---*/
//.. /*------------------------------------------------------------*/
//.. 
//.. /* Effect of MMX insns on x87 FPU state (table 11-2 of 
//..    IA32 arch manual, volume 3):
//.. 
//..    Read from, or write to MMX register (viz, any insn except EMMS):
//..    * All tags set to Valid (non-empty) -- FPTAGS[i] := nonzero
//..    * FP stack pointer set to zero
//.. 
//..    EMMS:
//..    * All tags set to Invalid (empty) -- FPTAGS[i] := zero
//..    * FP stack pointer set to zero
//.. */
//.. 
//.. static void do_MMX_preamble ( void )
//.. {
//..    Int      i;
//..    IRArray* descr = mkIRArray( OFFB_FPTAGS, Ity_I8, 8 );
//..    IRExpr*  zero  = mkU32(0);
//..    IRExpr*  tag1  = mkU8(1);
//..    put_ftop(zero);
//..    for (i = 0; i < 8; i++)
//..       stmt( IRStmt_PutI( descr, zero, i, tag1 ) );
//.. }
//.. 
//.. static void do_EMMS_preamble ( void )
//.. {
//..    Int      i;
//..    IRArray* descr = mkIRArray( OFFB_FPTAGS, Ity_I8, 8 );
//..    IRExpr*  zero  = mkU32(0);
//..    IRExpr*  tag0  = mkU8(0);
//..    put_ftop(zero);
//..    for (i = 0; i < 8; i++)
//..       stmt( IRStmt_PutI( descr, zero, i, tag0 ) );
//.. }
//.. 
//.. 
//.. static IRExpr* getMMXReg ( UInt archreg )
//.. {
//..    vassert(archreg < 8);
//..    return IRExpr_Get( OFFB_FPREGS + 8 * archreg, Ity_I64 );
//.. }
//.. 
//.. 
//.. static void putMMXReg ( UInt archreg, IRExpr* e )
//.. {
//..    vassert(archreg < 8);
//..    vassert(typeOfIRExpr(irbb->tyenv,e) == Ity_I64);
//..    stmt( IRStmt_Put( OFFB_FPREGS + 8 * archreg, e ) );
//.. }
//.. 
//.. 
//.. /* Helper for non-shift MMX insns.  Note this is incomplete in the
//..    sense that it does not first call do_MMX_preamble() -- that is the
//..    responsibility of its caller. */
//.. 
//.. static 
//.. UInt dis_MMXop_regmem_to_reg ( UChar sorb,
//..                                UInt  delta,
//..                                UChar opc,
//..                                Char* name,
//..                                Bool  show_granularity )
//.. {
//..    HChar   dis_buf[50];
//..    UChar   modrm = getUChar(delta);
//..    Bool    isReg = epartIsReg(modrm);
//..    IRExpr* argL  = NULL;
//..    IRExpr* argR  = NULL;
//..    IRExpr* argG  = NULL;
//..    IRExpr* argE  = NULL;
//..    IRTemp  res   = newTemp(Ity_I64);
//.. 
//..    Bool    invG  = False;
//..    IROp    op    = Iop_INVALID;
//..    void*   hAddr = NULL;
//..    Char*   hName = NULL;
//..    Bool    eLeft = False;
//.. 
//.. #  define XXX(_name) do { hAddr = &_name; hName = #_name; } while (0)
//.. 
//..    switch (opc) {
//..       /* Original MMX ones */
//..       case 0xFC: op = Iop_Add8x8; break;
//..       case 0xFD: op = Iop_Add16x4; break;
//..       case 0xFE: op = Iop_Add32x2; break;
//.. 
//..       case 0xEC: op = Iop_QAdd8Sx8; break;
//..       case 0xED: op = Iop_QAdd16Sx4; break;
//.. 
//..       case 0xDC: op = Iop_QAdd8Ux8; break;
//..       case 0xDD: op = Iop_QAdd16Ux4; break;
//.. 
//..       case 0xF8: op = Iop_Sub8x8;  break;
//..       case 0xF9: op = Iop_Sub16x4; break;
//..       case 0xFA: op = Iop_Sub32x2; break;
//.. 
//..       case 0xE8: op = Iop_QSub8Sx8; break;
//..       case 0xE9: op = Iop_QSub16Sx4; break;
//.. 
//..       case 0xD8: op = Iop_QSub8Ux8; break;
//..       case 0xD9: op = Iop_QSub16Ux4; break;
//.. 
//..       case 0xE5: op = Iop_MulHi16Sx4; break;
//..       case 0xD5: op = Iop_Mul16x4; break;
//..       case 0xF5: XXX(x86g_calculate_mmx_pmaddwd); break;
//.. 
//..       case 0x74: op = Iop_CmpEQ8x8; break;
//..       case 0x75: op = Iop_CmpEQ16x4; break;
//..       case 0x76: op = Iop_CmpEQ32x2; break;
//.. 
//..       case 0x64: op = Iop_CmpGT8Sx8; break;
//..       case 0x65: op = Iop_CmpGT16Sx4; break;
//..       case 0x66: op = Iop_CmpGT32Sx2; break;
//.. 
//..       case 0x6B: op = Iop_QNarrow32Sx2; eLeft = True; break;
//..       case 0x63: op = Iop_QNarrow16Sx4; eLeft = True; break;
//..       case 0x67: op = Iop_QNarrow16Ux4; eLeft = True; break;
//.. 
//..       case 0x68: op = Iop_InterleaveHI8x8;  eLeft = True; break;
//..       case 0x69: op = Iop_InterleaveHI16x4; eLeft = True; break;
//..       case 0x6A: op = Iop_InterleaveHI32x2; eLeft = True; break;
//.. 
//..       case 0x60: op = Iop_InterleaveLO8x8;  eLeft = True; break;
//..       case 0x61: op = Iop_InterleaveLO16x4; eLeft = True; break;
//..       case 0x62: op = Iop_InterleaveLO32x2; eLeft = True; break;
//.. 
//..       case 0xDB: op = Iop_And64; break;
//..       case 0xDF: op = Iop_And64; invG = True; break;
//..       case 0xEB: op = Iop_Or64; break;
//..       case 0xEF: /* Possibly do better here if argL and argR are the
//..                     same reg */
//..                  op = Iop_Xor64; break;
//.. 
//..       /* Introduced in SSE1 */
//..       case 0xE0: op = Iop_Avg8Ux8;    break;
//..       case 0xE3: op = Iop_Avg16Ux4;   break;
//..       case 0xEE: op = Iop_Max16Sx4;   break;
//..       case 0xDE: op = Iop_Max8Ux8;    break;
//..       case 0xEA: op = Iop_Min16Sx4;   break;
//..       case 0xDA: op = Iop_Min8Ux8;    break;
//..       case 0xE4: op = Iop_MulHi16Ux4; break;
//..       case 0xF6: XXX(x86g_calculate_mmx_psadbw); break;
//.. 
//..       /* Introduced in SSE2 */
//..       case 0xD4: op = Iop_Add64; break;
//..       case 0xFB: op = Iop_Sub64; break;
//.. 
//..       default: 
//..          vex_printf("\n0x%x\n", (Int)opc);
//..          vpanic("dis_MMXop_regmem_to_reg");
//..    }
//.. 
//.. #  undef XXX
//.. 
//..    argG = getMMXReg(gregOfRM(modrm));
//..    if (invG)
//..       argG = unop(Iop_Not64, argG);
//.. 
//..    if (isReg) {
//..       delta++;
//..       argE = getMMXReg(eregOfRM(modrm));
//..    } else {
//..       Int    len;
//..       IRTemp addr = disAMode( &len, sorb, delta, dis_buf );
//..       delta += len;
//..       argE = loadLE(Ity_I64, mkexpr(addr));
//..    }
//.. 
//..    if (eLeft) {
//..       argL = argE;
//..       argR = argG;
//..    } else {
//..       argL = argG;
//..       argR = argE;
//..    }
//.. 
//..    if (op != Iop_INVALID) {
//..       vassert(hName == NULL);
//..       vassert(hAddr == NULL);
//..       assign(res, binop(op, argL, argR));
//..    } else {
//..       vassert(hName != NULL);
//..       vassert(hAddr != NULL);
//..       assign( res, 
//..               mkIRExprCCall(
//..                  Ity_I64, 
//..                  0/*regparms*/, hName, hAddr,
//..                  mkIRExprVec_2( argL, argR )
//..               ) 
//..             );
//..    }
//.. 
//..    putMMXReg( gregOfRM(modrm), mkexpr(res) );
//.. 
//..    DIP("%s%s %s, %s\n", 
//..        name, show_granularity ? nameMMXGran(opc & 3) : (Char*)"",
//..        ( isReg ? nameMMXReg(eregOfRM(modrm)) : dis_buf ),
//..        nameMMXReg(gregOfRM(modrm)) );
//.. 
//..    return delta;
//.. }
//.. 
//.. 
//.. /* Vector by scalar shift of G by the amount specified at the bottom
//..    of E.  This is a straight copy of dis_SSE_shiftG_byE. */
//.. 
//.. static UInt dis_MMX_shiftG_byE ( UChar sorb, ULong delta, 
//..                                  HChar* opname, IROp op )
//.. {
//..    HChar   dis_buf[50];
//..    Int     alen, size;
//..    IRTemp  addr;
//..    Bool    shl, shr, sar;
//..    UChar   rm   = getUChar(delta);
//..    IRTemp  g0   = newTemp(Ity_I64);
//..    IRTemp  g1   = newTemp(Ity_I64);
//..    IRTemp  amt  = newTemp(Ity_I32);
//..    IRTemp  amt8 = newTemp(Ity_I8);
//.. 
//..    if (epartIsReg(rm)) {
//..       assign( amt, unop(Iop_64to32, getMMXReg(eregOfRM(rm))) );
//..       DIP("%s %s,%s\n", opname,
//..                         nameMMXReg(eregOfRM(rm)),
//..                         nameMMXReg(gregOfRM(rm)) );
//..       delta++;
//..    } else {
//..       addr = disAMode ( &alen, sorb, delta, dis_buf );
//..       assign( amt, loadLE(Ity_I32, mkexpr(addr)) );
//..       DIP("%s %s,%s\n", opname,
//..                         dis_buf,
//..                         nameMMXReg(gregOfRM(rm)) );
//..       delta += alen;
//..    }
//..    assign( g0,   getMMXReg(gregOfRM(rm)) );
//..    assign( amt8, unop(Iop_32to8, mkexpr(amt)) );
//.. 
//..    shl = shr = sar = False;
//..    size = 0;
//..    switch (op) {
//..       case Iop_ShlN16x4: shl = True; size = 32; break;
//..       case Iop_ShlN32x2: shl = True; size = 32; break;
//..       case Iop_Shl64:    shl = True; size = 64; break;
//..       case Iop_ShrN16x4: shr = True; size = 16; break;
//..       case Iop_ShrN32x2: shr = True; size = 32; break;
//..       case Iop_Shr64:    shr = True; size = 64; break;
//..       case Iop_SarN16x4: sar = True; size = 16; break;
//..       case Iop_SarN32x2: sar = True; size = 32; break;
//..       default: vassert(0);
//..    }
//.. 
//..    if (shl || shr) {
//..      assign( 
//..         g1,
//..         IRExpr_Mux0X(
//..            unop(Iop_1Uto8,binop(Iop_CmpLT32U,mkexpr(amt),mkU32(size))),
//..            mkU64(0),
//..            binop(op, mkexpr(g0), mkexpr(amt8))
//..         )
//..      );
//..    } else 
//..    if (sar) {
//..      assign( 
//..         g1,
//..         IRExpr_Mux0X(
//..            unop(Iop_1Uto8,binop(Iop_CmpLT32U,mkexpr(amt),mkU32(size))),
//..            binop(op, mkexpr(g0), mkU8(size-1)),
//..            binop(op, mkexpr(g0), mkexpr(amt8))
//..         )
//..      );
//..    } else {
//..       vassert(0);
//..    }
//.. 
//..    putMMXReg( gregOfRM(rm), mkexpr(g1) );
//..    return delta;
//.. }
//.. 
//.. 
//.. /* Vector by scalar shift of E by an immediate byte.  This is a
//..    straight copy of dis_SSE_shiftE_imm. */
//.. 
//.. static 
//.. UInt dis_MMX_shiftE_imm ( ULong delta, HChar* opname, IROp op )
//.. {
//..    Bool    shl, shr, sar;
//..    UChar   rm   = getUChar(delta);
//..    IRTemp  e0   = newTemp(Ity_I64);
//..    IRTemp  e1   = newTemp(Ity_I64);
//..    UChar   amt, size;
//..    vassert(epartIsReg(rm));
//..    vassert(gregOfRM(rm) == 2 
//..            || gregOfRM(rm) == 4 || gregOfRM(rm) == 6);
//..    amt = (Int)(getUChar(delta+1));
//..    delta += 2;
//..    DIP("%s $%d,%s\n", opname,
//..                       (Int)amt,
//..                       nameMMXReg(eregOfRM(rm)) );
//.. 
//..    assign( e0, getMMXReg(eregOfRM(rm)) );
//.. 
//..    shl = shr = sar = False;
//..    size = 0;
//..    switch (op) {
//..       case Iop_ShlN16x4: shl = True; size = 16; break;
//..       case Iop_ShlN32x2: shl = True; size = 32; break;
//..       case Iop_Shl64:    shl = True; size = 64; break;
//..       case Iop_SarN16x4: sar = True; size = 16; break;
//..       case Iop_SarN32x2: sar = True; size = 32; break;
//..       case Iop_ShrN16x4: shr = True; size = 16; break;
//..       case Iop_ShrN32x2: shr = True; size = 32; break;
//..       case Iop_Shr64:    shr = True; size = 64; break;
//..       default: vassert(0);
//..    }
//.. 
//..    if (shl || shr) {
//..      assign( e1, amt >= size 
//..                     ? mkU64(0)
//..                     : binop(op, mkexpr(e0), mkU8(amt))
//..      );
//..    } else 
//..    if (sar) {
//..      assign( e1, amt >= size 
//..                     ? binop(op, mkexpr(e0), mkU8(size-1))
//..                     : binop(op, mkexpr(e0), mkU8(amt))
//..      );
//..    } else {
//..       vassert(0);
//..    }
//.. 
//..    putMMXReg( eregOfRM(rm), mkexpr(e1) );
//..    return delta;
//.. }
//.. 
//.. 
//.. /* Completely handle all MMX instructions except emms. */
//.. 
//.. static
//.. UInt dis_MMX ( Bool* decode_ok, UChar sorb, Int sz, ULong delta )
//.. {
//..    Int   len;
//..    UChar modrm;
//..    HChar dis_buf[50];
//..    UChar opc = getUChar(delta);
//..    delta++;
//.. 
//..    /* dis_MMX handles all insns except emms. */
//..    do_MMX_preamble();
//.. 
//..    switch (opc) {
//.. 
//..       case 0x6E: 
//..          /* MOVD (src)ireg-or-mem (E), (dst)mmxreg (G)*/
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          modrm = getUChar(delta);
//..          if (epartIsReg(modrm)) {
//..             delta++;
//..             putMMXReg(
//..                gregOfRM(modrm),
//..                binop( Iop_32HLto64,
//..                       mkU32(0),
//..                       getIReg(4, eregOfRM(modrm)) ) );
//..             DIP("movd %s, %s\n", 
//..                 nameIReg(4,eregOfRM(modrm)), nameMMXReg(gregOfRM(modrm)));
//..          } else {
//..             IRTemp addr = disAMode( &len, sorb, delta, dis_buf );
//..             delta += len;
//..             putMMXReg(
//..                gregOfRM(modrm),
//..                binop( Iop_32HLto64,
//..                       mkU32(0),
//..                       loadLE(Ity_I32, mkexpr(addr)) ) );
//..             DIP("movd %s, %s\n", dis_buf, nameMMXReg(gregOfRM(modrm)));
//..          }
//..          break;
//.. 
//..       case 0x7E: /* MOVD (src)mmxreg (G), (dst)ireg-or-mem (E) */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          modrm = getUChar(delta);
//..          if (epartIsReg(modrm)) {
//..             delta++;
//..             putIReg( 4, eregOfRM(modrm),
//..                      unop(Iop_64to32, getMMXReg(gregOfRM(modrm)) ) );
//..             DIP("movd %s, %s\n", 
//..                 nameMMXReg(gregOfRM(modrm)), nameIReg(4,eregOfRM(modrm)));
//..          } else {
//..             IRTemp addr = disAMode( &len, sorb, delta, dis_buf );
//..             delta += len;
//..             storeLE( mkexpr(addr),
//..                      unop(Iop_64to32, getMMXReg(gregOfRM(modrm)) ) );
//..             DIP("movd %s, %s\n", nameMMXReg(gregOfRM(modrm)), dis_buf);
//..          }
//..          break;
//.. 
//..       case 0x6F:
//..          /* MOVQ (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          modrm = getUChar(delta);
//..          if (epartIsReg(modrm)) {
//..             delta++;
//..             putMMXReg( gregOfRM(modrm), getMMXReg(eregOfRM(modrm)) );
//..             DIP("movq %s, %s\n", 
//..                 nameMMXReg(eregOfRM(modrm)), nameMMXReg(gregOfRM(modrm)));
//..          } else {
//..             IRTemp addr = disAMode( &len, sorb, delta, dis_buf );
//..             delta += len;
//..             putMMXReg( gregOfRM(modrm), loadLE(Ity_I64, mkexpr(addr)) );
//..             DIP("movq %s, %s\n", 
//..                 dis_buf, nameMMXReg(gregOfRM(modrm)));
//..          }
//..          break;
//.. 
//..       case 0x7F:
//..          /* MOVQ (src)mmxreg, (dst)mmxreg-or-mem */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          modrm = getUChar(delta);
//..          if (epartIsReg(modrm)) {
//..             /* Fall through.  The assembler doesn't appear to generate
//..                these. */
//..             goto mmx_decode_failure;
//..          } else {
//..             IRTemp addr = disAMode( &len, sorb, delta, dis_buf );
//..             delta += len;
//..             storeLE( mkexpr(addr), getMMXReg(gregOfRM(modrm)) );
//..             DIP("mov(nt)q %s, %s\n", 
//..                 nameMMXReg(gregOfRM(modrm)), dis_buf);
//..          }
//..          break;
//.. 
//..       case 0xFC: 
//..       case 0xFD: 
//..       case 0xFE: /* PADDgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "padd", True );
//..          break;
//.. 
//..       case 0xEC: 
//..       case 0xED: /* PADDSgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "padds", True );
//..          break;
//.. 
//..       case 0xDC: 
//..       case 0xDD: /* PADDUSgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "paddus", True );
//..          break;
//.. 
//..       case 0xF8: 
//..       case 0xF9: 
//..       case 0xFA: /* PSUBgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "psub", True );
//..          break;
//.. 
//..       case 0xE8: 
//..       case 0xE9: /* PSUBSgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "psubs", True );
//..          break;
//.. 
//..       case 0xD8: 
//..       case 0xD9: /* PSUBUSgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "psubus", True );
//..          break;
//.. 
//..       case 0xE5: /* PMULHW (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pmulhw", False );
//..          break;
//.. 
//..       case 0xD5: /* PMULLW (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pmullw", False );
//..          break;
//.. 
//..       case 0xF5: /* PMADDWD (src)mmxreg-or-mem, (dst)mmxreg */
//..          vassert(sz == 4);
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pmaddwd", False );
//..          break;
//.. 
//..       case 0x74: 
//..       case 0x75: 
//..       case 0x76: /* PCMPEQgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pcmpeq", True );
//..          break;
//.. 
//..       case 0x64: 
//..       case 0x65: 
//..       case 0x66: /* PCMPGTgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pcmpgt", True );
//..          break;
//.. 
//..       case 0x6B: /* PACKSSDW (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "packssdw", False );
//..          break;
//.. 
//..       case 0x63: /* PACKSSWB (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "packsswb", False );
//..          break;
//.. 
//..       case 0x67: /* PACKUSWB (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "packuswb", False );
//..          break;
//.. 
//..       case 0x68: 
//..       case 0x69: 
//..       case 0x6A: /* PUNPCKHgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "punpckh", True );
//..          break;
//.. 
//..       case 0x60: 
//..       case 0x61: 
//..       case 0x62: /* PUNPCKLgg (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "punpckl", True );
//..          break;
//.. 
//..       case 0xDB: /* PAND (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pand", False );
//..          break;
//.. 
//..       case 0xDF: /* PANDN (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pandn", False );
//..          break;
//.. 
//..       case 0xEB: /* POR (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "por", False );
//..          break;
//.. 
//..       case 0xEF: /* PXOR (src)mmxreg-or-mem, (dst)mmxreg */
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          delta = dis_MMXop_regmem_to_reg ( sorb, delta, opc, "pxor", False );
//..          break; 
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #     define SHIFT_BY_REG(_name,_op)                                 \
/..                 delta = dis_MMX_shiftG_byE(sorb, delta, _name, _op); \
/..                 break;
#endif /* stop gcc multi-line comment warning */
//.. 
//..       /* PSLLgg (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xF1: SHIFT_BY_REG("psllw", Iop_ShlN16x4);
//..       case 0xF2: SHIFT_BY_REG("pslld", Iop_ShlN32x2);
//..       case 0xF3: SHIFT_BY_REG("psllq", Iop_Shl64);
//.. 
//..       /* PSRLgg (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xD1: SHIFT_BY_REG("psrlw", Iop_ShrN16x4);
//..       case 0xD2: SHIFT_BY_REG("psrld", Iop_ShrN32x2);
//..       case 0xD3: SHIFT_BY_REG("psrlq", Iop_Shr64);
//.. 
//..       /* PSRAgg (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xE1: SHIFT_BY_REG("psraw", Iop_SarN16x4);
//..       case 0xE2: SHIFT_BY_REG("psrad", Iop_SarN32x2);
//.. 
//.. #     undef SHIFT_BY_REG
//.. 
//..       case 0x71: 
//..       case 0x72: 
//..       case 0x73: {
//..          /* (sz==4): PSLLgg/PSRAgg/PSRLgg mmxreg by imm8 */
//..          UChar byte1, byte2, subopc;
//..          void* hAddr;
//..          Char* hName;
//..          if (sz != 4) 
//..             goto mmx_decode_failure;
//..          byte1  = opc;                       /* 0x71/72/73 */
//..          byte2  = getUChar(delta);           /* amode / sub-opcode */
//..          subopc = (byte2 >> 3) & 7;
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #        define SHIFT_BY_IMM(_name,_op)                         \
/..              do { delta = dis_MMX_shiftE_imm(delta,_name,_op);  \
/..              } while (0)
#endif /* stop gcc multi-line comment warning */
//.. 
//..          hAddr = NULL;
//..          hName = NULL;
//.. 
//..               if (subopc == 2 /*SRL*/ && opc == 0x71) 
//..                  SHIFT_BY_IMM("psrlw", Iop_ShrN16x4);
//..          else if (subopc == 2 /*SRL*/ && opc == 0x72) 
//..                  SHIFT_BY_IMM("psrld", Iop_ShrN32x2);
//..          else if (subopc == 2 /*SRL*/ && opc == 0x73) 
//..                  SHIFT_BY_IMM("psrlq", Iop_Shr64);
//.. 
//..          else if (subopc == 4 /*SAR*/ && opc == 0x71) 
//..                  SHIFT_BY_IMM("psraw", Iop_SarN16x4);
//..          else if (subopc == 4 /*SAR*/ && opc == 0x72) 
//..                  SHIFT_BY_IMM("psrad", Iop_SarN32x2);
//.. 
//..          else if (subopc == 6 /*SHL*/ && opc == 0x71) 
//..                  SHIFT_BY_IMM("psllw", Iop_ShlN16x4);
//..          else if (subopc == 6 /*SHL*/ && opc == 0x72) 
//..                  SHIFT_BY_IMM("pslld", Iop_ShlN32x2);
//..          else if (subopc == 6 /*SHL*/ && opc == 0x73) 
//..                  SHIFT_BY_IMM("psllq", Iop_Shl64);
//.. 
//..          else goto mmx_decode_failure;
//.. 
//.. #        undef SHIFT_BY_IMM
//..          break;
//..       }
//.. 
//..       /* --- MMX decode failure --- */
//..       default:
//..       mmx_decode_failure:
//..          *decode_ok = False;
//..          return delta; /* ignored */
//.. 
//..    }
//.. 
//..    *decode_ok = True;
//..    return delta;
//.. }
//.. 
//.. 
//.. /*------------------------------------------------------------*/
//.. /*--- More misc arithmetic and other obscure insns.        ---*/
//.. /*------------------------------------------------------------*/
//.. 
//.. /* Double length left and right shifts.  Apparently only required in
//..    v-size (no b- variant). */
//.. static
//.. UInt dis_SHLRD_Gv_Ev ( UChar sorb,
//..                        ULong delta, UChar modrm,
//..                        Int sz,
//..                        IRExpr* shift_amt,
//..                        Bool amt_is_literal,
//..                        Char* shift_amt_txt,
//..                        Bool left_shift )
//.. {
//..    /* shift_amt :: Ity_I8 is the amount to shift.  shift_amt_txt is used
//..       for printing it.   And eip on entry points at the modrm byte. */
//..    Int len;
//..    HChar dis_buf[50];
//.. 
//..    IRType ty       = szToITy(sz);
//..    IRTemp gsrc     = newTemp(ty);
//..    IRTemp esrc     = newTemp(ty);
//..    IRTemp addr     = IRTemp_INVALID;
//..    IRTemp tmpSH    = newTemp(Ity_I8);
//..    IRTemp tmpL     = IRTemp_INVALID;
//..    IRTemp tmpRes   = IRTemp_INVALID;
//..    IRTemp tmpSubSh = IRTemp_INVALID;
//..    IROp   mkpair;
//..    IROp   getres;
//..    IROp   shift;
//..    IRExpr* mask = NULL;
//.. 
//..    vassert(sz == 2 || sz == 4);
//.. 
//..    /* The E-part is the destination; this is shifted.  The G-part
//..       supplies bits to be shifted into the E-part, but is not
//..       changed.  
//.. 
//..       If shifting left, form a double-length word with E at the top
//..       and G at the bottom, and shift this left.  The result is then in
//..       the high part.
//.. 
//..       If shifting right, form a double-length word with G at the top
//..       and E at the bottom, and shift this right.  The result is then
//..       at the bottom.  */
//.. 
//..    /* Fetch the operands. */
//.. 
//..    assign( gsrc, getIReg(sz, gregOfRM(modrm)) );
//.. 
//..    if (epartIsReg(modrm)) {
//..       delta++;
//..       assign( esrc, getIReg(sz, eregOfRM(modrm)) );
//..       DIP("sh%cd%c %s, %s, %s\n",
//..           ( left_shift ? 'l' : 'r' ), nameISize(sz), 
//..           shift_amt_txt,
//..           nameIReg(sz, gregOfRM(modrm)), nameIReg(sz, eregOfRM(modrm)));
//..    } else {
//..       addr = disAMode ( &len, sorb, delta, dis_buf );
//..       delta += len;
//..       assign( esrc, loadLE(ty, mkexpr(addr)) );
//..       DIP("sh%cd%c %s, %s, %s\n", 
//..           ( left_shift ? 'l' : 'r' ), nameISize(sz), 
//..           shift_amt_txt,
//..           nameIReg(sz, gregOfRM(modrm)), dis_buf);
//..    }
//.. 
//..    /* Round up the relevant primops. */
//.. 
//..    if (sz == 4) {
//..       tmpL     = newTemp(Ity_I64);
//..       tmpRes   = newTemp(Ity_I32);
//..       tmpSubSh = newTemp(Ity_I32);
//..       mkpair   = Iop_32HLto64;
//..       getres   = left_shift ? Iop_64HIto32 : Iop_64to32;
//..       shift    = left_shift ? Iop_Shl64 : Iop_Shr64;
//..       mask     = mkU8(31);
//..    } else {
//..       /* sz == 2 */
//..       tmpL     = newTemp(Ity_I32);
//..       tmpRes   = newTemp(Ity_I16);
//..       tmpSubSh = newTemp(Ity_I16);
//..       mkpair   = Iop_16HLto32;
//..       getres   = left_shift ? Iop_32HIto16 : Iop_32to16;
//..       shift    = left_shift ? Iop_Shl32 : Iop_Shr32;
//..       mask     = mkU8(15);
//..    }
//.. 
//..    /* Do the shift, calculate the subshift value, and set 
//..       the flag thunk. */
//.. 
//..    assign( tmpSH, binop(Iop_And8, shift_amt, mask) );
//.. 
//..    if (left_shift)
//..       assign( tmpL, binop(mkpair, mkexpr(esrc), mkexpr(gsrc)) );
//..    else
//..       assign( tmpL, binop(mkpair, mkexpr(gsrc), mkexpr(esrc)) );
//.. 
//..    assign( tmpRes, unop(getres, binop(shift, mkexpr(tmpL), mkexpr(tmpSH)) ) );
//..    assign( tmpSubSh, 
//..            unop(getres, 
//..                 binop(shift, 
//..                       mkexpr(tmpL), 
//..                       binop(Iop_And8, 
//..                             binop(Iop_Sub8, mkexpr(tmpSH), mkU8(1) ),
//..                             mask))) );
//.. 
//..    setFlags_DEP1_DEP2_shift ( left_shift ? Iop_Shl32 : Iop_Sar32,
//..                               tmpRes, tmpSubSh, ty, tmpSH );
//.. 
//..    /* Put result back. */
//.. 
//..    if (epartIsReg(modrm)) {
//..       putIReg(sz, eregOfRM(modrm), mkexpr(tmpRes));
//..    } else {
//..       storeLE( mkexpr(addr), mkexpr(tmpRes) );
//..    }
//.. 
//..    if (amt_is_literal) delta++;
//..    return delta;
//.. }
//.. 
//.. 
//.. /* Handle BT/BTS/BTR/BTC Gv, Ev.  Apparently b-size is not
//..    required. */
//.. 
//.. typedef enum { BtOpNone, BtOpSet, BtOpReset, BtOpComp } BtOp;
//.. 
//.. static Char* nameBtOp ( BtOp op )
//.. {
//..    switch (op) {
//..       case BtOpNone:  return "";
//..       case BtOpSet:   return "s";
//..       case BtOpReset: return "r";
//..       case BtOpComp:  return "c";
//..       default: vpanic("nameBtOp(x86)");
//..    }
//.. }
//.. 
//.. 
//.. static
//.. UInt dis_bt_G_E ( UChar sorb, Int sz, ULong delta, BtOp op )
//.. {
//..    HChar  dis_buf[50];
//..    UChar  modrm;
//..    Int    len;
//..    IRTemp t_fetched, t_bitno0, t_bitno1, t_bitno2, t_addr0, 
//..           t_addr1, t_esp, t_mask;
//.. 
//..    vassert(sz == 2 || sz == 4);
//.. 
//..    t_fetched = t_bitno0 = t_bitno1 = t_bitno2 
//..              = t_addr0 = t_addr1 = t_esp = t_mask = IRTemp_INVALID;
//.. 
//..    t_fetched = newTemp(Ity_I8);
//..    t_bitno0  = newTemp(Ity_I32);
//..    t_bitno1  = newTemp(Ity_I32);
//..    t_bitno2  = newTemp(Ity_I8);
//..    t_addr1   = newTemp(Ity_I32);
//..    modrm     = getUChar(delta);
//.. 
//..    assign( t_bitno0, widenUto32(getIReg(sz, gregOfRM(modrm))) );
//..    
//..    if (epartIsReg(modrm)) {
//..       delta++;
//..       /* Get it onto the client's stack. */
//..       t_esp = newTemp(Ity_I32);
//..       t_addr0 = newTemp(Ity_I32);
//.. 
//..       assign( t_esp, binop(Iop_Sub32, getIReg(4, R_ESP), mkU32(sz)) );
//..       putIReg(4, R_ESP, mkexpr(t_esp));
//.. 
//..       storeLE( mkexpr(t_esp), getIReg(sz, eregOfRM(modrm)) );
//.. 
//..       /* Make t_addr0 point at it. */
//..       assign( t_addr0, mkexpr(t_esp) );
//.. 
//..       /* Mask out upper bits of the shift amount, since we're doing a
//..          reg. */
//..       assign( t_bitno1, binop(Iop_And32, 
//..                               mkexpr(t_bitno0), 
//..                               mkU32(sz == 4 ? 31 : 15)) );
//.. 
//..    } else {
//..       t_addr0 = disAMode ( &len, sorb, delta, dis_buf );
//..       delta += len;
//..       assign( t_bitno1, mkexpr(t_bitno0) );
//..    }
//..   
//..    /* At this point: t_addr0 is the address being operated on.  If it
//..       was a reg, we will have pushed it onto the client's stack.
//..       t_bitno1 is the bit number, suitably masked in the case of a
//..       reg.  */
//..   
//..    /* Now the main sequence. */
//..    assign( t_addr1, 
//..            binop(Iop_Add32, 
//..                  mkexpr(t_addr0), 
//..                  binop(Iop_Sar32, mkexpr(t_bitno1), mkU8(3))) );
//.. 
//..    /* t_addr1 now holds effective address */
//.. 
//..    assign( t_bitno2, 
//..            unop(Iop_32to8, 
//..                 binop(Iop_And32, mkexpr(t_bitno1), mkU32(7))) );
//.. 
//..    /* t_bitno2 contains offset of bit within byte */
//.. 
//..    if (op != BtOpNone) {
//..       t_mask = newTemp(Ity_I8);
//..       assign( t_mask, binop(Iop_Shl8, mkU8(1), mkexpr(t_bitno2)) );
//..    }
//.. 
//..    /* t_mask is now a suitable byte mask */
//.. 
//..    assign( t_fetched, loadLE(Ity_I8, mkexpr(t_addr1)) );
//.. 
//..    if (op != BtOpNone) {
//..       switch (op) {
//..          case BtOpSet: 
//..             storeLE( mkexpr(t_addr1), 
//..                      binop(Iop_Or8, mkexpr(t_fetched), 
//..                                     mkexpr(t_mask)) );
//..             break;
//..          case BtOpComp: 
//..             storeLE( mkexpr(t_addr1), 
//..                      binop(Iop_Xor8, mkexpr(t_fetched), 
//..                                      mkexpr(t_mask)) );
//..             break;
//..          case BtOpReset: 
//..             storeLE( mkexpr(t_addr1), 
//..                      binop(Iop_And8, mkexpr(t_fetched), 
//..                                      unop(Iop_Not8, mkexpr(t_mask))) );
//..             break;
//..          default: 
//..             vpanic("dis_bt_G_E(x86)");
//..       }
//..    }
//..  
//..    /* Side effect done; now get selected bit into Carry flag */
//..    /* Flags: C=selected bit, O,S,Z,A,P undefined, so are set to zero. */
//..    stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
//..    stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
//..    stmt( IRStmt_Put( 
//..             OFFB_CC_DEP1,
//..             binop(Iop_And32,
//..                   binop(Iop_Shr32, 
//..                         unop(Iop_8Uto32, mkexpr(t_fetched)),
//..                         mkexpr(t_bitno2)),
//..                   mkU32(1)))
//..        );
//.. 
//..    /* Move reg operand from stack back to reg */
//..    if (epartIsReg(modrm)) {
//..       /* t_esp still points at it. */
//..       putIReg(sz, eregOfRM(modrm), loadLE(szToITy(sz), mkexpr(t_esp)) );
//..       putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(t_esp), mkU32(sz)) );
//..    }
//.. 
//..    DIP("bt%s%c %s, %s\n",
//..        nameBtOp(op), nameISize(sz), nameIReg(sz, gregOfRM(modrm)), 
//..        ( epartIsReg(modrm) ? nameIReg(sz, eregOfRM(modrm)) : dis_buf ) );
//..  
//..    return delta;
//.. }



/* Handle BSF/BSR.  Only v-size seems necessary. */
static
ULong dis_bs_E_G ( Prefix pfx, Int sz, ULong delta, Bool fwds )
{
   Bool   isReg;
   UChar  modrm;
   HChar  dis_buf[50];

   IRType ty    = szToITy(sz);
   IRTemp src   = newTemp(ty);
   IRTemp dst   = newTemp(ty);
   IRTemp src64 = newTemp(Ity_I64);
   IRTemp dst64 = newTemp(Ity_I64);
   IRTemp src8  = newTemp(Ity_I8);

   vassert(sz == 8 || sz == 4 || sz == 2);

   modrm = getUChar(delta);
   isReg = epartIsReg(modrm);
   if (isReg) {
      delta++;
      assign( src, getIRegE(sz, pfx, modrm) );
   } else {
      Int    len;
      IRTemp addr = disAMode( &len, pfx, delta, dis_buf, 0 );
      delta += len;
      assign( src, loadLE(ty, mkexpr(addr)) );
   }

   DIP("bs%c%c %s, %s\n",
       fwds ? 'f' : 'r', nameISize(sz), 
       ( isReg ? nameIRegE(sz, pfx, modrm) : dis_buf ), 
       nameIRegG(sz, pfx, modrm));

   /* First, widen src to 64 bits if it is not already. */
   assign( src64, widenUto64(mkexpr(src)) );

   /* Generate an 8-bit expression which is zero iff the 
      original is zero, and nonzero otherwise */
   assign( src8,
           unop(Iop_1Uto8, 
                binop(Iop_CmpNE64,
                      mkexpr(src64), mkU64(0))) );

   /* Flags: Z is 1 iff source value is zero.  All others 
      are undefined -- we force them to zero. */
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(AMD64G_CC_OP_COPY) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0) ));
   stmt( IRStmt_Put( 
            OFFB_CC_DEP1,
            IRExpr_Mux0X( mkexpr(src8),
                          /* src==0 */
                          mkU64(AMD64G_CC_MASK_Z),
                          /* src!=0 */
                          mkU64(0)
                        )
       ));
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU64(0) ));

   /* Result: iff source value is zero, we can't use
      Iop_Clz64/Iop_Ctz64 as they have no defined result in that case.
      But anyway, amd64 semantics say the result is undefined in
      such situations.  Hence handle the zero case specially. */

   /* Bleh.  What we compute:

          bsf64:  if src == 0 then {dst is unchanged} 
                              else Ctz64(src)

          bsr64:  if src == 0 then {dst is unchanged} 
                              else 63 - Clz64(src)

          bsf32:  if src == 0 then {dst is unchanged} 
                              else Ctz64(32Uto64(src))

          bsr32:  if src == 0 then {dst is unchanged}
                              else 63 - Clz64(32Uto64(src))

          bsf16:  if src == 0 then {dst is unchanged} 
                              else Ctz64(32Uto64(16Uto32(src)))

          bsr16:  if src == 0 then {dst is unchanged} 
                              else 63 - Clz64(32Uto64(16Uto32(src)))
   */

   /* The main computation, guarding against zero. */
   assign( dst64,
           IRExpr_Mux0X( 
              mkexpr(src8),
              /* src == 0 -- leave dst unchanged */
              widenUto64( getIRegG( sz, pfx, modrm ) ),
              /* src != 0 */
              fwds ? unop(Iop_Ctz64, mkexpr(src64))
                   : binop(Iop_Sub64, 
                           mkU64(63), 
                           unop(Iop_Clz64, mkexpr(src64)))
           )
         );

   if (sz == 2)
      assign( dst, unop(Iop_32to16, unop(Iop_64to32, mkexpr(dst64))) );
   else
   if (sz == 4)
      assign( dst, unop(Iop_64to32, mkexpr(dst64)) );
   else
      assign( dst, mkexpr(dst64) );

   /* dump result back */
   putIRegG( sz, pfx, modrm, mkexpr(dst) );

   return delta;
}


/* swap rAX with the reg specified by reg and REX.B */
static 
void codegen_xchg_rAX_Reg ( Prefix pfx, Int sz, UInt regLo3 )
{
   IRType ty = szToITy(sz);
   IRTemp t1 = newTemp(ty);
   IRTemp t2 = newTemp(ty);
   vassert(sz == 8);
   vassert(regLo3 < 8);
   assign( t1, getIReg64(R_RAX) );
   assign( t2, getIRegRexB(8,pfx, regLo3) );
   putIReg64( R_RAX, mkexpr(t2) );
   putIRegRexB(8, pfx, regLo3, mkexpr(t1) );
   DIP("xchg%c %s, %s\n", 
       nameISize(sz), nameIRegRAX(sz), 
                      nameIRegRexB(8,pfx, regLo3));
}


//.. static 
//.. void codegen_SAHF ( void )
//.. {
//..    /* Set the flags to:
//..       (x86g_calculate_flags_all() & X86G_CC_MASK_O)  -- retain the old O flag
//..       | (%AH & (X86G_CC_MASK_S|X86G_CC_MASK_Z|X86G_CC_MASK_A
//..                 |X86G_CC_MASK_P|X86G_CC_MASK_C)
//..    */
//..    UInt   mask_SZACP = X86G_CC_MASK_S|X86G_CC_MASK_Z|X86G_CC_MASK_A
//..                        |X86G_CC_MASK_C|X86G_CC_MASK_P;
//..    IRTemp oldflags   = newTemp(Ity_I32);
//..    assign( oldflags, mk_x86g_calculate_eflags_all() );
//..    stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
//..    stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
//..    stmt( IRStmt_Put( OFFB_CC_DEP1,
//..          binop(Iop_Or32,
//..                binop(Iop_And32, mkexpr(oldflags), mkU32(X86G_CC_MASK_O)),
//..                binop(Iop_And32, 
//..                      binop(Iop_Shr32, getIReg(4, R_EAX), mkU8(8)),
//..                      mkU32(mask_SZACP))
//..               )
//..    ));
//.. }
//.. 
//.. 
//.. //-- static 
//.. //-- void codegen_LAHF ( UCodeBlock* cb )
//.. //-- {
//.. //--    Int t = newTemp(cb);
//.. //-- 
//.. //--    /* Pushed arg is ignored, it just provides somewhere to put the
//.. //--       return value. */
//.. //--    uInstr2(cb, GET,   4, ArchReg, R_EAX, TempReg, t);
//.. //--    uInstr0(cb, CALLM_S, 0);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, t);
//.. //--    uInstr1(cb, CALLM, 0, Lit16,   VGOFF_(helper_LAHF));
//.. //--    uFlagsRWU(cb, FlagsSZACP, FlagsEmpty, FlagsEmpty);
//.. //--    uInstr1(cb, POP,   4, TempReg, t);
//.. //--    uInstr0(cb, CALLM_E, 0);
//.. //-- 
//.. //--    /* At this point, the %ah sub-register in %eax has been updated,
//.. //--       the rest is the same, so do a PUT of the whole thing. */
//.. //--    uInstr2(cb, PUT,   4,  TempReg, t,   ArchReg, R_EAX);
//.. //-- }
//.. //-- 

static
ULong dis_cmpxchg_G_E ( Prefix      pfx,
                        Int         size, 
                        ULong       delta0 )
{
   HChar dis_buf[50];
   Int   len;

   IRType ty    = szToITy(size);
   IRTemp acc   = newTemp(ty);
   IRTemp src   = newTemp(ty);
   IRTemp dest  = newTemp(ty);
   IRTemp dest2 = newTemp(ty);
   IRTemp acc2  = newTemp(ty);
   IRTemp cond8 = newTemp(Ity_I8);
   IRTemp addr  = IRTemp_INVALID;
   UChar  rm    = getUChar(delta0);

   if (epartIsReg(rm)) {
      vassert(0); /* awaiting test case */
      assign( dest, getIRegE(size, pfx, rm) );
      delta0++;
      DIP("cmpxchg%c %s,%s\n", nameISize(size),
                               nameIRegG(size,pfx,rm),
                               nameIRegE(size,pfx,rm) );
   } else {
      addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      assign( dest, loadLE(ty, mkexpr(addr)) );
      delta0 += len;
      DIP("cmpxchg%c %s,%s\n", nameISize(size), 
                               nameIRegG(size,pfx,rm), dis_buf);
   }

   assign( src, getIRegG(size, pfx, rm) );
   assign( acc, getIRegRAX(size) );
   setFlags_DEP1_DEP2(Iop_Sub8, acc, dest, ty);
   assign( cond8, unop(Iop_1Uto8, mk_amd64g_calculate_condition(AMD64CondZ)) );
   assign( dest2, IRExpr_Mux0X(mkexpr(cond8), mkexpr(dest), mkexpr(src)) );
   assign( acc2,  IRExpr_Mux0X(mkexpr(cond8), mkexpr(dest), mkexpr(acc)) );
   putIRegRAX(size, mkexpr(acc2));

   if (epartIsReg(rm)) {
      putIRegE(size, pfx, rm, mkexpr(dest2));
   } else {
      storeLE( mkexpr(addr), mkexpr(dest2) );
   }

   return delta0;
}


//.. //-- static
//.. //-- Addr dis_cmpxchg8b ( UCodeBlock* cb, 
//.. //--                      UChar       sorb,
//.. //--                      Addr        eip0 )
//.. //-- {
//.. //--    Int   tal, tah, junkl, junkh, destl, desth, srcl, srch, accl, acch;
//.. //--    HChar dis_buf[50];
//.. //--    UChar rm;
//.. //--    UInt  pair;
//.. //-- 
//.. //--    rm    = getUChar(eip0);
//.. //--    accl  = newTemp(cb);
//.. //--    acch  = newTemp(cb);
//.. //--    srcl  = newTemp(cb);
//.. //--    srch  = newTemp(cb);
//.. //--    destl = newTemp(cb);
//.. //--    desth = newTemp(cb);
//.. //--    junkl = newTemp(cb);
//.. //--    junkh = newTemp(cb);
//.. //-- 
//.. //--    vg_assert(!epartIsReg(rm));
//.. //-- 
//.. //--    pair = disAMode ( cb, sorb, eip0, dis_buf );
//.. //--    tal = LOW24(pair);
//.. //--    tah = newTemp(cb);
//.. //--    uInstr2(cb, MOV, 4, TempReg, tal, TempReg, tah);
//.. //--    uInstr2(cb, ADD, 4, Literal, 0, TempReg, tah);
//.. //--    uLiteral(cb, 4);
//.. //--    eip0 += HI8(pair);
//.. //--    DIP("cmpxchg8b %s\n", dis_buf);
//.. //--    
//.. //--    uInstr0(cb, CALLM_S, 0);
//.. //-- 
//.. //--    uInstr2(cb, LOAD,  4, TempReg, tah, TempReg, desth);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, desth);
//.. //--    uInstr2(cb, LOAD,  4, TempReg, tal, TempReg, destl);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, destl);
//.. //--    uInstr2(cb, GET,   4, ArchReg, R_ECX, TempReg, srch);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, srch);
//.. //--    uInstr2(cb, GET,   4, ArchReg, R_EBX, TempReg, srcl);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, srcl);
//.. //--    uInstr2(cb, GET,   4, ArchReg, R_EDX, TempReg, acch);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, acch);
//.. //--    uInstr2(cb, GET,   4, ArchReg, R_EAX, TempReg, accl);
//.. //--    uInstr1(cb, PUSH,  4, TempReg, accl);
//.. //--    
//.. //--    uInstr1(cb, CALLM, 0, Lit16,   VGOFF_(helper_cmpxchg8b));
//.. //--    uFlagsRWU(cb, FlagsEmpty, FlagZ, FlagsEmpty);
//.. //--    
//.. //--    uInstr1(cb, POP,   4, TempReg, accl);
//.. //--    uInstr2(cb, PUT,   4, TempReg, accl, ArchReg, R_EAX);
//.. //--    uInstr1(cb, POP,   4, TempReg, acch);
//.. //--    uInstr2(cb, PUT,   4, TempReg, acch, ArchReg, R_EDX);
//.. //--    uInstr1(cb, POP,   4, TempReg, srcl);
//.. //--    uInstr2(cb, PUT,   4, TempReg, srcl, ArchReg, R_EBX);
//.. //--    uInstr1(cb, POP,   4, TempReg, srch);
//.. //--    uInstr2(cb, PUT,   4, TempReg, srch, ArchReg, R_ECX);
//.. //--    uInstr1(cb, POP,   4, TempReg, destl);
//.. //--    uInstr2(cb, STORE, 4, TempReg, destl, TempReg, tal);
//.. //--    uInstr1(cb, POP,   4, TempReg, desth);
//.. //--    uInstr2(cb, STORE, 4, TempReg, desth, TempReg, tah);
//.. //-- 
//.. //--    uInstr0(cb, CALLM_E, 0);
//.. //--    
//.. //--    return eip0;
//.. //-- }


/* Handle conditional move instructions of the form
      cmovcc E(reg-or-mem), G(reg)

   E(src) is reg-or-mem
   G(dst) is reg.

   If E is reg, -->    GET %E, tmps
                       GET %G, tmpd
                       CMOVcc tmps, tmpd
                       PUT tmpd, %G
 
   If E is mem  -->    (getAddr E) -> tmpa
                       LD (tmpa), tmps
                       GET %G, tmpd
                       CMOVcc tmps, tmpd
                       PUT tmpd, %G
*/
static
ULong dis_cmov_E_G ( Prefix        pfx,
                     Int           sz, 
                     AMD64Condcode cond,
                     ULong         delta0 )
{
   UChar rm  = getUChar(delta0);
   HChar dis_buf[50];
   Int   len;

   IRType ty   = szToITy(sz);
   IRTemp tmps = newTemp(ty);
   IRTemp tmpd = newTemp(ty);

   if (epartIsReg(rm)) {
      assign( tmps, getIRegE(sz, pfx, rm) );
      assign( tmpd, getIRegG(sz, pfx, rm) );

      putIRegG( sz, pfx, rm,
                IRExpr_Mux0X( unop(Iop_1Uto8,
                                   mk_amd64g_calculate_condition(cond)),
                              mkexpr(tmpd),
                              mkexpr(tmps) )
              );
      DIP("cmov%s %s,%s\n", name_AMD64Condcode(cond),
                            nameIRegE(sz,pfx,rm),
                            nameIRegG(sz,pfx,rm));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      IRTemp addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      assign( tmps, loadLE(ty, mkexpr(addr)) );
      assign( tmpd, getIRegG(sz, pfx, rm) );

      putIRegG( sz, pfx, rm,
                IRExpr_Mux0X( unop(Iop_1Uto8,
                                   mk_amd64g_calculate_condition(cond)),
                              mkexpr(tmpd),
                              mkexpr(tmps) )
              );

      DIP("cmov%s %s,%s\n", name_AMD64Condcode(cond),
                            dis_buf,
                            nameIRegG(sz,pfx,rm));
      return len+delta0;
   }
}


static
ULong dis_xadd_G_E ( /*OUT*/Bool* decode_ok,
                     Prefix pfx, Int sz, ULong delta0 )
{
   Int   len;
   UChar rm = getUChar(delta0);
   HChar dis_buf[50];

   IRType ty    = szToITy(sz);
   IRTemp tmpd  = newTemp(ty);
   IRTemp tmpt0 = newTemp(ty);
   IRTemp tmpt1 = newTemp(ty);
   *decode_ok = True;

   if (epartIsReg(rm)) {
      *decode_ok = False;
      return delta0;
   } else {
      IRTemp addr = disAMode ( &len, pfx, delta0, dis_buf, 0 );
      assign( tmpd,  loadLE(ty, mkexpr(addr)) );
      assign( tmpt0, getIRegG(sz, pfx, rm) );
      assign( tmpt1, binop(mkSizedOp(ty,Iop_Add8), mkexpr(tmpd), mkexpr(tmpt0)) );
      setFlags_DEP1_DEP2( Iop_Add8, tmpd, tmpt0, ty );
      storeLE( mkexpr(addr), mkexpr(tmpt1) );
      putIRegG(sz, pfx, rm, mkexpr(tmpd));
      DIP("xadd%c %s, %s\n",
          nameISize(sz), nameIRegG(sz,pfx,rm), dis_buf);
      return len+delta0;
   }
}

//.. /* Move 16 bits from Ew (ireg or mem) to G (a segment register). */
//.. 
//.. static
//.. UInt dis_mov_Ew_Sw ( UChar sorb, ULong delta0 )
//.. {
//..    Int    len;
//..    IRTemp addr;
//..    UChar  rm  = getUChar(delta0);
//..    HChar  dis_buf[50];
//.. 
//..    if (epartIsReg(rm)) {
//..       putSReg( gregOfRM(rm), getIReg(2, eregOfRM(rm)) );
//..       DIP("movw %s,%s\n", nameIReg(2,eregOfRM(rm)), nameSReg(gregOfRM(rm)));
//..       return 1+delta0;
//..    } else {
//..       addr = disAMode ( &len, sorb, delta0, dis_buf );
//..       putSReg( gregOfRM(rm), loadLE(Ity_I16, mkexpr(addr)) );
//..       DIP("movw %s,%s\n", dis_buf, nameSReg(gregOfRM(rm)));
//..       return len+delta0;
//..    }
//.. }
//.. 
//.. /* Move 16 bits from G (a segment register) to Ew (ireg or mem).  If
//..    dst is ireg and sz==4, zero out top half of it.  */
//.. 
//.. static
//.. UInt dis_mov_Sw_Ew ( UChar sorb,
//..                      Int   sz,
//..                      UInt  delta0 )
//.. {
//..    Int    len;
//..    IRTemp addr;
//..    UChar  rm  = getUChar(delta0);
//..    HChar  dis_buf[50];
//.. 
//..    vassert(sz == 2 || sz == 4);
//.. 
//..    if (epartIsReg(rm)) {
//..       if (sz == 4)
//..          putIReg(4, eregOfRM(rm), unop(Iop_16Uto32, getSReg(gregOfRM(rm))));
//..       else
//..          putIReg(2, eregOfRM(rm), getSReg(gregOfRM(rm)));
//.. 
//..       DIP("mov %s,%s\n", nameSReg(gregOfRM(rm)), nameIReg(sz,eregOfRM(rm)));
//..       return 1+delta0;
//..    } else {
//..       addr = disAMode ( &len, sorb, delta0, dis_buf );
//..       storeLE( mkexpr(addr), getSReg(gregOfRM(rm)) );
//..       DIP("mov %s,%s\n", nameSReg(gregOfRM(rm)), dis_buf);
//..       return len+delta0;
//..    }
//.. }
//.. 
//.. 
//.. static 
//.. void dis_push_segreg ( UInt sreg, Int sz )
//.. {
//..     IRTemp t1 = newTemp(Ity_I16);
//..     IRTemp ta = newTemp(Ity_I32);
//..     vassert(sz == 2 || sz == 4);
//.. 
//..     assign( t1, getSReg(sreg) );
//..     assign( ta, binop(Iop_Sub32, getIReg(4, R_ESP), mkU32(sz)) );
//..     putIReg(4, R_ESP, mkexpr(ta));
//..     storeLE( mkexpr(ta), mkexpr(t1) );
//.. 
//..     DIP("pushw %s\n", nameSReg(sreg));
//.. }
//.. 
//.. static
//.. void dis_pop_segreg ( UInt sreg, Int sz )
//.. {
//..     IRTemp t1 = newTemp(Ity_I16);
//..     IRTemp ta = newTemp(Ity_I32);
//..     vassert(sz == 2 || sz == 4);
//.. 
//..     assign( ta, getIReg(4, R_ESP) );
//..     assign( t1, loadLE(Ity_I16, mkexpr(ta)) );
//.. 
//..     putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(ta), mkU32(sz)) );
//..     putSReg( sreg, mkexpr(t1) );
//..     DIP("pop %s\n", nameSReg(sreg));
//.. }

static
void dis_ret ( ULong d64 )
{
   IRTemp t1 = newTemp(Ity_I64); 
   IRTemp t2 = newTemp(Ity_I64);
   assign(t1, getIReg64(R_RSP));
   assign(t2, loadLE(Ity_I64,mkexpr(t1)));
   putIReg64(R_RSP, binop(Iop_Add64, mkexpr(t1), mkU64(8+d64)));
   jmp_treg(Ijk_Ret,t2);
}


/*------------------------------------------------------------*/
/*--- SSE/SSE2/SSE3 helpers                                ---*/
/*------------------------------------------------------------*/

/* Worker function; do not call directly. 
   Handles full width G = G `op` E   and   G = (not G) `op` E.
*/

static ULong dis_SSE_E_to_G_all_wrk ( 
                Prefix pfx, ULong delta, 
                HChar* opname, IROp op,
                Bool   invertG
             )
{
   HChar   dis_buf[50];
   Int     alen;
   IRTemp  addr;
   UChar   rm = getUChar(delta);
   IRExpr* gpart
      = invertG ? unop(Iop_NotV128, getXMMReg(gregOfRexRM(pfx,rm)))
                : getXMMReg(gregOfRexRM(pfx,rm));
   if (epartIsReg(rm)) {
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(op, gpart,
                           getXMMReg(eregOfRexRM(pfx,rm))) );
      DIP("%s %s,%s\n", opname,
                        nameXMMReg(eregOfRexRM(pfx,rm)),
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+1;
   } else {
      addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(op, gpart,
                           loadLE(Ity_V128, mkexpr(addr))) );
      DIP("%s %s,%s\n", opname,
                        dis_buf,
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+alen;
   }
}


/* All lanes SSE binary operation, G = G `op` E. */

static
ULong dis_SSE_E_to_G_all ( Prefix pfx, ULong delta, 
                           HChar* opname, IROp op )
{
   return dis_SSE_E_to_G_all_wrk( pfx, delta, opname, op, False );
}

/* All lanes SSE binary operation, G = (not G) `op` E. */

static
ULong dis_SSE_E_to_G_all_invG ( Prefix pfx, ULong delta, 
                                HChar* opname, IROp op )
{
   return dis_SSE_E_to_G_all_wrk( pfx, delta, opname, op, True );
}


/* Lowest 32-bit lane only SSE binary operation, G = G `op` E. */

static ULong dis_SSE_E_to_G_lo32 ( Prefix pfx, ULong delta, 
                                   HChar* opname, IROp op )
{
   HChar   dis_buf[50];
   Int     alen;
   IRTemp  addr;
   UChar   rm = getUChar(delta);
   IRExpr* gpart = getXMMReg(gregOfRexRM(pfx,rm));
   if (epartIsReg(rm)) {
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(op, gpart,
                           getXMMReg(eregOfRexRM(pfx,rm))) );
      DIP("%s %s,%s\n", opname,
                        nameXMMReg(eregOfRexRM(pfx,rm)),
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+1;
   } else {
      /* We can only do a 32-bit memory read, so the upper 3/4 of the
         E operand needs to be made simply of zeroes. */
      IRTemp epart = newTemp(Ity_V128);
      addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
      assign( epart, unop( Iop_32UtoV128,
                           loadLE(Ity_I32, mkexpr(addr))) );
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(op, gpart, mkexpr(epart)) );
      DIP("%s %s,%s\n", opname,
                        dis_buf,
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+alen;
   }
}


/* Lower 64-bit lane only SSE binary operation, G = G `op` E. */

static ULong dis_SSE_E_to_G_lo64 ( Prefix pfx, ULong delta, 
                                   HChar* opname, IROp op )
{
   HChar   dis_buf[50];
   Int     alen;
   IRTemp  addr;
   UChar   rm = getUChar(delta);
   IRExpr* gpart = getXMMReg(gregOfRexRM(pfx,rm));
   if (epartIsReg(rm)) {
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(op, gpart,
                           getXMMReg(eregOfRexRM(pfx,rm))) );
      DIP("%s %s,%s\n", opname,
                        nameXMMReg(eregOfRexRM(pfx,rm)),
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+1;
   } else {
      /* We can only do a 64-bit memory read, so the upper half of the
         E operand needs to be made simply of zeroes. */
      IRTemp epart = newTemp(Ity_V128);
      addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
      assign( epart, unop( Iop_64UtoV128,
                           loadLE(Ity_I64, mkexpr(addr))) );
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(op, gpart, mkexpr(epart)) );
      DIP("%s %s,%s\n", opname,
                        dis_buf,
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+alen;
   }
}


//.. /* All lanes unary SSE operation, G = op(E). */
//.. 
//.. static UInt dis_SSE_E_to_G_unary_all ( 
//..                UChar sorb, ULong delta, 
//..                HChar* opname, IROp op
//..             )
//.. {
//..    HChar   dis_buf[50];
//..    Int     alen;
//..    IRTemp  addr;
//..    UChar   rm = getUChar(delta);
//..    if (epartIsReg(rm)) {
//..       putXMMReg( gregOfRM(rm), 
//..                  unop(op, getXMMReg(eregOfRM(rm))) );
//..       DIP("%s %s,%s\n", opname,
//..                         nameXMMReg(eregOfRM(rm)),
//..                         nameXMMReg(gregOfRM(rm)) );
//..       return delta+1;
//..    } else {
//..       addr = disAMode ( &alen, sorb, delta, dis_buf );
//..       putXMMReg( gregOfRM(rm), 
//..                  unop(op, loadLE(Ity_V128, mkexpr(addr))) );
//..       DIP("%s %s,%s\n", opname,
//..                         dis_buf,
//..                         nameXMMReg(gregOfRM(rm)) );
//..       return delta+alen;
//..    }
//.. }
//.. 
//.. 
//.. /* Lowest 32-bit lane only unary SSE operation, G = op(E). */
//.. 
//.. static UInt dis_SSE_E_to_G_unary_lo32 ( 
//..                UChar sorb, ULong delta, 
//..                HChar* opname, IROp op
//..             )
//.. {
//..    /* First we need to get the old G value and patch the low 32 bits
//..       of the E operand into it.  Then apply op and write back to G. */
//..    HChar   dis_buf[50];
//..    Int     alen;
//..    IRTemp  addr;
//..    UChar   rm = getUChar(delta);
//..    IRTemp  oldG0 = newTemp(Ity_V128);
//..    IRTemp  oldG1 = newTemp(Ity_V128);
//.. 
//..    assign( oldG0, getXMMReg(gregOfRM(rm)) );
//.. 
//..    if (epartIsReg(rm)) {
//..       assign( oldG1, 
//..               binop( Iop_Set128lo32,
//..                      mkexpr(oldG0),
//..                      getXMMRegLane32(eregOfRM(rm), 0)) );
//..       putXMMReg( gregOfRM(rm), unop(op, mkexpr(oldG1)) );
//..       DIP("%s %s,%s\n", opname,
//..                         nameXMMReg(eregOfRM(rm)),
//..                         nameXMMReg(gregOfRM(rm)) );
//..       return delta+1;
//..    } else {
//..       addr = disAMode ( &alen, sorb, delta, dis_buf );
//..       assign( oldG1, 
//..               binop( Iop_Set128lo32,
//..                      mkexpr(oldG0),
//..                      loadLE(Ity_I32, mkexpr(addr)) ));
//..       putXMMReg( gregOfRM(rm), unop(op, mkexpr(oldG1)) );
//..       DIP("%s %s,%s\n", opname,
//..                         dis_buf,
//..                         nameXMMReg(gregOfRM(rm)) );
//..       return delta+alen;
//..    }
//.. }


/* Lowest 64-bit lane only unary SSE operation, G = op(E). */

static ULong dis_SSE_E_to_G_unary_lo64 ( 
                Prefix pfx, ULong delta, 
                HChar* opname, IROp op
             )
{
   /* First we need to get the old G value and patch the low 64 bits
      of the E operand into it.  Then apply op and write back to G. */
   HChar   dis_buf[50];
   Int     alen;
   IRTemp  addr;
   UChar   rm = getUChar(delta);
   IRTemp  oldG0 = newTemp(Ity_V128);
   IRTemp  oldG1 = newTemp(Ity_V128);

   assign( oldG0, getXMMReg(gregOfRexRM(pfx,rm)) );

   if (epartIsReg(rm)) {
      assign( oldG1, 
              binop( Iop_SetV128lo64,
                     mkexpr(oldG0),
                     getXMMRegLane64(eregOfRexRM(pfx,rm), 0)) );
      putXMMReg( gregOfRexRM(pfx,rm), unop(op, mkexpr(oldG1)) );
      DIP("%s %s,%s\n", opname,
                        nameXMMReg(eregOfRexRM(pfx,rm)),
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+1;
   } else {
      addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
      assign( oldG1, 
              binop( Iop_SetV128lo64,
                     mkexpr(oldG0),
                     loadLE(Ity_I64, mkexpr(addr)) ));
      putXMMReg( gregOfRexRM(pfx,rm), unop(op, mkexpr(oldG1)) );
      DIP("%s %s,%s\n", opname,
                        dis_buf,
                        nameXMMReg(gregOfRexRM(pfx,rm)) );
      return delta+alen;
   }
}


//.. /* SSE integer binary operation:
//..       G = G `op` E   (eLeft == False)
//..       G = E `op` G   (eLeft == True)
//.. */
//.. static UInt dis_SSEint_E_to_G( 
//..                UChar sorb, ULong delta, 
//..                HChar* opname, IROp op,
//..                Bool   eLeft
//..             )
//.. {
//..    HChar   dis_buf[50];
//..    Int     alen;
//..    IRTemp  addr;
//..    UChar   rm = getUChar(delta);
//..    IRExpr* gpart = getXMMReg(gregOfRM(rm));
//..    IRExpr* epart = NULL;
//..    if (epartIsReg(rm)) {
//..       epart = getXMMReg(eregOfRM(rm));
//..       DIP("%s %s,%s\n", opname,
//..                         nameXMMReg(eregOfRM(rm)),
//..                         nameXMMReg(gregOfRM(rm)) );
//..       delta += 1;
//..    } else {
//..       addr  = disAMode ( &alen, sorb, delta, dis_buf );
//..       epart = loadLE(Ity_V128, mkexpr(addr));
//..       DIP("%s %s,%s\n", opname,
//..                         dis_buf,
//..                         nameXMMReg(gregOfRM(rm)) );
//..       delta += alen;
//..    }
//..    putXMMReg( gregOfRM(rm), 
//..               eLeft ? binop(op, epart, gpart)
//.. 	            : binop(op, gpart, epart) );
//..    return delta;
//.. }


/* Helper for doing SSE FP comparisons. */

static void findSSECmpOp ( Bool* needNot, IROp* op, 
                           Int imm8, Bool all_lanes, Int sz )
{
   imm8 &= 7;
   *needNot = False;
   *op      = Iop_INVALID;
   if (imm8 >= 4) {
      *needNot = True;
      imm8 -= 4;
   }

   if (sz == 4 && all_lanes) {
      switch (imm8) {
         case 0: *op = Iop_CmpEQ32Fx4; return;
         case 1: *op = Iop_CmpLT32Fx4; return;
         case 2: *op = Iop_CmpLE32Fx4; return;
         case 3: *op = Iop_CmpUN32Fx4; return;
         default: break;
      }
   }
   if (sz == 4 && !all_lanes) {
      switch (imm8) {
         case 0: *op = Iop_CmpEQ32F0x4; return;
         case 1: *op = Iop_CmpLT32F0x4; return;
         case 2: *op = Iop_CmpLE32F0x4; return;
         case 3: *op = Iop_CmpUN32F0x4; return;
         default: break;
      }
   }
   if (sz == 8 && all_lanes) {
      switch (imm8) {
         case 0: *op = Iop_CmpEQ64Fx2; return;
         case 1: *op = Iop_CmpLT64Fx2; return;
         case 2: *op = Iop_CmpLE64Fx2; return;
         case 3: *op = Iop_CmpUN64Fx2; return;
         default: break;
      }
   }
   if (sz == 8 && !all_lanes) {
      switch (imm8) {
         case 0: *op = Iop_CmpEQ64F0x2; return;
         case 1: *op = Iop_CmpLT64F0x2; return;
         case 2: *op = Iop_CmpLE64F0x2; return;
         case 3: *op = Iop_CmpUN64F0x2; return;
         default: break;
      }
   }
   vpanic("findSSECmpOp(amd64,guest)");
}

/* Handles SSE 32F comparisons. */

static ULong dis_SSEcmp_E_to_G ( Prefix pfx, ULong delta, 
                                 HChar* opname, Bool all_lanes, Int sz )
{
   HChar   dis_buf[50];
   Int     alen, imm8;
   IRTemp  addr;
   Bool    needNot = False;
   IROp    op      = Iop_INVALID;
   IRTemp  plain   = newTemp(Ity_V128);
   UChar   rm      = getUChar(delta);
   UShort  mask    = 0;
   vassert(sz == 4 || sz == 8);
   if (epartIsReg(rm)) {
      imm8 = getUChar(delta+1);
      findSSECmpOp(&needNot, &op, imm8, all_lanes, sz);
      assign( plain, binop(op, getXMMReg(gregOfRexRM(pfx,rm)), 
                               getXMMReg(eregOfRexRM(pfx,rm))) );
      delta += 2;
      DIP("%s $%d,%s,%s\n", opname,
                            (Int)imm8,
                            nameXMMReg(eregOfRexRM(pfx,rm)),
                            nameXMMReg(gregOfRexRM(pfx,rm)) );
   } else {
      addr = disAMode ( &alen, pfx, delta, dis_buf, 1 );
      imm8 = getUChar(delta+alen);
      findSSECmpOp(&needNot, &op, imm8, all_lanes, sz);
      assign( plain, binop(op, getXMMReg(gregOfRexRM(pfx,rm)), 
                               loadLE(Ity_V128, mkexpr(addr))) );
      delta += alen+1;
      DIP("%s $%d,%s,%s\n", opname,
                            (Int)imm8,
                            dis_buf,
                            nameXMMReg(gregOfRexRM(pfx,rm)) );
   }

   if (needNot && all_lanes) {
      putXMMReg( gregOfRexRM(pfx,rm), 
                 unop(Iop_NotV128, mkexpr(plain)) );
   }
   else
   if (needNot && !all_lanes) {
      mask = toUShort(sz==4 ? 0x000F : 0x00FF);
      putXMMReg( gregOfRexRM(pfx,rm), 
                 binop(Iop_XorV128, mkexpr(plain), mkV128(mask)) );
   }
   else {
      putXMMReg( gregOfRexRM(pfx,rm), mkexpr(plain) );
   }

   return delta;
}


//.. /* Vector by scalar shift of G by the amount specified at the bottom
//..    of E. */
//.. 
//.. static UInt dis_SSE_shiftG_byE ( UChar sorb, ULong delta, 
//..                                  HChar* opname, IROp op )
//.. {
//..    HChar   dis_buf[50];
//..    Int     alen, size;
//..    IRTemp  addr;
//..    Bool    shl, shr, sar;
//..    UChar   rm   = getUChar(delta);
//..    IRTemp  g0   = newTemp(Ity_V128);
//..    IRTemp  g1   = newTemp(Ity_V128);
//..    IRTemp  amt  = newTemp(Ity_I32);
//..    IRTemp  amt8 = newTemp(Ity_I8);
//..    if (epartIsReg(rm)) {
//..       assign( amt, getXMMRegLane32(eregOfRM(rm), 0) );
//..       DIP("%s %s,%s\n", opname,
//..                         nameXMMReg(eregOfRM(rm)),
//..                         nameXMMReg(gregOfRM(rm)) );
//..       delta++;
//..    } else {
//..       addr = disAMode ( &alen, sorb, delta, dis_buf );
//..       assign( amt, loadLE(Ity_I32, mkexpr(addr)) );
//..       DIP("%s %s,%s\n", opname,
//..                         dis_buf,
//..                         nameXMMReg(gregOfRM(rm)) );
//..       delta += alen;
//..    }
//..    assign( g0,   getXMMReg(gregOfRM(rm)) );
//..    assign( amt8, unop(Iop_32to8, mkexpr(amt)) );
//.. 
//..    shl = shr = sar = False;
//..    size = 0;
//..    switch (op) {
//..       case Iop_ShlN16x8: shl = True; size = 32; break;
//..       case Iop_ShlN32x4: shl = True; size = 32; break;
//..       case Iop_ShlN64x2: shl = True; size = 64; break;
//..       case Iop_SarN16x8: sar = True; size = 16; break;
//..       case Iop_SarN32x4: sar = True; size = 32; break;
//..       case Iop_ShrN16x8: shr = True; size = 16; break;
//..       case Iop_ShrN32x4: shr = True; size = 32; break;
//..       case Iop_ShrN64x2: shr = True; size = 64; break;
//..       default: vassert(0);
//..    }
//.. 
//..    if (shl || shr) {
//..      assign( 
//..         g1,
//..         IRExpr_Mux0X(
//..            unop(Iop_1Uto8,binop(Iop_CmpLT32U,mkexpr(amt),mkU32(size))),
//..            mkV128(0x0000),
//..            binop(op, mkexpr(g0), mkexpr(amt8))
//..         )
//..      );
//..    } else 
//..    if (sar) {
//..      assign( 
//..         g1,
//..         IRExpr_Mux0X(
//..            unop(Iop_1Uto8,binop(Iop_CmpLT32U,mkexpr(amt),mkU32(size))),
//..            binop(op, mkexpr(g0), mkU8(size-1)),
//..            binop(op, mkexpr(g0), mkexpr(amt8))
//..         )
//..      );
//..    } else {
//..       vassert(0);
//..    }
//.. 
//..    putXMMReg( gregOfRM(rm), mkexpr(g1) );
//..    return delta;
//.. }
//.. 
//.. 
//.. /* Vector by scalar shift of E by an immediate byte. */
//.. 
//.. static 
//.. UInt dis_SSE_shiftE_imm ( ULong delta, HChar* opname, IROp op )
//.. {
//..    Bool    shl, shr, sar;
//..    UChar   rm   = getUChar(delta);
//..    IRTemp  e0   = newTemp(Ity_V128);
//..    IRTemp  e1   = newTemp(Ity_V128);
//..    UChar   amt, size;
//..    vassert(epartIsReg(rm));
//..    vassert(gregOfRM(rm) == 2 
//..            || gregOfRM(rm) == 4 || gregOfRM(rm) == 6);
//..    amt = (Int)(getUChar(delta+1));
//..    delta += 2;
//..    DIP("%s $%d,%s\n", opname,
//..                       (Int)amt,
//..                       nameXMMReg(eregOfRM(rm)) );
//..    assign( e0, getXMMReg(eregOfRM(rm)) );
//.. 
//..    shl = shr = sar = False;
//..    size = 0;
//..    switch (op) {
//..       case Iop_ShlN16x8: shl = True; size = 16; break;
//..       case Iop_ShlN32x4: shl = True; size = 32; break;
//..       case Iop_ShlN64x2: shl = True; size = 64; break;
//..       case Iop_SarN16x8: sar = True; size = 16; break;
//..       case Iop_SarN32x4: sar = True; size = 32; break;
//..       case Iop_ShrN16x8: shr = True; size = 16; break;
//..       case Iop_ShrN32x4: shr = True; size = 32; break;
//..       case Iop_ShrN64x2: shr = True; size = 64; break;
//..       default: vassert(0);
//..    }
//.. 
//..    if (shl || shr) {
//..      assign( e1, amt >= size 
//..                     ? mkV128(0x0000)
//..                     : binop(op, mkexpr(e0), mkU8(amt))
//..      );
//..    } else 
//..    if (sar) {
//..      assign( e1, amt >= size 
//..                     ? binop(op, mkexpr(e0), mkU8(size-1))
//..                     : binop(op, mkexpr(e0), mkU8(amt))
//..      );
//..    } else {
//..       vassert(0);
//..    }
//.. 
//..    putXMMReg( eregOfRM(rm), mkexpr(e1) );
//..    return delta;
//.. }


/* Get the current SSE rounding mode. */

static IRExpr* /* :: Ity_I32 */ get_sse_roundingmode ( void )
{
   return 
      unop( Iop_64to32, 
            binop( Iop_And64, 
                   IRExpr_Get( OFFB_SSEROUND, Ity_I64 ), 
                   mkU64(3) ));
}

static void put_sse_roundingmode ( IRExpr* sseround )
{
   vassert(typeOfIRExpr(irbb->tyenv, sseround) == Ity_I32);
   stmt( IRStmt_Put( OFFB_SSEROUND, 
                     unop(Iop_32Uto64,sseround) ) );
}

//.. /* Break a 128-bit value up into four 32-bit ints. */
//.. 
//.. static void breakup128to32s ( IRTemp t128,
//.. 			      /*OUTs*/
//..                               IRTemp* t3, IRTemp* t2,
//..                               IRTemp* t1, IRTemp* t0 )
//.. {
//..    IRTemp hi64 = newTemp(Ity_I64);
//..    IRTemp lo64 = newTemp(Ity_I64);
//..    assign( hi64, unop(Iop_128HIto64, mkexpr(t128)) );
//..    assign( lo64, unop(Iop_128to64,   mkexpr(t128)) );
//.. 
//..    vassert(t0 && *t0 == IRTemp_INVALID);
//..    vassert(t1 && *t1 == IRTemp_INVALID);
//..    vassert(t2 && *t2 == IRTemp_INVALID);
//..    vassert(t3 && *t3 == IRTemp_INVALID);
//.. 
//..    *t0 = newTemp(Ity_I32);
//..    *t1 = newTemp(Ity_I32);
//..    *t2 = newTemp(Ity_I32);
//..    *t3 = newTemp(Ity_I32);
//..    assign( *t0, unop(Iop_64to32,   mkexpr(lo64)) );
//..    assign( *t1, unop(Iop_64HIto32, mkexpr(lo64)) );
//..    assign( *t2, unop(Iop_64to32,   mkexpr(hi64)) );
//..    assign( *t3, unop(Iop_64HIto32, mkexpr(hi64)) );
//.. }
//.. 
//.. /* Construct a 128-bit value from four 32-bit ints. */
//.. 
//.. static IRExpr* mk128from32s ( IRTemp t3, IRTemp t2,
//..                               IRTemp t1, IRTemp t0 )
//.. {
//..    return
//..       binop( Iop_64HLto128,
//..              binop(Iop_32HLto64, mkexpr(t3), mkexpr(t2)),
//..              binop(Iop_32HLto64, mkexpr(t1), mkexpr(t0))
//..    );
//.. }
//.. 
//.. /* Break a 64-bit value up into four 16-bit ints. */
//.. 
//.. static void breakup64to16s ( IRTemp t64,
//..                              /*OUTs*/
//..                              IRTemp* t3, IRTemp* t2,
//..                              IRTemp* t1, IRTemp* t0 )
//.. {
//..    IRTemp hi32 = newTemp(Ity_I32);
//..    IRTemp lo32 = newTemp(Ity_I32);
//..    assign( hi32, unop(Iop_64HIto32, mkexpr(t64)) );
//..    assign( lo32, unop(Iop_64to32,   mkexpr(t64)) );
//.. 
//..    vassert(t0 && *t0 == IRTemp_INVALID);
//..    vassert(t1 && *t1 == IRTemp_INVALID);
//..    vassert(t2 && *t2 == IRTemp_INVALID);
//..    vassert(t3 && *t3 == IRTemp_INVALID);
//.. 
//..    *t0 = newTemp(Ity_I16);
//..    *t1 = newTemp(Ity_I16);
//..    *t2 = newTemp(Ity_I16);
//..    *t3 = newTemp(Ity_I16);
//..    assign( *t0, unop(Iop_32to16,   mkexpr(lo32)) );
//..    assign( *t1, unop(Iop_32HIto16, mkexpr(lo32)) );
//..    assign( *t2, unop(Iop_32to16,   mkexpr(hi32)) );
//..    assign( *t3, unop(Iop_32HIto16, mkexpr(hi32)) );
//.. }
//.. 
//.. /* Construct a 64-bit value from four 16-bit ints. */
//.. 
//.. static IRExpr* mk64from16s ( IRTemp t3, IRTemp t2,
//..                              IRTemp t1, IRTemp t0 )
//.. {
//..    return
//..       binop( Iop_32HLto64,
//..              binop(Iop_16HLto32, mkexpr(t3), mkexpr(t2)),
//..              binop(Iop_16HLto32, mkexpr(t1), mkexpr(t0))
//..    );
//.. }


/*------------------------------------------------------------*/
/*--- Disassemble a single instruction                     ---*/
/*------------------------------------------------------------*/

/* Disassemble a single instruction into IR.  The instruction
   is located in host memory at &guest_code[delta].
   Set *size to be the size of the instruction.
   If the returned value is Dis_Resteer,
   the next guest address is assigned to *whereNext.  If resteerOK
   is False, disInstr may not return Dis_Resteer. */
   
static 
DisResult disInstr ( /*IN*/  Bool       resteerOK,
                     /*IN*/  Bool       (*resteerOkFn) ( Addr64 ),
                     /*IN*/  ULong      delta, 
                     /*IN*/  VexSubArch subarch,
                     /*OUT*/ Long*      size,
                     /*OUT*/ Addr64*    whereNext )
{
   IRType    ty;
   IRTemp    addr, /* t0, */ t1, t2, t3, t4 /*, t5, t6 */;
   Int       alen;
   UChar     opc, modrm, /*abyte,*/ pre;
   Long      d64;
   HChar     dis_buf[50];
   Int       am_sz, d_sz, n, n_prefixes;
   DisResult whatNext = Dis_Continue;
   UChar*    insn; /* used in SSE decoders */

   /* Holds eip at the start of the insn, so that we can print
      consistent error messages for unimplemented insns. */
   ULong delta_start = delta;

   /* sz denotes the nominal data-op size of the insn; we change it to
      2 if an 0x66 prefix is seen and 8 if REX.W is 1.  In case of
      conflict REX.W takes precedence. */
   Int sz = 4;

   /* pfx holds the summary of prefixes. */
   Prefix pfx = PFX_EMPTY;

   /* If we don't set *size properly, this causes bbToIR_AMD64Instr to
      assert. */
   *size = 0;

   vassert(guest_rip_next_assumed == 0);
   vassert(guest_rip_next_mustcheck == False);

   addr = /* t0 = */ t1 = t2 = t3 = t4 = /* t5 = t6 = */ IRTemp_INVALID; 

   DIP("\t0x%llx:  ", guest_rip_bbstart+delta);

   /* Spot the client-request magic sequence. */
   {
      UChar* code = (UChar*)(guest_code + delta);
      /* Spot this:
         C1C01D                roll $29, %eax
         C1C003                roll $3,  %eax
         C1C81B                rorl $27, %eax
         C1C805                rorl $5,  %eax
         C1C00D                roll $13, %eax
         C1C013                roll $19, %eax      
      */
      if (code[ 0] == 0xC1 && code[ 1] == 0xC0 && code[ 2] == 0x1D &&
          code[ 3] == 0xC1 && code[ 4] == 0xC0 && code[ 5] == 0x03 &&
          code[ 6] == 0xC1 && code[ 7] == 0xC8 && code[ 8] == 0x1B &&
          code[ 9] == 0xC1 && code[10] == 0xC8 && code[11] == 0x05 &&
          code[12] == 0xC1 && code[13] == 0xC0 && code[14] == 0x0D &&
          code[15] == 0xC1 && code[16] == 0xC0 && code[17] == 0x13
         ) {
         DIP("%%edx = client_request ( %%eax )\n");         
         delta += 18;
         jmp_lit(Ijk_ClientReq, guest_rip_bbstart+delta);
         whatNext = Dis_StopHere;
         goto decode_success;
      }
   }

   /* Eat prefixes, summarising the result in pfx and sz, and rejecting
      as many invalid combinations as possible. */
   n_prefixes = 0;
   while (True) {
      if (n_prefixes > 5) goto decode_failure;
      pre = getUChar(delta);
      switch (pre) {
         case 0x66: pfx |= PFX_66; break;
         case 0x67: pfx |= PFX_ASO; break;
         case 0xF2: pfx |= PFX_F2; break;
         case 0xF3: pfx |= PFX_F3; break;
         case 0xF0: pfx |= PFX_LOCK; break;
         case 0x2E: pfx |= PFX_CS; break;
         case 0x3E: pfx |= PFX_DS; break;
         case 0x26: pfx |= PFX_ES; break;
         case 0x64: pfx |= PFX_FS; break;
         case 0x65: pfx |= PFX_GS; break;
         case 0x36: pfx |= PFX_SS; break;
         case 0x40 ... 0x4F:
            pfx |= PFX_REX;
            if (pre & (1<<3)) pfx |= PFX_REXW;
            if (pre & (1<<2)) pfx |= PFX_REXR;
            if (pre & (1<<1)) pfx |= PFX_REXX;
            if (pre & (1<<0)) pfx |= PFX_REXB;
            break;
         default: 
            goto not_a_prefix;
      }
      n_prefixes++;
      delta++;
   }

   not_a_prefix:
   /* Dump invalid combinations */
   if (pfx & PFX_ASO) 
      goto decode_failure; /* don't support address-size override */

   n = 0;
   if (pfx & PFX_F2) n++;
   if (pfx & PFX_F3) n++;
   if (n > 1) 
      goto decode_failure; /* can't have both */

   n = 0;
   if (pfx & PFX_CS) n++;
   if (pfx & PFX_DS) n++;
   if (pfx & PFX_ES) n++;
   if (pfx & PFX_FS) n++;
   if (pfx & PFX_GS) n++;
   if (pfx & PFX_SS) n++;
   if (n > 1) 
      goto decode_failure; /* multiple seg overrides == illegal */

   /* Set up sz. */
   sz = 4;
   if (pfx & PFX_66) sz = 2;
   if ((pfx & PFX_REX) && (pfx & PFX_REXW)) sz = 8;

   /* Kludge re LOCK prefixes.  We assume here that all code generated
      by Vex is going to be run in a single-threaded context, in other
      words that concurrent executions of Vex-generated translations
      will not happen.  That is certainly the case for how the
      Valgrind-3.0 code line uses Vex.  Given that assumption, it
      seems safe to ignore LOCK prefixes since there will never be any
      other thread running at the same time as this one.  However, at
      least emit a memory fence on the basis that it would at least be
      prudent to flush any memory transactions from this thread as far
      as possible down the memory hierarchy. */
   if (pfx & PFX_LOCK) {
      /* vex_printf("vex amd64->IR: ignoring LOCK prefix on: ");
         insn_verbose = True; */
      stmt( IRStmt_MFence() );
   }


   /* ---------------------------------------------------- */
   /* --- The SSE decoder.                             --- */
   /* ---------------------------------------------------- */

   /* What did I do to deserve SSE ?  Perhaps I was really bad in a
      previous life? */

   /* Note, this doesn't handle SSE2 or SSE3.  That is handled in a
      later section, further on. */

   insn = (UChar*)&guest_code[delta];

//..    /* Treat fxsave specially.  It should be doable even on an SSE0
//..       (Pentium-II class) CPU.  Hence be prepared to handle it on
//..       any subarchitecture variant.
//..    */
//.. 
//..    /* 0F AE /0 = FXSAVE m512 -- write x87 and SSE state to memory */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xAE
//..        && !epartIsReg(insn[2]) && gregOfRM(insn[2]) == 0) {
//..       modrm = getUChar(delta+2);
//..       vassert(sz == 4);
//..       vassert(!epartIsReg(modrm));
//.. 
//..       addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..       delta += 2+alen;
//.. 
//..       DIP("fxsave %s\n", dis_buf);
//.. 
//..       /* Uses dirty helper: 
//..             void x86g_do_FXSAVE ( VexGuestX86State*, UInt ) */
//..       IRDirty* d = unsafeIRDirty_0_N ( 
//..                       0/*regparms*/, 
//..                       "x86g_dirtyhelper_FXSAVE", 
//..                       &x86g_dirtyhelper_FXSAVE,
//..                       mkIRExprVec_1( mkexpr(addr) )
//..                    );
//..       d->needsBBP = True;
//.. 
//..       /* declare we're writing memory */
//..       d->mFx   = Ifx_Write;
//..       d->mAddr = mkexpr(addr);
//..       d->mSize = 512;
//.. 
//..       /* declare we're reading guest state */
//..       d->nFxState = 7;
//.. 
//..       d->fxState[0].fx     = Ifx_Read;
//..       d->fxState[0].offset = OFFB_FTOP;
//..       d->fxState[0].size   = sizeof(UInt);
//.. 
//..       d->fxState[1].fx     = Ifx_Read;
//..       d->fxState[1].offset = OFFB_FPREGS;
//..       d->fxState[1].size   = 8 * sizeof(ULong);
//.. 
//..       d->fxState[2].fx     = Ifx_Read;
//..       d->fxState[2].offset = OFFB_FPTAGS;
//..       d->fxState[2].size   = 8 * sizeof(UChar);
//.. 
//..       d->fxState[3].fx     = Ifx_Read;
//..       d->fxState[3].offset = OFFB_FPROUND;
//..       d->fxState[3].size   = sizeof(UInt);
//.. 
//..       d->fxState[4].fx     = Ifx_Read;
//..       d->fxState[4].offset = OFFB_FC3210;
//..       d->fxState[4].size   = sizeof(UInt);
//.. 
//..       d->fxState[5].fx     = Ifx_Read;
//..       d->fxState[5].offset = OFFB_XMM0;
//..       d->fxState[5].size   = 8 * sizeof(U128);
//.. 
//..       d->fxState[6].fx     = Ifx_Read;
//..       d->fxState[6].offset = OFFB_SSEROUND;
//..       d->fxState[6].size   = sizeof(UInt);
//.. 
//..       /* Be paranoid ... this assertion tries to ensure the 8 %xmm
//.. 	 images are packed back-to-back.  If not, the value of
//.. 	 d->fxState[5].size is wrong. */
//..       vassert(16 == sizeof(U128));
//..       vassert(OFFB_XMM7 == (OFFB_XMM0 + 7 * 16));
//.. 
//..       stmt( IRStmt_Dirty(d) );
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* ------ SSE decoder main ------ */
//.. 
//..    /* Skip parts of the decoder which don't apply given the stated
//..       guest subarchitecture. */
//..    if (subarch == VexSubArchX86_sse0)
//..       goto after_sse_decoders;
//..    
//..    /* Otherwise we must be doing sse1 or sse2, so we can at least try
//..       for SSE1 here. */
//.. 
//..    /* 0F 58 = ADDPS -- add 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x58) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "addps", Iop_Add32Fx4 );
//..       goto decode_success;
//..    }

   /* F3 0F 58 = ADDSS -- add 32F0x4 from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x58) {
      delta = dis_SSE_E_to_G_lo32( pfx, delta+2, "addss", Iop_Add32F0x4 );
      goto decode_success;
   }

   /* 0F 55 = ANDNPS -- G = (not G) and E */
   if (haveNo66noF2noF3(pfx) && sz == 4 
       && insn[0] == 0x0F && insn[1] == 0x55) {
      delta = dis_SSE_E_to_G_all_invG( pfx, delta+2, "andnps", Iop_AndV128 );
      goto decode_success;
   }

   /* 0F 54 = ANDPS -- G = G and E */
   if (haveNo66noF2noF3(pfx) && sz == 4 
       && insn[0] == 0x0F && insn[1] == 0x54) {
      delta = dis_SSE_E_to_G_all( pfx, delta+2, "andps", Iop_AndV128 );
      goto decode_success;
   }

//..    /* 0F C2 = CMPPS -- 32Fx4 comparison from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xC2) {
//..       delta = dis_SSEcmp_E_to_G( sorb, delta+2, "cmpps", True, 4 );
//..       goto decode_success;
//..    }

   /* F3 0F C2 = CMPSS -- 32F0x4 comparison from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0xC2) {
      delta = dis_SSEcmp_E_to_G( pfx, delta+2, "cmpss", False, 4 );
      goto decode_success;
   }

   /* 0F 2F = COMISS  -- 32F0x4 comparison G,E, and set ZCP */
   /* 0F 2E = UCOMISS -- 32F0x4 comparison G,E, and set ZCP */
   if (haveNo66noF2noF3(pfx) && sz == 4 
       && insn[0] == 0x0F && (insn[1] == 0x2F || insn[1] == 0x2E)) {
      IRTemp argL = newTemp(Ity_F32);
      IRTemp argR = newTemp(Ity_F32);
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         assign( argR, getXMMRegLane32F( eregOfRexRM(pfx,modrm), 
                                         0/*lowest lane*/ ) );
         delta += 2+1;
         DIP("%scomiss %s,%s\n", insn[1]==0x2E ? "u" : "",
                                 nameXMMReg(eregOfRexRM(pfx,modrm)),
                                 nameXMMReg(gregOfRexRM(pfx,modrm)) );
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
	 assign( argR, loadLE(Ity_F32, mkexpr(addr)) );
         delta += 2+alen;
         DIP("%scomiss %s,%s\n", insn[1]==0x2E ? "u" : "",
                                 dis_buf,
                                 nameXMMReg(gregOfRexRM(pfx,modrm)) );
      }
      assign( argL, getXMMRegLane32F( gregOfRexRM(pfx,modrm), 
                                      0/*lowest lane*/ ) );

      stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(AMD64G_CC_OP_COPY) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0) ));
      stmt( IRStmt_Put( 
               OFFB_CC_DEP1,
               binop( Iop_And64,
                      unop( Iop_32Uto64,
                            binop(Iop_CmpF64, 
                                  unop(Iop_F32toF64,mkexpr(argL)),
                                  unop(Iop_F32toF64,mkexpr(argR)))),
                      mkU64(0x45)
          )));

      goto decode_success;
   }

//..    /* 0F 2A = CVTPI2PS -- convert 2 x I32 in mem/mmx to 2 x F32 in low
//..       half xmm */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x2A) {
//..       IRTemp arg64 = newTemp(Ity_I64);
//..       IRTemp rmode = newTemp(Ity_I32);
//..       vassert(sz == 4);
//.. 
//..       modrm = getUChar(delta+2);
//..       do_MMX_preamble();
//..       if (epartIsReg(modrm)) {
//..          assign( arg64, getMMXReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("cvtpi2ps %s,%s\n", nameMMXReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( arg64, loadLE(Ity_I64, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("cvtpi2ps %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//.. 
//..       assign( rmode, get_sse_roundingmode() );
//.. 
//..       putXMMRegLane32F( 
//..          gregOfRM(modrm), 0,
//..          binop(Iop_F64toF32, 
//..                mkexpr(rmode),
//..                unop(Iop_I32toF64, 
//..                     unop(Iop_64to32, mkexpr(arg64)) )) );
//.. 
//..       putXMMRegLane32F(
//..          gregOfRM(modrm), 1, 
//..          binop(Iop_F64toF32, 
//..                mkexpr(rmode),
//..                unop(Iop_I32toF64,
//..                     unop(Iop_64HIto32, mkexpr(arg64)) )) );
//.. 
//..       goto decode_success;
//..    }

   /* F3 0F 2A = CVTSI2SS 
      -- sz==4: convert I32 in mem/ireg to F32 in low quarter xmm
      -- sz==8: convert I64 in mem/ireg to F32 in low quarter xmm */
   if (haveF3no66noF2(pfx) && (sz == 4 || sz == 8)
       && insn[0] == 0x0F && insn[1] == 0x2A) {

      IRTemp rmode = newTemp(Ity_I32);
      assign( rmode, get_sse_roundingmode() );
      modrm = getUChar(delta+2);

      if (sz == 4) {
         IRTemp arg32 = newTemp(Ity_I32);
         if (epartIsReg(modrm)) {
            assign( arg32, getIReg32(eregOfRexRM(pfx,modrm)) );
            delta += 2+1;
            DIP("cvtsi2ss %s,%s\n", nameIReg32(eregOfRexRM(pfx,modrm)),
                                    nameXMMReg(gregOfRexRM(pfx,modrm)));
         } else {
            addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
            assign( arg32, loadLE(Ity_I32, mkexpr(addr)) );
            delta += 2+alen;
            DIP("cvtsi2ss %s,%s\n", dis_buf,
                                    nameXMMReg(gregOfRexRM(pfx,modrm)) );
         }
         putXMMRegLane32F( 
            gregOfRexRM(pfx,modrm), 0,
            binop(Iop_F64toF32,
                  mkexpr(rmode),
                  unop(Iop_I32toF64, mkexpr(arg32)) ) );
      } else {
         /* sz == 8 */
         IRTemp arg64 = newTemp(Ity_I64);
         if (epartIsReg(modrm)) {
            assign( arg64, getIReg64(eregOfRexRM(pfx,modrm)) );
            delta += 2+1;
            DIP("cvtsi2ssq %s,%s\n", nameIReg64(eregOfRexRM(pfx,modrm)),
                                     nameXMMReg(gregOfRexRM(pfx,modrm)));
         } else {
            addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
            assign( arg64, loadLE(Ity_I64, mkexpr(addr)) );
            delta += 2+alen;
            DIP("cvtsi2ssq %s,%s\n", dis_buf,
                                     nameXMMReg(gregOfRexRM(pfx,modrm)) );
         }
         putXMMRegLane32F( 
            gregOfRexRM(pfx,modrm), 0,
            binop(Iop_F64toF32,
                  mkexpr(rmode),
                  binop(Iop_I64toF64, mkexpr(rmode), mkexpr(arg64)) ) );
      }

      goto decode_success;
   }

//..    /* 0F 2D = CVTPS2PI -- convert 2 x F32 in mem/low half xmm to 2 x
//..       I32 in mmx, according to prevailing SSE rounding mode */
//..    /* 0F 2C = CVTTPS2PI -- convert 2 x F32 in mem/low half xmm to 2 x
//..       I32 in mmx, rounding towards zero */
//..    if (sz == 4 && insn[0] == 0x0F && (insn[1] == 0x2D || insn[1] == 0x2C)) {
//..       IRTemp dst64  = newTemp(Ity_I64);
//..       IRTemp rmode  = newTemp(Ity_I32);
//..       IRTemp f32lo  = newTemp(Ity_F32);
//..       IRTemp f32hi  = newTemp(Ity_F32);
//..       Bool   r2zero = insn[1] == 0x2C;
//.. 
//..       do_MMX_preamble();
//..       modrm = getUChar(delta+2);
//.. 
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//.. 	 assign(f32lo, getXMMRegLane32F(eregOfRM(modrm), 0));
//.. 	 assign(f32hi, getXMMRegLane32F(eregOfRM(modrm), 1));
//..          DIP("cvt%sps2pi %s,%s\n", r2zero ? "t" : "",
//..                                    nameXMMReg(eregOfRM(modrm)),
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign(f32lo, loadLE(Ity_F32, mkexpr(addr)));
//.. 	 assign(f32hi, loadLE(Ity_F32, binop( Iop_Add32, 
//..                                               mkexpr(addr), 
//..                                               mkU32(4) )));
//..          delta += 2+alen;
//..          DIP("cvt%sps2pi %s,%s\n", r2zero ? "t" : "",
//..                                    dis_buf,
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       }
//.. 
//..       if (r2zero) {
//..          assign(rmode, mkU32((UInt)Irrm_ZERO) );
//..       } else {
//..          assign( rmode, get_sse_roundingmode() );
//..       }
//.. 
//..       assign( 
//..          dst64,
//..          binop( Iop_32HLto64,
//..                 binop( Iop_F64toI32, 
//..                        mkexpr(rmode), 
//..                        unop( Iop_F32toF64, mkexpr(f32hi) ) ),
//..                 binop( Iop_F64toI32, 
//..                        mkexpr(rmode), 
//..                        unop( Iop_F32toF64, mkexpr(f32lo) ) )
//..               )
//..       );
//.. 
//..       putMMXReg(gregOfRM(modrm), mkexpr(dst64));
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 2D = CVTSS2SI -- convert F32 in mem/low quarter xmm to
//..       I32 in ireg, according to prevailing SSE rounding mode */
   /* F3 0F 2C = CVTTSS2SI 
      when sz==4 -- convert F32 in mem/low quarter xmm to I32 in ireg, 
                    truncating towards zero
      when sz==8 -- convert F32 in mem/low quarter xmm to I64 in ireg, 
                    truncating towards zero 
   */
   if (haveF3no66noF2(pfx) 
       && insn[0] == 0x0F 
       && ( /* insn[1] == 0x2D || */ insn[1] == 0x2C)) {
      IRTemp rmode  = newTemp(Ity_I32);
      IRTemp f32lo  = newTemp(Ity_F32);
      Bool   r2zero = toBool(insn[1] == 0x2C);
      vassert(sz == 4 || sz == 8);

      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         delta += 2+1;
         assign(f32lo, getXMMRegLane32F(eregOfRexRM(pfx,modrm), 0));
         DIP("cvt%sss2si %s,%s\n", r2zero ? "t" : "",
                                   nameXMMReg(eregOfRexRM(pfx,modrm)),
                                   nameIReg(sz, gregOfRexRM(pfx,modrm), False));
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         assign(f32lo, loadLE(Ity_F32, mkexpr(addr)));
         delta += 2+alen;
         DIP("cvt%sss2si %s,%s\n", r2zero ? "t" : "",
                                   dis_buf,
                                   nameIReg(sz, gregOfRexRM(pfx,modrm), False));
      }

      if (r2zero) {
         assign( rmode, mkU32((UInt)Irrm_ZERO) );
      } else {
         assign( rmode, get_sse_roundingmode() );
      }

      if (sz == 4) {
         putIReg32( gregOfRexRM(pfx,modrm),
                    binop( Iop_F64toI32, 
                           mkexpr(rmode), 
                           unop(Iop_F32toF64, mkexpr(f32lo))) );
      } else {
         putIReg64( gregOfRexRM(pfx,modrm),
                    binop( Iop_F64toI64, 
                           mkexpr(rmode), 
                           unop(Iop_F32toF64, mkexpr(f32lo))) );
      }

      goto decode_success;
   }


////////////////////////////////////////////////////////////////
//..    /* F3 0F 2C = CVTTSS2SI -- convert F32 in mem/low quarter xmm to
//..       I32 in ireg, according to prevailing SSE rounding mode */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F 
//..        && (insn[2] == 0x2D || insn[2] == 0x2C)) {
//..       IRTemp rmode = newTemp(Ity_I32);
//..       IRTemp f32lo = newTemp(Ity_F32);
//..       Bool   r2zero = insn[2] == 0x2C;
//..       vassert(sz == 4);
//.. 
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          delta += 3+1;
//.. 	 assign(f32lo, getXMMRegLane32F(eregOfRM(modrm), 0));
//..          DIP("cvt%sss2si %s,%s\n", r2zero ? "t" : "",
//..                                    nameXMMReg(eregOfRM(modrm)),
//..                                    nameIReg(4, gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//.. 	 assign(f32lo, loadLE(Ity_F32, mkexpr(addr)));
//..          delta += 3+alen;
//..          DIP("cvt%sss2si %s,%s\n", r2zero ? "t" : "",
//..                                    dis_buf,
//..                                    nameIReg(4, gregOfRM(modrm)));
//..       }
//.. 
//..       if (r2zero) {
//..          assign( rmode, mkU32((UInt)Irrm_ZERO) );
//..       } else {
//..          assign( rmode, get_sse_roundingmode() );
//..       }
//.. 
//..       putIReg(4, gregOfRM(modrm),
//..                  binop( Iop_F64toI32, 
//..                         mkexpr(rmode), 
//..                         unop( Iop_F32toF64, mkexpr(f32lo) ) )
//..       );
//.. 
//..       goto decode_success;
//..    }
///////////////////////////////////////////////////////////////////


//.. 
//..    /* 0F 5E = DIVPS -- div 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x5E) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "divps", Iop_Div32Fx4 );
//..       goto decode_success;
//..    }

   /* F3 0F 5E = DIVSS -- div 32F0x4 from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5E) {
      delta = dis_SSE_E_to_G_lo32( pfx, delta+2, "divss", Iop_Div32F0x4 );
      goto decode_success;
   }

   /* 0F AE /2 = LDMXCSR m32 -- load %mxcsr */
   if (insn[0] == 0x0F && insn[1] == 0xAE
       && haveNo66noF2noF3(pfx)
       && !epartIsReg(insn[2]) && gregLO3ofRM(insn[2]) == 2) {

      IRTemp t64 = newTemp(Ity_I64);
      IRTemp ew = newTemp(Ity_I32);

      vassert(sz == 4);
      addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
      delta += 2+alen;
      DIP("ldmxcsr %s\n", dis_buf);

      /* The only thing we observe in %mxcsr is the rounding mode.
         Therefore, pass the 32-bit value (SSE native-format control
         word) to a clean helper, getting back a 64-bit value, the
         lower half of which is the SSEROUND value to store, and the
         upper half of which is the emulation-warning token which may
         be generated.  
      */
      /* ULong amd64h_check_ldmxcsr ( ULong ); */
      assign( t64, mkIRExprCCall(
                      Ity_I64, 0/*regparms*/, 
                      "amd64g_check_ldmxcsr",
                      &amd64g_check_ldmxcsr, 
                      mkIRExprVec_1( 
                         unop(Iop_32Uto64,
                              loadLE(Ity_I32, mkexpr(addr))
                         )
                      )
                   )
            );

      put_sse_roundingmode( unop(Iop_64to32, mkexpr(t64)) );
      assign( ew, unop(Iop_64HIto32, mkexpr(t64) ) );
      put_emwarn( mkexpr(ew) );
      /* Finally, if an emulation warning was reported, side-exit to
         the next insn, reporting the warning, so that Valgrind's
         dispatcher sees the warning. */
      stmt( 
         IRStmt_Exit(
            binop(Iop_CmpNE64, unop(Iop_32Uto64,mkexpr(ew)), mkU64(0)),
            Ijk_EmWarn,
            IRConst_U64(guest_rip_bbstart+delta)
         )
      );
      goto decode_success;
   }

//..    /* 0F 5F = MAXPS -- max 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x5F) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "maxps", Iop_Max32Fx4 );
//..       goto decode_success;
//..    }

   /* F3 0F 5F = MAXSS -- max 32F0x4 from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5F) {
      delta = dis_SSE_E_to_G_lo32( pfx, delta+2, "maxss", Iop_Max32F0x4 );
      goto decode_success;
   }

//..    /* 0F 5D = MINPS -- min 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x5D) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "minps", Iop_Min32Fx4 );
//..       goto decode_success;
//..    }

   /* F3 0F 5D = MINSS -- min 32F0x4 from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5D) {
      delta = dis_SSE_E_to_G_lo32( pfx, delta+2, "minss", Iop_Min32F0x4 );
      goto decode_success;
   }

   /* 0F 28 = MOVAPS -- move from E (mem or xmm) to G (xmm). */
   /* 0F 10 = MOVUPS -- move from E (mem or xmm) to G (xmm). */
   if (haveNo66noF2noF3(pfx) && sz == 4
       && insn[0] == 0x0F && (insn[1] == 0x28 || insn[1] == 0x10)) {
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         putXMMReg( gregOfRexRM(pfx,modrm), 
                    getXMMReg( eregOfRexRM(pfx,modrm) ));
         DIP("mov[ua]ps %s,%s\n", nameXMMReg(eregOfRexRM(pfx,modrm)),
                                  nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+1;
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         putXMMReg( gregOfRexRM(pfx,modrm), 
                    loadLE(Ity_V128, mkexpr(addr)) );
         DIP("mov[ua]ps %s,%s\n", dis_buf,
                                  nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+alen;
      }
      goto decode_success;
   }

   /* 0F 29 = MOVAPS -- move from G (xmm) to E (mem or xmm). */
   if (haveNo66noF2noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x29) {
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         /* fall through; awaiting test case */
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         storeLE( mkexpr(addr), getXMMReg(gregOfRexRM(pfx,modrm)) );
         DIP("movaps %s,%s\n", nameXMMReg(gregOfRexRM(pfx,modrm)),
                               dis_buf );
         delta += 2+alen;
         goto decode_success;
      }
   }

//..    /* 0F 16 = MOVHPS -- move from mem to high half of XMM. */
//..    /* 0F 16 = MOVLHPS -- move from lo half to hi half of XMM. */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x16) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//..          putXMMRegLane64( gregOfRM(modrm), 1/*upper lane*/,
//..                           getXMMRegLane64( eregOfRM(modrm), 0 ) );
//..          DIP("movhps %s,%s\n", nameXMMReg(eregOfRM(modrm)), 
//..                                nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          delta += 2+alen;
//..          putXMMRegLane64( gregOfRM(modrm), 1/*upper lane*/,
//..                           loadLE(Ity_I64, mkexpr(addr)) );
//..          DIP("movhps %s,%s\n", dis_buf, 
//..                                nameXMMReg( gregOfRM(modrm) ));
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 17 = MOVHPS -- move from high half of XMM to mem. */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x17) {
//..       if (!epartIsReg(insn[2])) {
//..          delta += 2;
//..          addr = disAMode ( &alen, sorb, delta, dis_buf );
//..          delta += alen;
//..          storeLE( mkexpr(addr), 
//..                   getXMMRegLane64( gregOfRM(insn[2]),
//..                                    1/*upper lane*/ ) );
//..          DIP("movhps %s,%s\n", nameXMMReg( gregOfRM(insn[2]) ),
//..                                dis_buf);
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }
//.. 
//..    /* 0F 12 = MOVLPS -- move from mem to low half of XMM. */
//..    /* OF 12 = MOVHLPS -- from from hi half to lo half of XMM. */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x12) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//..          putXMMRegLane64( gregOfRM(modrm),  
//..                           0/*lower lane*/,
//..                           getXMMRegLane64( eregOfRM(modrm), 1 ));
//..          DIP("movhlps %s, %s\n", nameXMMReg(eregOfRM(modrm)), 
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          delta += 2+alen;
//..          putXMMRegLane64( gregOfRM(modrm),  0/*lower lane*/,
//..                           loadLE(Ity_I64, mkexpr(addr)) );
//..          DIP("movlps %s, %s\n", 
//..              dis_buf, nameXMMReg( gregOfRM(modrm) ));
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 13 = MOVLPS -- move from low half of XMM to mem. */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x13) {
//..       if (!epartIsReg(insn[2])) {
//..          delta += 2;
//..          addr = disAMode ( &alen, sorb, delta, dis_buf );
//..          delta += alen;
//..          storeLE( mkexpr(addr), 
//..                   getXMMRegLane64( gregOfRM(insn[2]), 
//..                                    0/*lower lane*/ ) );
//..          DIP("movlps %s, %s\n", nameXMMReg( gregOfRM(insn[2]) ),
//..                                 dis_buf);
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }
//.. 
//..    /* 0F 50 = MOVMSKPS - move 4 sign bits from 4 x F32 in xmm(E)
//..       to 4 lowest bits of ireg(G) */
//..    if (insn[0] == 0x0F && insn[1] == 0x50) {
//..       modrm = getUChar(delta+2);
//..       if (sz == 4 && epartIsReg(modrm)) {
//..          Int src;
//..          t0 = newTemp(Ity_I32);
//..          t1 = newTemp(Ity_I32);
//..          t2 = newTemp(Ity_I32);
//..          t3 = newTemp(Ity_I32);
//..          delta += 2+1;
//..          src = eregOfRM(modrm);
//..          assign( t0, binop( Iop_And32,
//..                             binop(Iop_Shr32, getXMMRegLane32(src,0), mkU8(31)),
//..                             mkU32(1) ));
//..          assign( t1, binop( Iop_And32,
//..                             binop(Iop_Shr32, getXMMRegLane32(src,1), mkU8(30)),
//..                             mkU32(2) ));
//..          assign( t2, binop( Iop_And32,
//..                             binop(Iop_Shr32, getXMMRegLane32(src,2), mkU8(29)),
//..                             mkU32(4) ));
//..          assign( t3, binop( Iop_And32,
//..                             binop(Iop_Shr32, getXMMRegLane32(src,3), mkU8(28)),
//..                             mkU32(8) ));
//..          putIReg(4, gregOfRM(modrm),
//..                     binop(Iop_Or32,
//..                           binop(Iop_Or32, mkexpr(t0), mkexpr(t1)),
//..                           binop(Iop_Or32, mkexpr(t2), mkexpr(t3))
//..                          )
//..                  );
//..          DIP("movmskps %s,%s\n", nameXMMReg(src), 
//..                                  nameIReg(4, gregOfRM(modrm)));
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }
//.. 
//..    /* 0F 2B = MOVNTPS -- for us, just a plain SSE store. */
//..    if (insn[0] == 0x0F && insn[1] == 0x2B) {
//..       modrm = getUChar(delta+2);
//..       if (!epartIsReg(modrm)) {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          storeLE( mkexpr(addr), getXMMReg(gregOfRM(modrm)) );
//..          DIP("movntps %s,%s\n", dis_buf,
//..                                 nameXMMReg(gregOfRM(modrm)));
//..          delta += 2+alen;
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F E7 = MOVNTQ -- for us, just a plain MMX store.  Note, the
//..       Intel manual does not say anything about the usual business of
//..       the FP reg tags getting trashed whenever an MMX insn happens.
//..       So we just leave them alone. 
//..    */
//..    if (insn[0] == 0x0F && insn[1] == 0xE7) {
//..       modrm = getUChar(delta+2);
//..       if (sz == 4 && !epartIsReg(modrm)) {
//..          /* do_MMX_preamble(); Intel docs don't specify this */
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          storeLE( mkexpr(addr), getMMXReg(gregOfRM(modrm)) );
//..          DIP("movntq %s,%s\n", dis_buf,
//..                                nameMMXReg(gregOfRM(modrm)));
//..          delta += 2+alen;
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }

   /* F3 0F 10 = MOVSS -- move 32 bits from E (mem or lo 1/4 xmm) to G
      (lo 1/4 xmm).  If E is mem, upper 3/4 of G is zeroed out. */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x10) {
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         putXMMRegLane32( gregOfRexRM(pfx,modrm), 0,
                          getXMMRegLane32( eregOfRexRM(pfx,modrm), 0 ));
         DIP("movss %s,%s\n", nameXMMReg(eregOfRexRM(pfx,modrm)),
                              nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+1;
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         putXMMReg( gregOfRexRM(pfx,modrm), mkV128(0) );
         putXMMRegLane32( gregOfRexRM(pfx,modrm), 0,
                          loadLE(Ity_I32, mkexpr(addr)) );
         DIP("movss %s,%s\n", dis_buf,
                              nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+alen;
      }
      goto decode_success;
   }

   /* F3 0F 11 = MOVSS -- move 32 bits from G (lo 1/4 xmm) to E (mem
      or lo 1/4 xmm). */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x11) {
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         /* fall through, we don't yet have a test case */
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         storeLE( mkexpr(addr),
                  getXMMRegLane32(gregOfRexRM(pfx,modrm), 0) );
         DIP("movss %s,%s\n", nameXMMReg(gregOfRexRM(pfx,modrm)),
                              dis_buf);
         delta += 2+alen;
         goto decode_success;
      }
   }

//..    /* 0F 59 = MULPS -- mul 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x59) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "mulps", Iop_Mul32Fx4 );
//..       goto decode_success;
//..    }

   /* F3 0F 59 = MULSS -- mul 32F0x4 from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x59) {
      delta = dis_SSE_E_to_G_lo32( pfx, delta+2, "mulss", Iop_Mul32F0x4 );
      goto decode_success;
   }

   /* 0F 56 = ORPS -- G = G and E */
   if (haveNo66noF2noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x56) {
      delta = dis_SSE_E_to_G_all( pfx, delta+2, "orps", Iop_OrV128 );
      goto decode_success;
   }

//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F E0 = PAVGB -- 8x8 unsigned Packed Average, with rounding */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xE0) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pavgb", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F E3 = PAVGW -- 16x4 unsigned Packed Average, with rounding */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xE3) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pavgw", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F C5 = PEXTRW -- extract 16-bit field from mmx(E) and put 
//..       zero-extend of it in ireg(G). */
//..    if (insn[0] == 0x0F && insn[1] == 0xC5) {
//..       modrm = insn[2];
//..       if (sz == 4 && epartIsReg(modrm)) {
//..          IRTemp sV = newTemp(Ity_I64);
//..          t5 = newTemp(Ity_I16);
//..          do_MMX_preamble();
//..          assign(sV, getMMXReg(eregOfRM(modrm)));
//..          breakup64to16s( sV, &t3, &t2, &t1, &t0 );
//..          switch (insn[3] & 3) {
//..             case 0:  assign(t5, mkexpr(t0)); break;
//..             case 1:  assign(t5, mkexpr(t1)); break;
//..             case 2:  assign(t5, mkexpr(t2)); break;
//..             case 3:  assign(t5, mkexpr(t3)); break;
//..             default: vassert(0);
//..          }
//..          putIReg(4, gregOfRM(modrm), unop(Iop_16Uto32, mkexpr(t5)));
//..          DIP("pextrw $%d,%s,%s\n",
//..              (Int)insn[3], nameMMXReg(eregOfRM(modrm)),
//..                            nameIReg(4,gregOfRM(modrm)));
//..          delta += 4;
//..          goto decode_success;
//..       } 
//..       /* else fall through */
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F C4 = PINSRW -- get 16 bits from E(mem or low half ireg) and
//..       put it into the specified lane of mmx(G). */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xC4) {
//..       /* Use t0 .. t3 to hold the 4 original 16-bit lanes of the
//..          mmx reg.  t4 is the new lane value.  t5 is the original
//..          mmx value. t6 is the new mmx value. */
//..       Int lane;
//..       t4 = newTemp(Ity_I16);
//..       t5 = newTemp(Ity_I64);
//..       t6 = newTemp(Ity_I64);
//..       modrm = insn[2];
//..       do_MMX_preamble();
//.. 
//..       assign(t5, getMMXReg(gregOfRM(modrm)));
//..       breakup64to16s( t5, &t3, &t2, &t1, &t0 );
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign(t4, getIReg(2, eregOfRM(modrm)));
//..          lane = insn[3];
//..          delta += 2+2;
//..          DIP("pinsrw $%d,%s,%s\n", (Int)lane, 
//..                                    nameIReg(2,eregOfRM(modrm)),
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       } else {
//..          /* awaiting test case */
//..          goto decode_failure;
//..       }
//.. 
//..       switch (lane & 3) {
//..          case 0:  assign(t6, mk64from16s(t3,t2,t1,t4)); break;
//..          case 1:  assign(t6, mk64from16s(t3,t2,t4,t0)); break;
//..          case 2:  assign(t6, mk64from16s(t3,t4,t1,t0)); break;
//..          case 3:  assign(t6, mk64from16s(t4,t2,t1,t0)); break;
//..          default: vassert(0);
//..       }
//..       putMMXReg(gregOfRM(modrm), mkexpr(t6));
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F EE = PMAXSW -- 16x4 signed max */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xEE) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pmaxsw", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F DE = PMAXUB -- 8x8 unsigned max */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xDE) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pmaxub", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F EA = PMINSW -- 16x4 signed min */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xEA) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pminsw", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F DA = PMINUB -- 8x8 unsigned min */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xDA) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pminub", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F D7 = PMOVMSKB -- extract sign bits from each of 8 lanes in
//..       mmx(G), turn them into a byte, and put zero-extend of it in
//..       ireg(G). */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xD7) {
//..       modrm = insn[2];
//..       if (epartIsReg(modrm)) {
//..          do_MMX_preamble();
//..          t0 = newTemp(Ity_I64);
//..          t1 = newTemp(Ity_I32);
//..          assign(t0, getMMXReg(eregOfRM(modrm)));
//..          assign(t1, mkIRExprCCall(
//..                        Ity_I32, 0/*regparms*/, 
//..                        "x86g_calculate_mmx_pmovmskb",
//..                        &x86g_calculate_mmx_pmovmskb,
//..                        mkIRExprVec_1(mkexpr(t0))));
//..          putIReg(4, gregOfRM(modrm), mkexpr(t1));
//..          DIP("pmovmskb %s,%s\n", nameMMXReg(eregOfRM(modrm)),
//..                                  nameIReg(4,gregOfRM(modrm)));
//..          delta += 3;
//..          goto decode_success;
//..       } 
//..       /* else fall through */
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F E4 = PMULUH -- 16x4 hi-half of unsigned widening multiply */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xE4) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "pmuluh", False );
//..       goto decode_success;
//..    }

   /* 0F 18 /0 = PREFETCHNTA -- prefetch into caches, */
   /* 0F 18 /1 = PREFETCH0   -- with various different hints */
   /* 0F 18 /2 = PREFETCH1 */
   /* 0F 18 /3 = PREFETCH2 */
   if (insn[0] == 0x0F && insn[1] == 0x18
       && haveNo66noF2noF3(pfx)
       && !epartIsReg(insn[2]) 
       && gregLO3ofRM(insn[2]) >= 0 && gregLO3ofRM(insn[2]) <= 3) {
      HChar* hintstr = "??";

      modrm = getUChar(delta+2);
      vassert(!epartIsReg(modrm));

      addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
      delta += 2+alen;

      switch (gregLO3ofRM(modrm)) {
         case 0: hintstr = "nta"; break;
         case 1: hintstr = "t0"; break;
         case 2: hintstr = "t1"; break;
         case 3: hintstr = "t2"; break;
         default: vassert(0);
      }

      DIP("prefetch%s %s\n", hintstr, dis_buf);
      goto decode_success;
   }

//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F F6 = PSADBW -- sum of 8Ux8 absolute differences */
//..    if (insn[0] == 0x0F && insn[1] == 0xF6) {
//..       vassert(sz == 4);
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                  sorb, delta+2, insn[1], "psadbw", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE1 ---*** */
//..    /* 0F 70 = PSHUFW -- rearrange 4x16 from E(mmx or mem) to G(mmx) */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x70) {
//..       Int order;
//..       IRTemp sV, dV, s3, s2, s1, s0;
//..       s3 = s2 = s1 = s0 = IRTemp_INVALID;
//..       sV = newTemp(Ity_I64);
//..       dV = newTemp(Ity_I64);
//..       do_MMX_preamble();
//..       modrm = insn[2];
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getMMXReg(eregOfRM(modrm)) );
//..          order = (Int)insn[3];
//..          delta += 2+2;
//..          DIP("pshufw $%d,%s,%s\n", order, 
//..                                    nameMMXReg(eregOfRM(modrm)),
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_I64, mkexpr(addr)) );
//..          order = (Int)insn[2+alen];
//..          delta += 3+alen;
//..          DIP("pshufw $%d,%s,%s\n", order, 
//..                                    dis_buf,
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       }
//..       breakup64to16s( sV, &s3, &s2, &s1, &s0 );
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #     define SEL(n) \
/..                 ((n)==0 ? s0 : ((n)==1 ? s1 : ((n)==2 ? s2 : s3)))
#endif /* stop gcc multi-line comment warning */
//..       assign(dV,
//.. 	     mk64from16s( SEL((order>>6)&3), SEL((order>>4)&3),
//..                           SEL((order>>2)&3), SEL((order>>0)&3) )
//..       );
//..       putMMXReg(gregOfRM(modrm), mkexpr(dV));
//.. #     undef SEL
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 53 = RCPPS -- approx reciprocal 32Fx4 from R/M to R */
//..    if (insn[0] == 0x0F && insn[1] == 0x53) {
//..       vassert(sz == 4);
//..       delta = dis_SSE_E_to_G_unary_all( sorb, delta+2, 
//..                                         "rcpps", Iop_Recip32Fx4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 53 = RCPSS -- approx reciprocal 32F0x4 from R/M to R */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x53) {
//..       vassert(sz == 4);
//..       delta = dis_SSE_E_to_G_unary_lo32( sorb, delta+3, 
//..                                          "rcpss", Iop_Recip32F0x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 52 = RSQRTPS -- approx reciprocal sqrt 32Fx4 from R/M to R */
//..    if (insn[0] == 0x0F && insn[1] == 0x52) {
//..       vassert(sz == 4);
//..       delta = dis_SSE_E_to_G_unary_all( sorb, delta+2, 
//..                                         "rsqrtps", Iop_RSqrt32Fx4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 52 = RSQRTSS -- approx reciprocal sqrt 32F0x4 from R/M to R */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x52) {
//..       vassert(sz == 4);
//..       delta = dis_SSE_E_to_G_unary_lo32( sorb, delta+3, 
//..                                          "rsqrtss", Iop_RSqrt32F0x4 );
//..       goto decode_success;
//..    }

   /* 0F AE /7 = SFENCE -- flush pending operations to memory */
   if (haveNo66noF2noF3(pfx) 
       && insn[0] == 0x0F && insn[1] == 0xAE
       && epartIsReg(insn[2]) && gregLO3ofRM(insn[2]) == 7
       && sz == 4) {
      delta += 3;
      /* Insert a memory fence.  It's sometimes important that these
         are carried through to the generated code. */
      stmt( IRStmt_MFence() );
      DIP("sfence\n");
      goto decode_success;
   }

//..    /* 0F C6 /r ib = SHUFPS -- shuffle packed F32s */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xC6) {
//..       Int    select;
//..       IRTemp sV, dV;
//..       IRTemp s3, s2, s1, s0, d3, d2, d1, d0;
//..       sV = newTemp(Ity_V128);
//..       dV = newTemp(Ity_V128);
//..       s3 = s2 = s1 = s0 = d3 = d2 = d1 = d0 = IRTemp_INVALID;
//..       modrm = insn[2];
//..       assign( dV, getXMMReg(gregOfRM(modrm)) );
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          select = (Int)insn[3];
//..          delta += 2+2;
//..          DIP("shufps $%d,%s,%s\n", select, 
//..                                    nameXMMReg(eregOfRM(modrm)),
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//..          select = (Int)insn[2+alen];
//..          delta += 3+alen;
//..          DIP("shufps $%d,%s,%s\n", select, 
//..                                    dis_buf,
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       }
//.. 
//..       breakup128to32s( dV, &d3, &d2, &d1, &d0 );
//..       breakup128to32s( sV, &s3, &s2, &s1, &s0 );
//.. 
//.. #     define SELD(n) ((n)==0 ? d0 : ((n)==1 ? d1 : ((n)==2 ? d2 : d3)))
//.. #     define SELS(n) ((n)==0 ? s0 : ((n)==1 ? s1 : ((n)==2 ? s2 : s3)))
//.. 
//..       putXMMReg(
//..          gregOfRM(modrm), 
//..          mk128from32s( SELS((select>>6)&3), SELS((select>>4)&3), 
//..                        SELD((select>>2)&3), SELD((select>>0)&3) )
//..       );
//.. 
//.. #     undef SELD
//.. #     undef SELS
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 51 = SQRTPS -- approx sqrt 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x51) {
//..       delta = dis_SSE_E_to_G_unary_all( sorb, delta+2, 
//..                                         "sqrtps", Iop_Sqrt32Fx4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 51 = SQRTSS -- approx sqrt 32F0x4 from R/M to R */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x51) {
//..       vassert(sz == 4);
//..       delta = dis_SSE_E_to_G_unary_lo32( sorb, delta+3, 
//..                                          "sqrtss", Iop_Sqrt32F0x4 );
//..       goto decode_success;
//..    }

   /* 0F AE /3 = STMXCSR m32 -- store %mxcsr */
   if (insn[0] == 0x0F && insn[1] == 0xAE
       && haveNo66noF2noF3(pfx)
       && !epartIsReg(insn[2]) && gregLO3ofRM(insn[2]) == 3) {

      vassert(sz == 4);
      addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
      delta += 2+alen;

      /* Fake up a native SSE mxcsr word.  The only thing it depends
         on is SSEROUND[1:0], so call a clean helper to cook it up. 
      */
      /* ULong amd64h_create_mxcsr ( ULong sseround ) */
      DIP("stmxcsr %s\n", dis_buf);
      storeLE( 
         mkexpr(addr), 
         unop(Iop_64to32,      
              mkIRExprCCall(
                 Ity_I64, 0/*regp*/,
                 "amd64g_create_mxcsr", &amd64g_create_mxcsr, 
                 mkIRExprVec_1( unop(Iop_32Uto64,get_sse_roundingmode()) ) 
	      ) 
	 )
      );
      goto decode_success;
   }

//..    /* 0F 5C = SUBPS -- sub 32Fx4 from R/M to R */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x5C) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "subps", Iop_Sub32Fx4 );
//..       goto decode_success;
//..    }

   /* F3 0F 5C = SUBSS -- sub 32F0x4 from R/M to R */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5C) {
      delta = dis_SSE_E_to_G_lo32( pfx, delta+2, "subss", Iop_Sub32F0x4 );
      goto decode_success;
   }

//..    /* 0F 15 = UNPCKHPS -- unpack and interleave high part F32s */
//..    /* 0F 14 = UNPCKLPS -- unpack and interleave low part F32s */
//..    /* These just appear to be special cases of SHUFPS */
//..    if (sz == 4 && insn[0] == 0x0F && (insn[1] == 0x15 || insn[1] == 0x14)) {
//..       IRTemp sV, dV;
//..       IRTemp s3, s2, s1, s0, d3, d2, d1, d0;
//..       Bool hi = insn[1] == 0x15;
//..       sV = newTemp(Ity_V128);
//..       dV = newTemp(Ity_V128);
//..       s3 = s2 = s1 = s0 = d3 = d2 = d1 = d0 = IRTemp_INVALID;
//..       modrm = insn[2];
//..       assign( dV, getXMMReg(gregOfRM(modrm)) );
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("unpck%sps %s,%s\n", hi ? "h" : "l",
//..                                   nameXMMReg(eregOfRM(modrm)),
//..                                   nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("unpck%sps %s,%s\n", hi ? "h" : "l",
//..                                   dis_buf,
//..                                   nameXMMReg(gregOfRM(modrm)));
//..       }
//.. 
//..       breakup128to32s( dV, &d3, &d2, &d1, &d0 );
//..       breakup128to32s( sV, &s3, &s2, &s1, &s0 );
//.. 
//..       if (hi) {
//..          putXMMReg( gregOfRM(modrm), mk128from32s( s3, d3, s2, d2 ) );
//..       } else {
//..          putXMMReg( gregOfRM(modrm), mk128from32s( s1, d1, s0, d0 ) );
//..       }
//.. 
//..       goto decode_success;
//..    }

   /* 0F 57 = XORPS -- G = G and E */
   if (haveNo66noF2noF3(pfx) && sz == 4 
       && insn[0] == 0x0F && insn[1] == 0x57) {
      delta = dis_SSE_E_to_G_all( pfx, delta+2, "xorps", Iop_XorV128 );
      goto decode_success;
   }

//..    /* ---------------------------------------------------- */
//..    /* --- end of the SSE decoder.                      --- */
//..    /* ---------------------------------------------------- */
//.. 
//..    /* ---------------------------------------------------- */
//..    /* --- start of the SSE2 decoder.                   --- */
//..    /* ---------------------------------------------------- */
//.. 
//..    /* Skip parts of the decoder which don't apply given the stated
//..       guest subarchitecture. */
//..    if (subarch == VexSubArchX86_sse0 || subarch == VexSubArchX86_sse1)
//..       goto after_sse_decoders;
//.. 
//..    insn = (UChar*)&guest_code[delta];
//.. 
//..    /* 66 0F 58 = ADDPD -- add 32Fx4 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x58) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "addpd", Iop_Add64Fx2 );
//..       goto decode_success;
//..    }
 
   /* F2 0F 58 = ADDSD -- add 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x58) {
      vassert(sz == 4);
      delta = dis_SSE_E_to_G_lo64( pfx, delta+2, "addsd", Iop_Add64F0x2 );
      goto decode_success;
   }

   /* 66 0F 55 = ANDNPD -- G = (not G) and E */
   if (have66noF2noF3(pfx) && sz == 2 
       && insn[0] == 0x0F && insn[1] == 0x55) {
      delta = dis_SSE_E_to_G_all_invG( pfx, delta+2, "andnpd", Iop_AndV128 );
      goto decode_success;
   }

   /* 66 0F 54 = ANDPD -- G = G and E */
   if (have66noF2noF3(pfx) && sz == 2 
       && insn[0] == 0x0F && insn[1] == 0x54) {
      delta = dis_SSE_E_to_G_all( pfx, delta+2, "andpd", Iop_AndV128 );
      goto decode_success;
   }

//..    /* 66 0F C2 = CMPPD -- 64Fx2 comparison from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xC2) {
//..       delta = dis_SSEcmp_E_to_G( sorb, delta+2, "cmppd", True, 8 );
//..       goto decode_success;
//..    }

   /* F2 0F C2 = CMPSD -- 64F0x2 comparison from R/M to R */
   if (haveF2no66noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0xC2) {
      delta = dis_SSEcmp_E_to_G( pfx, delta+2, "cmpsd", False, 8 );
      goto decode_success;
   }

   /* 66 0F 2F = COMISD  -- 64F0x2 comparison G,E, and set ZCP */
   /* 66 0F 2E = UCOMISD -- 64F0x2 comparison G,E, and set ZCP */
   if (have66noF2noF3(pfx) && sz == 2
       && insn[0] == 0x0F && (insn[1] == 0x2F || insn[1] == 0x2E)) {
      IRTemp argL = newTemp(Ity_F64);
      IRTemp argR = newTemp(Ity_F64);
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         assign( argR, getXMMRegLane64F( eregOfRexRM(pfx,modrm), 
                                         0/*lowest lane*/ ) );
         delta += 2+1;
         DIP("%scomisd %s,%s\n", insn[1]==0x2E ? "u" : "",
                                 nameXMMReg(eregOfRexRM(pfx,modrm)),
                                 nameXMMReg(gregOfRexRM(pfx,modrm)) );
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         assign( argR, loadLE(Ity_F64, mkexpr(addr)) );
         delta += 2+alen;
         DIP("%scomisd %s,%s\n", insn[1]==0x2E ? "u" : "",
                                 dis_buf,
                                 nameXMMReg(gregOfRexRM(pfx,modrm)) );
      }
      assign( argL, getXMMRegLane64F( gregOfRexRM(pfx,modrm), 
                                      0/*lowest lane*/ ) );

      stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(AMD64G_CC_OP_COPY) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0) ));
      stmt( IRStmt_Put( 
               OFFB_CC_DEP1,
               binop( Iop_And64,
                      unop( Iop_32Uto64, 
                            binop(Iop_CmpF64, mkexpr(argL), mkexpr(argR)) ),
                      mkU64(0x45)
          )));

      goto decode_success;
   }

//..    /* F3 0F E6 = CVTDQ2PD -- convert 2 x I32 in mem/lo half xmm to 2 x
//..       F64 in xmm(G) */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0xE6) {
//..       IRTemp arg64 = newTemp(Ity_I64);
//..       vassert(sz == 4);
//.. 
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          assign( arg64, getXMMRegLane64(eregOfRM(modrm), 0) );
//..          delta += 3+1;
//..          DIP("cvtdq2pd %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//..          assign( arg64, loadLE(Ity_I64, mkexpr(addr)) );
//..          delta += 3+alen;
//..          DIP("cvtdq2pd %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//.. 
//..       putXMMRegLane64F( 
//..          gregOfRM(modrm), 0,
//..          unop(Iop_I32toF64, unop(Iop_64to32, mkexpr(arg64)))
//..       );
//.. 
//..       putXMMRegLane64F(
//..          gregOfRM(modrm), 1, 
//..          unop(Iop_I32toF64, unop(Iop_64HIto32, mkexpr(arg64)))
//..       );
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 5B = CVTDQ2PS -- convert 4 x I32 in mem/xmm to 4 x F32 in
//..       xmm(G) */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x5B) {
//..       IRTemp argV  = newTemp(Ity_V128);
//..       IRTemp rmode = newTemp(Ity_I32);
//.. 
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          assign( argV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("cvtdq2ps %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign( argV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("cvtdq2ps %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//..          
//..       assign( rmode, get_sse_roundingmode() );
//..       breakup128to32s( argV, &t3, &t2, &t1, &t0 );
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #     define CVT(_t)  binop( Iop_F64toF32,                    \
/..                              mkexpr(rmode),                   \
/..                              unop(Iop_I32toF64,mkexpr(_t)))
#endif /* stop gcc multi-line comment warning */
//..       
//..       putXMMRegLane32F( gregOfRM(modrm), 3, CVT(t3) );
//..       putXMMRegLane32F( gregOfRM(modrm), 2, CVT(t2) );
//..       putXMMRegLane32F( gregOfRM(modrm), 1, CVT(t1) );
//..       putXMMRegLane32F( gregOfRM(modrm), 0, CVT(t0) );
//.. 
//.. #     undef CVT
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* F2 0F E6 = CVTPD2DQ -- convert 2 x F64 in mem/xmm to 2 x I32 in
//..       lo half xmm(G), and zero upper half */
//..    if (insn[0] == 0xF2 && insn[1] == 0x0F && insn[2] == 0xE6) {
//..       IRTemp argV  = newTemp(Ity_V128);
//..       IRTemp rmode = newTemp(Ity_I32);
//..       vassert(sz == 4);
//.. 
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          assign( argV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 3+1;
//..          DIP("cvtpd2dq %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//.. 	 assign( argV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 3+alen;
//..          DIP("cvtpd2dq %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//..          
//..       assign( rmode, get_sse_roundingmode() );
//..       t0 = newTemp(Ity_F64);
//..       t1 = newTemp(Ity_F64);
//..       assign( t0, unop(Iop_ReinterpI64asF64, 
//..                        unop(Iop_128to64, mkexpr(argV))) );
//..       assign( t1, unop(Iop_ReinterpI64asF64, 
//..                        unop(Iop_128HIto64, mkexpr(argV))) );
//..       
#if 0 /* stop gcc multi-line comment warning */
/.. #     define CVT(_t)  binop( Iop_F64toI32,                    \
/..                              mkexpr(rmode),                   \
/..                              mkexpr(_t) )
#endif /* stop gcc multi-line comment warning */
//..       
//..       putXMMRegLane32( gregOfRM(modrm), 3, mkU32(0) );
//..       putXMMRegLane32( gregOfRM(modrm), 2, mkU32(0) );
//..       putXMMRegLane32( gregOfRM(modrm), 1, CVT(t1) );
//..       putXMMRegLane32( gregOfRM(modrm), 0, CVT(t0) );
//.. 
//.. #     undef CVT
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 2D = CVTPD2PI -- convert 2 x F64 in mem/xmm to 2 x
//..       I32 in mmx, according to prevailing SSE rounding mode */
//..    /* 66 0F 2C = CVTTPD2PI -- convert 2 x F64 in mem/xmm to 2 x
//..       I32 in mmx, rounding towards zero */
//..    if (sz == 2 && insn[0] == 0x0F && (insn[1] == 0x2D || insn[1] == 0x2C)) {
//..       IRTemp dst64  = newTemp(Ity_I64);
//..       IRTemp rmode  = newTemp(Ity_I32);
//..       IRTemp f64lo  = newTemp(Ity_F64);
//..       IRTemp f64hi  = newTemp(Ity_F64);
//..       Bool   r2zero = insn[1] == 0x2C;
//.. 
//..       do_MMX_preamble();
//..       modrm = getUChar(delta+2);
//.. 
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//.. 	 assign(f64lo, getXMMRegLane64F(eregOfRM(modrm), 0));
//.. 	 assign(f64hi, getXMMRegLane64F(eregOfRM(modrm), 1));
//..          DIP("cvt%spd2pi %s,%s\n", r2zero ? "t" : "",
//..                                    nameXMMReg(eregOfRM(modrm)),
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign(f64lo, loadLE(Ity_F64, mkexpr(addr)));
//.. 	 assign(f64hi, loadLE(Ity_F64, binop( Iop_Add32, 
//..                                               mkexpr(addr), 
//..                                               mkU32(8) )));
//..          delta += 2+alen;
//..          DIP("cvt%spf2pi %s,%s\n", r2zero ? "t" : "",
//..                                    dis_buf,
//..                                    nameMMXReg(gregOfRM(modrm)));
//..       }
//.. 
//..       if (r2zero) {
//..          assign(rmode, mkU32((UInt)Irrm_ZERO) );
//..       } else {
//..          assign( rmode, get_sse_roundingmode() );
//..       }
//.. 
//..       assign( 
//..          dst64,
//..          binop( Iop_32HLto64,
//..                 binop( Iop_F64toI32, mkexpr(rmode), mkexpr(f64hi) ),
//..                 binop( Iop_F64toI32, mkexpr(rmode), mkexpr(f64lo) )
//..               )
//..       );
//.. 
//..       putMMXReg(gregOfRM(modrm), mkexpr(dst64));
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 5A = CVTPD2PS -- convert 2 x F64 in mem/xmm to 2 x F32 in
//..       lo half xmm(G), and zero upper half */
//..    /* Note, this is practically identical to CVTPD2DQ.  It would have
//..       been nicer to merge them together, but the insn[] offsets differ
//..       by one. */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x5A) {
//..       IRTemp argV  = newTemp(Ity_V128);
//..       IRTemp rmode = newTemp(Ity_I32);
//.. 
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          assign( argV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("cvtpd2ps %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign( argV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("cvtpd2ps %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//..          
//..       assign( rmode, get_sse_roundingmode() );
//..       t0 = newTemp(Ity_F64);
//..       t1 = newTemp(Ity_F64);
//..       assign( t0, unop(Iop_ReinterpI64asF64, 
//..                        unop(Iop_128to64, mkexpr(argV))) );
//..       assign( t1, unop(Iop_ReinterpI64asF64, 
//..                        unop(Iop_128HIto64, mkexpr(argV))) );
//..       
#if 0 /* stop gcc multi-line comment warning */
/.. #     define CVT(_t)  binop( Iop_F64toF32,                    \
/..                              mkexpr(rmode),                   \
/..                              mkexpr(_t) )
#endif /* stop gcc multi-line comment warning */
//..       
//..       putXMMRegLane32(  gregOfRM(modrm), 3, mkU32(0) );
//..       putXMMRegLane32(  gregOfRM(modrm), 2, mkU32(0) );
//..       putXMMRegLane32F( gregOfRM(modrm), 1, CVT(t1) );
//..       putXMMRegLane32F( gregOfRM(modrm), 0, CVT(t0) );
//.. 
//.. #     undef CVT
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 2A = CVTPI2PD -- convert 2 x I32 in mem/mmx to 2 x F64 in
//..       xmm(G) */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x2A) {
//..       IRTemp arg64 = newTemp(Ity_I64);
//.. 
//..       modrm = getUChar(delta+2);
//..       do_MMX_preamble();
//..       if (epartIsReg(modrm)) {
//..          assign( arg64, getMMXReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("cvtpi2pd %s,%s\n", nameMMXReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign( arg64, loadLE(Ity_I64, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("cvtpi2pd %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//.. 
//..       putXMMRegLane64F( 
//..          gregOfRM(modrm), 0,
//..          unop(Iop_I32toF64, unop(Iop_64to32, mkexpr(arg64)) )
//..       );
//.. 
//..       putXMMRegLane64F( 
//..          gregOfRM(modrm), 1,
//..          unop(Iop_I32toF64, unop(Iop_64HIto32, mkexpr(arg64)) )
//..       );
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 5B = CVTPS2DQ -- convert 4 x F32 in mem/xmm to 4 x I32 in
//..       xmm(G) */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x5B) {
//..       IRTemp argV  = newTemp(Ity_V128);
//..       IRTemp rmode = newTemp(Ity_I32);
//.. 
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          assign( argV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("cvtps2dq %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign( argV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("cvtps2dq %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//..          
//..       assign( rmode, get_sse_roundingmode() );
//..       breakup128to32s( argV, &t3, &t2, &t1, &t0 );
//.. 
//..       /* This is less than ideal.  If it turns out to be a performance
//.. 	 bottleneck it can be improved. */
#if 0 /* stop gcc multi-line comment warning */
/.. #     define CVT(_t)                            \
/..         binop( Iop_F64toI32,                    \
/..                mkexpr(rmode),                   \
/..                unop( Iop_F32toF64,              \
/..                      unop( Iop_ReinterpI32asF32, mkexpr(_t))) )
#endif /* stop gcc multi-line comment warning */
//..       
//..       putXMMRegLane32( gregOfRM(modrm), 3, CVT(t3) );
//..       putXMMRegLane32( gregOfRM(modrm), 2, CVT(t2) );
//..       putXMMRegLane32( gregOfRM(modrm), 1, CVT(t1) );
//..       putXMMRegLane32( gregOfRM(modrm), 0, CVT(t0) );
//.. 
//.. #     undef CVT
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 0F 5A = CVTPS2PD -- convert 2 x F32 in low half mem/xmm to 2 x
//..       F64 in xmm(G). */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0x5A) {
//..       IRTemp f32lo = newTemp(Ity_F32);
//..       IRTemp f32hi = newTemp(Ity_F32);
//.. 
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          assign( f32lo, getXMMRegLane32F(eregOfRM(modrm), 0) );
//..          assign( f32hi, getXMMRegLane32F(eregOfRM(modrm), 1) );
//..          delta += 2+1;
//..          DIP("cvtps2pd %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//.. 	 assign( f32lo, loadLE(Ity_F32, mkexpr(addr)) );
//.. 	 assign( f32hi, loadLE(Ity_F32, 
//..                                binop(Iop_Add32,mkexpr(addr),mkU32(4))) );
//..          delta += 2+alen;
//..          DIP("cvtps2pd %s,%s\n", dis_buf,
//..                                  nameXMMReg(gregOfRM(modrm)) );
//..       }
//.. 
//..       putXMMRegLane64F( gregOfRM(modrm), 1,
//..                         unop(Iop_F32toF64, mkexpr(f32hi)) );
//..       putXMMRegLane64F( gregOfRM(modrm), 0,
//..                         unop(Iop_F32toF64, mkexpr(f32lo)) );
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* F2 0F 2D = CVTSD2SI -- convert F64 in mem/low half xmm to
//..       I32 in ireg, according to prevailing SSE rounding mode */
   /* F2 0F 2C = CVTTSD2SI 
      when sz==4 -- convert F64 in mem/low half xmm to I32 in ireg, 
                    truncating towards zero
      when sz==8 -- convert F64 in mem/low half xmm to I64 in ireg, 
                    truncating towards zero 
   */
   if (haveF2no66noF3(pfx) 
       && insn[0] == 0x0F 
       && ( /* insn[1] == 0x2D || */ insn[1] == 0x2C)) {
      IRTemp rmode  = newTemp(Ity_I32);
      IRTemp f64lo  = newTemp(Ity_F64);
      Bool   r2zero = toBool(insn[1] == 0x2C);
      vassert(sz == 4 || sz == 8);

      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         delta += 2+1;
         assign(f64lo, getXMMRegLane64F(eregOfRexRM(pfx,modrm), 0));
         DIP("cvt%ssd2si %s,%s\n", r2zero ? "t" : "",
                                   nameXMMReg(eregOfRexRM(pfx,modrm)),
                                   nameIReg(sz, gregOfRexRM(pfx,modrm), False));
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         assign(f64lo, loadLE(Ity_F64, mkexpr(addr)));
         delta += 2+alen;
         DIP("cvt%ssd2si %s,%s\n", r2zero ? "t" : "",
                                   dis_buf,
                                   nameIReg(sz, gregOfRexRM(pfx,modrm), False));
      }

      if (r2zero) {
         assign( rmode, mkU32((UInt)Irrm_ZERO) );
      } else {
         assign( rmode, get_sse_roundingmode() );
      }

      if (sz == 4) {
         putIReg32( gregOfRexRM(pfx,modrm),
                    binop( Iop_F64toI32, mkexpr(rmode), mkexpr(f64lo)) );
      } else {
         putIReg64( gregOfRexRM(pfx,modrm),
                    binop( Iop_F64toI64, mkexpr(rmode), mkexpr(f64lo)) );
      }

      goto decode_success;
   }

   /* F2 0F 5A = CVTSD2SS -- convert F64 in mem/low half xmm to F32 in
      low 1/4 xmm(G), according to prevailing SSE rounding mode */
   if (haveF2no66noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5A) {
      IRTemp rmode = newTemp(Ity_I32);
      IRTemp f64lo = newTemp(Ity_F64);
      vassert(sz == 4);

      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         delta += 2+1;
         assign(f64lo, getXMMRegLane64F(eregOfRexRM(pfx,modrm), 0));
         DIP("cvtsd2ss %s,%s\n", nameXMMReg(eregOfRexRM(pfx,modrm)),
                                 nameXMMReg(gregOfRexRM(pfx,modrm)));
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         assign(f64lo, loadLE(Ity_F64, mkexpr(addr)));
         delta += 2+alen;
         DIP("cvtsd2ss %s,%s\n", dis_buf,
                                 nameXMMReg(gregOfRexRM(pfx,modrm)));
      }

      assign( rmode, get_sse_roundingmode() );
      putXMMRegLane32F( 
         gregOfRexRM(pfx,modrm), 0, 
         binop( Iop_F64toF32, mkexpr(rmode), mkexpr(f64lo) )
      );

      goto decode_success;
   }

   /* F2 0F 2A = CVTSI2SD 
      when sz==4 -- convert I32 in mem/ireg to F64 in low half xmm
      when sz==8 -- convert I64 in mem/ireg to F64 in low half xmm
   */
   if (haveF2no66noF3(pfx) && (sz == 4 || sz == 8)
       && insn[0] == 0x0F && insn[1] == 0x2A) {
      modrm = getUChar(delta+2);

      if (sz == 4) {
         IRTemp arg32 = newTemp(Ity_I32);
         if (epartIsReg(modrm)) {
            assign( arg32, getIReg32(eregOfRexRM(pfx,modrm)) );
            delta += 2+1;
            DIP("cvtsi2sd %s,%s\n", nameIReg32(eregOfRexRM(pfx,modrm)),
                                    nameXMMReg(gregOfRexRM(pfx,modrm)));
         } else {
            addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
            assign( arg32, loadLE(Ity_I32, mkexpr(addr)) );
            delta += 2+alen;
            DIP("cvtsi2sd %s,%s\n", dis_buf,
                                    nameXMMReg(gregOfRexRM(pfx,modrm)) );
         }
         putXMMRegLane64F( gregOfRexRM(pfx,modrm), 0,
                           unop(Iop_I32toF64, mkexpr(arg32)) 
         );
      } else {
         /* sz == 8 */
         IRTemp arg64 = newTemp(Ity_I64);
         if (epartIsReg(modrm)) {
            assign( arg64, getIReg64(eregOfRexRM(pfx,modrm)) );
            delta += 2+1;
            DIP("cvtsi2sdq %s,%s\n", nameIReg64(eregOfRexRM(pfx,modrm)),
                                     nameXMMReg(gregOfRexRM(pfx,modrm)));
         } else {
            addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
            assign( arg64, loadLE(Ity_I64, mkexpr(addr)) );
            delta += 2+alen;
            DIP("cvtsi2sdq %s,%s\n", dis_buf,
                                     nameXMMReg(gregOfRexRM(pfx,modrm)) );
         }
         putXMMRegLane64F( 
            gregOfRexRM(pfx,modrm), 
            0,
            binop( Iop_I64toF64,
                   get_sse_roundingmode(),
                   mkexpr(arg64)
            ) 
         );

      }

      goto decode_success;
   }

   /* F3 0F 5A = CVTSS2SD -- convert F32 in mem/low 1/4 xmm to F64 in
      low half xmm(G) */
   if (haveF3no66noF2(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5A) {
      IRTemp f32lo = newTemp(Ity_F32);

      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         delta += 2+1;
         assign(f32lo, getXMMRegLane32F(eregOfRexRM(pfx,modrm), 0));
         DIP("cvtss2sd %s,%s\n", nameXMMReg(eregOfRexRM(pfx,modrm)),
                                 nameXMMReg(gregOfRexRM(pfx,modrm)));
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         assign(f32lo, loadLE(Ity_F32, mkexpr(addr)));
         delta += 2+alen;
         DIP("cvtss2sd %s,%s\n", dis_buf,
                                 nameXMMReg(gregOfRexRM(pfx,modrm)));
      }

      putXMMRegLane64F( gregOfRexRM(pfx,modrm), 0, 
                        unop( Iop_F32toF64, mkexpr(f32lo) ) );

      goto decode_success;
   }

//..    /* 66 0F E6 = CVTTPD2DQ -- convert 2 x F64 in mem/xmm to 2 x I32 in
//..       lo half xmm(G), and zero upper half, rounding towards zero */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE6) {
//..       IRTemp argV  = newTemp(Ity_V128);
//..       IRTemp rmode = newTemp(Ity_I32);
//.. 
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          assign( argV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("cvttpd2dq %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                   nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( argV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("cvttpd2dq %s,%s\n", dis_buf,
//..                                   nameXMMReg(gregOfRM(modrm)) );
//..       }
//.. 
//..       assign( rmode, mkU32((UInt)Irrm_ZERO) );
//.. 
//..       t0 = newTemp(Ity_F64);
//..       t1 = newTemp(Ity_F64);
//..       assign( t0, unop(Iop_ReinterpI64asF64, 
//..                        unop(Iop_128to64, mkexpr(argV))) );
//..       assign( t1, unop(Iop_ReinterpI64asF64, 
//..                        unop(Iop_128HIto64, mkexpr(argV))) );
//..       
#if 0 /* stop gcc multi-line comment warning */
/.. #     define CVT(_t)  binop( Iop_F64toI32,                    \
/..                              mkexpr(rmode),                   \
/..                              mkexpr(_t) )
#endif /* stop gcc multi-line comment warning */
//..       
//..       putXMMRegLane32( gregOfRM(modrm), 3, mkU32(0) );
//..       putXMMRegLane32( gregOfRM(modrm), 2, mkU32(0) );
//..       putXMMRegLane32( gregOfRM(modrm), 1, CVT(t1) );
//..       putXMMRegLane32( gregOfRM(modrm), 0, CVT(t0) );
//.. 
//.. #     undef CVT
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 5B = CVTTPS2DQ -- convert 4 x F32 in mem/xmm to 4 x I32 in
//..       xmm(G), rounding towards zero */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x5B) {
//..       IRTemp argV  = newTemp(Ity_V128);
//..       IRTemp rmode = newTemp(Ity_I32);
//..       vassert(sz == 4);
//.. 
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          assign( argV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 3+1;
//..          DIP("cvttps2dq %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                   nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//.. 	 assign( argV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 3+alen;
//..          DIP("cvttps2dq %s,%s\n", dis_buf,
//..                                   nameXMMReg(gregOfRM(modrm)) );
//..       }
//..          
//..       assign( rmode, mkU32((UInt)Irrm_ZERO) );
//..       breakup128to32s( argV, &t3, &t2, &t1, &t0 );
//.. 
//..       /* This is less than ideal.  If it turns out to be a performance
//.. 	 bottleneck it can be improved. */
#if 0 /* stop gcc multi-line comment warning */
/.. #     define CVT(_t)                            \
/..         binop( Iop_F64toI32,                    \
/..                mkexpr(rmode),                   \
/..                unop( Iop_F32toF64,              \
/..                      unop( Iop_ReinterpI32asF32, mkexpr(_t))) )
#endif /* stop gcc multi-line comment warning */
//..       
//..       putXMMRegLane32( gregOfRM(modrm), 3, CVT(t3) );
//..       putXMMRegLane32( gregOfRM(modrm), 2, CVT(t2) );
//..       putXMMRegLane32( gregOfRM(modrm), 1, CVT(t1) );
//..       putXMMRegLane32( gregOfRM(modrm), 0, CVT(t0) );
//.. 
//.. #     undef CVT
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 5E = DIVPD -- div 64Fx2 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x5E) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "divpd", Iop_Div64Fx2 );
//..       goto decode_success;
//..    }

   /* F2 0F 5E = DIVSD -- div 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x5E) {
      vassert(sz == 4);
      delta = dis_SSE_E_to_G_lo64( pfx, delta+2, "divsd", Iop_Div64F0x2 );
      goto decode_success;
   }

//..    /* 0F AE /5 = LFENCE -- flush pending operations to memory */
//..    /* 0F AE /6 = MFENCE -- flush pending operations to memory */
//..    if (insn[0] == 0x0F && insn[1] == 0xAE
//..        && epartIsReg(insn[2]) 
//..        && (gregOfRM(insn[2]) == 5 || gregOfRM(insn[2]) == 6)) {
//..       vassert(sz == 4);
//..       delta += 3;
//..       /* Insert a memory fence.  It's sometimes important that these
//..          are carried through to the generated code. */
//..       stmt( IRStmt_MFence() );
//..       DIP("%sfence\n", gregOfRM(insn[2])==5 ? "l" : "m");
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 5F = MAXPD -- max 64Fx2 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x5F) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "maxpd", Iop_Max64Fx2 );
//..       goto decode_success;
//..    }

   /* F2 0F 5F = MAXSD -- max 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5F) {
      delta = dis_SSE_E_to_G_lo64( pfx, delta+2, "maxsd", Iop_Max64F0x2 );
      goto decode_success;
   }

//..    /* 66 0F 5D = MINPD -- min 64Fx2 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x5D) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "minpd", Iop_Min64Fx2 );
//..       goto decode_success;
//..    }

   /* F2 0F 5D = MINSD -- min 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x5D) {
      delta = dis_SSE_E_to_G_lo64( pfx, delta+2, "minsd", Iop_Min64F0x2 );
      goto decode_success;
   }

   /* 66 0F 28 = MOVAPD -- move from E (mem or xmm) to G (xmm). */
   /* 66 0F 10 = MOVUPD -- move from E (mem or xmm) to G (xmm). */
   /* 66 0F 6F = MOVDQA -- move from E (mem or xmm) to G (xmm). */
   if (have66noF2noF3(pfx) && sz == 2 
       && insn[0] == 0x0F 
       && (insn[1] == 0x28 || insn[1] == 0x10 || insn[1] == 0x6F)) {
      HChar* wot = insn[1]==0x28 ? "apd" :
                   insn[1]==0x10 ? "upd" : "dqa";
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         putXMMReg( gregOfRexRM(pfx,modrm), 
                    getXMMReg( eregOfRexRM(pfx,modrm) ));
         DIP("mov%s %s,%s\n", wot, nameXMMReg(eregOfRexRM(pfx,modrm)),
                                   nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+1;
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         putXMMReg( gregOfRexRM(pfx,modrm), 
                    loadLE(Ity_V128, mkexpr(addr)) );
         DIP("mov%s %s,%s\n", wot, dis_buf,
                                   nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+alen;
      }
      goto decode_success;
   }

//..    /* 66 0F 29 = MOVAPD -- move from G (xmm) to E (mem or xmm). */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x29) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          /* fall through; awaiting test case */
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          storeLE( mkexpr(addr), getXMMReg(gregOfRM(modrm)) );
//..          DIP("movapd %s,%s\n", nameXMMReg(gregOfRM(modrm)),
//..                                dis_buf );
//..          delta += 2+alen;
//..          goto decode_success;
//..       }
//..    }
//.. 
//..    /* 66 0F 6E = MOVD from r/m32 to xmm, zeroing high 3/4 of xmm. */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x6E) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//..          putXMMReg(
//..             gregOfRM(modrm),
//..             unop( Iop_32Uto128, getIReg(4, eregOfRM(modrm)) ) 
//..          );
//..          DIP("movd %s, %s\n", 
//..              nameIReg(4,eregOfRM(modrm)), nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode( &alen, sorb, delta+2, dis_buf );
//..          delta += 2+alen;
//..          putXMMReg(
//..             gregOfRM(modrm),
//..             unop( Iop_32Uto128,loadLE(Ity_I32, mkexpr(addr)) ) 
//..          );
//..          DIP("movd %s, %s\n", dis_buf, nameXMMReg(gregOfRM(modrm)));
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 7E = MOVD from xmm low 1/4 to r/m32. */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x7E) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//..          putIReg( 4, eregOfRM(modrm),
//..                   getXMMRegLane32(gregOfRM(modrm), 0) );
//..          DIP("movd %s, %s\n", 
//..              nameXMMReg(gregOfRM(modrm)), nameIReg(4,eregOfRM(modrm)));
//..       } else {
//..          addr = disAMode( &alen, sorb, delta+2, dis_buf );
//..          delta += 2+alen;
//..          storeLE( mkexpr(addr),
//..                   getXMMRegLane32(gregOfRM(modrm), 0) );
//..          DIP("movd %s, %s\n", nameXMMReg(gregOfRM(modrm)), dis_buf);
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 7F = MOVDQA -- move from G (xmm) to E (mem or xmm). */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x7F) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          delta += 2+1;
//..          putXMMReg( eregOfRM(modrm),
//..                     getXMMReg(gregOfRM(modrm)) );
//..          DIP("movdqa %s, %s\n", nameXMMReg(gregOfRM(modrm)), 
//..                                 nameXMMReg(eregOfRM(modrm)));
//..       } else {
//..          addr = disAMode( &alen, sorb, delta+2, dis_buf );
//..          delta += 2+alen;
//..          storeLE( mkexpr(addr), getXMMReg(gregOfRM(modrm)) );
//..          DIP("movdqa %s, %s\n", nameXMMReg(gregOfRM(modrm)), dis_buf);
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 6F = MOVDQU -- move from E (mem or xmm) to G (xmm). */
//..    /* Unfortunately can't simply use the MOVDQA case since the
//..       prefix lengths are different (66 vs F3) */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x6F) {
//..       vassert(sz == 4);
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          putXMMReg( gregOfRM(modrm), 
//..                     getXMMReg( eregOfRM(modrm) ));
//..          DIP("movdqu %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                nameXMMReg(gregOfRM(modrm)));
//..          delta += 3+1;
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//..          putXMMReg( gregOfRM(modrm), 
//..                     loadLE(Ity_V128, mkexpr(addr)) );
//..          DIP("movdqu %s,%s\n", dis_buf,
//..                                nameXMMReg(gregOfRM(modrm)));
//..          delta += 3+alen;
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 7F = MOVDQU -- move from G (xmm) to E (mem or xmm). */
//..    /* Unfortunately can't simply use the MOVDQA case since the
//..       prefix lengths are different (66 vs F3) */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x7F) {
//..       vassert(sz == 4);
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          delta += 3+1;
//..          putXMMReg( eregOfRM(modrm),
//..                     getXMMReg(gregOfRM(modrm)) );
//..          DIP("movdqu %s, %s\n", nameXMMReg(gregOfRM(modrm)), 
//..                                 nameXMMReg(eregOfRM(modrm)));
//..       } else {
//..          addr = disAMode( &alen, sorb, delta+3, dis_buf );
//..          delta += 3+alen;
//..          storeLE( mkexpr(addr), getXMMReg(gregOfRM(modrm)) );
//..          DIP("movdqu %s, %s\n", nameXMMReg(gregOfRM(modrm)), dis_buf);
//..       }
//..       goto decode_success;
//..    }
//.. 
//..    /* F2 0F D6 = MOVDQ2Q -- move from E (lo half xmm, not mem) to G (mmx). */
//..    if (insn[0] == 0xF2 && insn[1] == 0x0F && insn[2] == 0xD6) {
//..       vassert(sz == 4);
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          do_MMX_preamble();
//..          putMMXReg( gregOfRM(modrm), 
//..                     getXMMRegLane64( eregOfRM(modrm), 0 ));
//..          DIP("movdq2q %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                 nameMMXReg(gregOfRM(modrm)));
//..          delta += 3+1;
//..          goto decode_success;
//..       } else {
//..          /* fall through, apparently no mem case for this insn */
//..       }
//..    }
//.. 
//..    /* 66 0F 16 = MOVHPD -- move from mem to high half of XMM. */
//..    /* These seems identical to MOVHPS.  This instruction encoding is
//..       completely crazy. */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x16) {
//..       modrm = getUChar(delta+2);
//..       if (epartIsReg(modrm)) {
//..          /* fall through; apparently reg-reg is not possible */
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          delta += 2+alen;
//..          putXMMRegLane64( gregOfRM(modrm), 1/*upper lane*/,
//..                           loadLE(Ity_I64, mkexpr(addr)) );
//..          DIP("movhpd %s,%s\n", dis_buf, 
//..                                nameXMMReg( gregOfRM(modrm) ));
//..          goto decode_success;
//..       }
//..    }
//.. 
//..    /* 66 0F 17 = MOVHPD -- move from high half of XMM to mem. */
//..    /* Again, this seems identical to MOVHPS. */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x17) {
//..       if (!epartIsReg(insn[2])) {
//..          delta += 2;
//..          addr = disAMode ( &alen, sorb, delta, dis_buf );
//..          delta += alen;
//..          storeLE( mkexpr(addr), 
//..                   getXMMRegLane64( gregOfRM(insn[2]),
//..                                    1/*upper lane*/ ) );
//..          DIP("movhpd %s,%s\n", nameXMMReg( gregOfRM(insn[2]) ),
//..                                dis_buf);
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }

   /* 66 0F 12 = MOVLPD -- move from mem to low half of XMM. */
   /* Identical to MOVLPS ? */
   if (have66noF2noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x12) {
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         /* fall through; apparently reg-reg is not possible */
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         delta += 2+alen;
         putXMMRegLane64( gregOfRexRM(pfx,modrm),
                          0/*lower lane*/,
                          loadLE(Ity_I64, mkexpr(addr)) );
         DIP("movlpd %s, %s\n", 
             dis_buf, nameXMMReg( gregOfRexRM(pfx,modrm) ));
         goto decode_success;
      }
   }

//..    /* 66 0F 13 = MOVLPD -- move from low half of XMM to mem. */
//..    /* Identical to MOVLPS ? */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x13) {
//..       if (!epartIsReg(insn[2])) {
//..          delta += 2;
//..          addr = disAMode ( &alen, sorb, delta, dis_buf );
//..          delta += alen;
//..          storeLE( mkexpr(addr), 
//..                   getXMMRegLane64( gregOfRM(insn[2]), 
//..                                    0/*lower lane*/ ) );
//..          DIP("movlpd %s, %s\n", nameXMMReg( gregOfRM(insn[2]) ),
//..                                 dis_buf);
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }
//.. 
//..    /* 66 0F 50 = MOVMSKPD - move 2 sign bits from 2 x F64 in xmm(E) to
//..       2 lowest bits of ireg(G) */
//..    if (insn[0] == 0x0F && insn[1] == 0x50) {
//..       modrm = getUChar(delta+2);
//..       if (sz == 2 && epartIsReg(modrm)) {
//..          Int src;
//..          t0 = newTemp(Ity_I32);
//..          t1 = newTemp(Ity_I32);
//..          delta += 2+1;
//..          src = eregOfRM(modrm);
//..          assign( t0, binop( Iop_And32,
//..                             binop(Iop_Shr32, getXMMRegLane32(src,1), mkU8(31)),
//..                             mkU32(1) ));
//..          assign( t1, binop( Iop_And32,
//..                             binop(Iop_Shr32, getXMMRegLane32(src,3), mkU8(30)),
//..                             mkU32(2) ));
//..          putIReg(4, gregOfRM(modrm),
//..                     binop(Iop_Or32, mkexpr(t0), mkexpr(t1))
//..                  );
//..          DIP("movmskpd %s,%s\n", nameXMMReg(src), 
//..                                  nameIReg(4, gregOfRM(modrm)));
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }
//.. 
//..    /* 66 0F E7 = MOVNTDQ -- for us, just a plain SSE store. */
//..    if (insn[0] == 0x0F && insn[1] == 0xE7) {
//..       modrm = getUChar(delta+2);
//..       if (sz == 2 && !epartIsReg(modrm)) {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          storeLE( mkexpr(addr), getXMMReg(gregOfRM(modrm)) );
//..          DIP("movntdq %s,%s\n", dis_buf,
//..                                 nameXMMReg(gregOfRM(modrm)));
//..          delta += 2+alen;
//..          goto decode_success;
//..       }
//..       /* else fall through */
//..    }

   /* 0F C3 = MOVNTI -- for us, just a plain ireg store. */
   if (haveNo66noF2noF3(pfx) &&
       insn[0] == 0x0F && insn[1] == 0xC3) {
      vassert(sz == 4 || sz == 8);
      modrm = getUChar(delta+2);
      if (!epartIsReg(modrm)) {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         storeLE( mkexpr(addr), getIRegG(sz, pfx, modrm) );
         DIP("movnti %s,%s\n", dis_buf,
                               nameIRegG(sz, pfx, modrm));
         delta += 2+alen;
         goto decode_success;
      }
      /* else fall through */
   }

   /* 66 0F D6 = MOVQ -- move 64 bits from G (lo half xmm) to E (mem
      or lo half xmm).  */
   if (have66noF2noF3(pfx) && insn[0] == 0x0F && insn[1] == 0xD6) {
      vassert(sz == 2);
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         /* fall through, awaiting test case */
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         storeLE( mkexpr(addr), 
                  getXMMRegLane64( gregOfRexRM(pfx,modrm), 0 ));
         DIP("movq %s,%s\n", nameXMMReg(gregOfRexRM(pfx,modrm)), dis_buf );
         delta += 2+alen;
         goto decode_success;
      }
   }

//..    /* F3 0F D6 = MOVQ2DQ -- move from E (mmx) to G (lo half xmm, zero
//..       hi half). */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0xD6) {
//..       vassert(sz == 4);
//..       modrm = getUChar(delta+3);
//..       if (epartIsReg(modrm)) {
//..          do_MMX_preamble();
//..          putXMMReg( gregOfRM(modrm), 
//..                     unop(Iop_64Uto128, getMMXReg( eregOfRM(modrm) )) );
//..          DIP("movq2dq %s,%s\n", nameMMXReg(eregOfRM(modrm)),
//..                                 nameXMMReg(gregOfRM(modrm)));
//..          delta += 3+1;
//..          goto decode_success;
//..       } else {
//..          /* fall through, apparently no mem case for this insn */
//..       }
//..    }
//.. 
//..    /* F3 0F 7E = MOVQ -- move 64 bits from E (mem or lo half xmm) to
//..       G (lo half xmm).  If E is mem, upper half of G is zeroed out. */
   /* F2 0F 10 = MOVSD -- move 64 bits from E (mem or lo half xmm) to
      G (lo half xmm).  If E is mem, upper half of G is zeroed out.
      (original defn) */
   if ( (haveF2no66noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x10)
        || 
        (haveF3no66noF2(pfx) && insn[0] == 0x0F && insn[1] == 0x7E)
      ) {
      vassert(sz == 4);
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         putXMMRegLane64( gregOfRexRM(pfx,modrm), 0,
                          getXMMRegLane64( eregOfRexRM(pfx,modrm), 0 ));
         DIP("movsd %s,%s\n", nameXMMReg(eregOfRexRM(pfx,modrm)),
                              nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+1;
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         putXMMReg( gregOfRexRM(pfx,modrm), mkV128(0) );
         putXMMRegLane64( gregOfRexRM(pfx,modrm), 0,
                          loadLE(Ity_I64, mkexpr(addr)) );
         DIP("movsd %s,%s\n", dis_buf,
                              nameXMMReg(gregOfRexRM(pfx,modrm)));
         delta += 2+alen;
      }
      goto decode_success;
   }

   /* F2 0F 11 = MOVSD -- move 64 bits from G (lo half xmm) to E (mem
      or lo half xmm). */
   if (haveF2no66noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x11) {
      modrm = getUChar(delta+2);
      if (epartIsReg(modrm)) {
         /* fall through, we don't yet have a test case */
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         storeLE( mkexpr(addr),
                  getXMMRegLane64(gregOfRexRM(pfx,modrm), 0) );
         DIP("movsd %s,%s\n", nameXMMReg(gregOfRexRM(pfx,modrm)),
                              dis_buf);
         delta += 2+alen;
         goto decode_success;
      }
   }

//..    /* 66 0F 59 = MULPD -- mul 64Fx2 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x59) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "mulpd", Iop_Mul64Fx2 );
//..       goto decode_success;
//..    }

   /* F2 0F 59 = MULSD -- mul 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && sz == 4
       && insn[0] == 0x0F && insn[1] == 0x59) {
      delta = dis_SSE_E_to_G_lo64( pfx, delta+2, "mulsd", Iop_Mul64F0x2 );
      goto decode_success;
   }

   /* 66 0F 56 = ORPD -- G = G and E */
   if (have66noF2noF3(pfx) && sz == 2 
       && insn[0] == 0x0F && insn[1] == 0x56) {
      delta = dis_SSE_E_to_G_all( pfx, delta+2, "orpd", Iop_OrV128 );
      goto decode_success;
   }

//..    /* 66 0F C6 /r ib = SHUFPD -- shuffle packed F64s */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xC6) {
//..       Int    select;
//..       IRTemp sV = newTemp(Ity_V128);
//..       IRTemp dV = newTemp(Ity_V128);
//..       IRTemp s1 = newTemp(Ity_I64);
//..       IRTemp s0 = newTemp(Ity_I64);
//..       IRTemp d1 = newTemp(Ity_I64);
//..       IRTemp d0 = newTemp(Ity_I64);
//.. 
//..       modrm = insn[2];
//..       assign( dV, getXMMReg(gregOfRM(modrm)) );
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          select = (Int)insn[3];
//..          delta += 2+2;
//..          DIP("shufpd $%d,%s,%s\n", select, 
//..                                    nameXMMReg(eregOfRM(modrm)),
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//..          select = (Int)insn[2+alen];
//..          delta += 3+alen;
//..          DIP("shufpd $%d,%s,%s\n", select, 
//..                                    dis_buf,
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       }
//.. 
//..       assign( d1, unop(Iop_128HIto64, mkexpr(dV)) );
//..       assign( d0, unop(Iop_128to64,   mkexpr(dV)) );
//..       assign( s1, unop(Iop_128HIto64, mkexpr(sV)) );
//..       assign( s0, unop(Iop_128to64,   mkexpr(sV)) );
//.. 
//.. #     define SELD(n) mkexpr((n)==0 ? d0 : d1)
//.. #     define SELS(n) mkexpr((n)==0 ? s0 : s1)
//.. 
//..       putXMMReg(
//..          gregOfRM(modrm), 
//..          binop(Iop_64HLto128, SELS((select>>1)&1), SELD((select>>0)&1) )
//..       );
//.. 
//.. #     undef SELD
//.. #     undef SELS
//.. 
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 51 = SQRTPD -- approx sqrt 64Fx2 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x51) {
//..       delta = dis_SSE_E_to_G_unary_all( sorb, delta+2, 
//..                                         "sqrtpd", Iop_Sqrt64Fx2 );
//..       goto decode_success;
//..    }

   /* F2 0F 51 = SQRTSD -- approx sqrt 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x51) {
      vassert(sz == 4);
      delta = dis_SSE_E_to_G_unary_lo64( pfx, delta+2, 
                                         "sqrtsd", Iop_Sqrt64F0x2 );
      goto decode_success;
   }

//..    /* 66 0F 5C = SUBPD -- sub 64Fx2 from R/M to R */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x5C) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "subpd", Iop_Sub64Fx2 );
//..       goto decode_success;
//..    }

   /* F2 0F 5C = SUBSD -- sub 64F0x2 from R/M to R */
   if (haveF2no66noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x5C) {
      vassert(sz == 4);
      delta = dis_SSE_E_to_G_lo64( pfx, delta+2, "subsd", Iop_Sub64F0x2 );
      goto decode_success;
   }

   /* 66 0F 15 = UNPCKHPD -- unpack and interleave high part F64s */
   /* 66 0F 14 = UNPCKLPD -- unpack and interleave low part F64s */
   /* These just appear to be special cases of SHUFPS */
   if (have66noF2noF3(pfx) 
       && sz == 2 /* could be 8 if rex also present */
       && insn[0] == 0x0F && (insn[1] == 0x15 || insn[1] == 0x14)) {
      IRTemp s1 = newTemp(Ity_I64);
      IRTemp s0 = newTemp(Ity_I64);
      IRTemp d1 = newTemp(Ity_I64);
      IRTemp d0 = newTemp(Ity_I64);
      IRTemp sV = newTemp(Ity_V128);
      IRTemp dV = newTemp(Ity_V128);
      Bool   hi = toBool(insn[1] == 0x15);

      modrm = insn[2];
      assign( dV, getXMMReg(gregOfRexRM(pfx,modrm)) );

      if (epartIsReg(modrm)) {
         assign( sV, getXMMReg(eregOfRexRM(pfx,modrm)) );
         delta += 2+1;
         DIP("unpck%sps %s,%s\n", hi ? "h" : "l",
                                  nameXMMReg(eregOfRexRM(pfx,modrm)),
                                  nameXMMReg(gregOfRexRM(pfx,modrm)));
      } else {
         addr = disAMode ( &alen, pfx, delta+2, dis_buf, 0 );
         assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
         delta += 2+alen;
         DIP("unpck%sps %s,%s\n", hi ? "h" : "l",
                                  dis_buf,
                                  nameXMMReg(gregOfRexRM(pfx,modrm)));
      }

      assign( d1, unop(Iop_V128HIto64, mkexpr(dV)) );
      assign( d0, unop(Iop_V128to64,   mkexpr(dV)) );
      assign( s1, unop(Iop_V128HIto64, mkexpr(sV)) );
      assign( s0, unop(Iop_V128to64,   mkexpr(sV)) );

      if (hi) {
         putXMMReg( gregOfRexRM(pfx,modrm), 
                    binop(Iop_64HLtoV128, mkexpr(s1), mkexpr(d1)) );
      } else {
         putXMMReg( gregOfRexRM(pfx,modrm), 
                    binop(Iop_64HLtoV128, mkexpr(s0), mkexpr(d0)) );
      }

      goto decode_success;
   }

   /* 66 0F 57 = XORPD -- G = G xor E */
   if (have66noF2noF3(pfx) && insn[0] == 0x0F && insn[1] == 0x57) {
      delta = dis_SSE_E_to_G_all( pfx, delta+2, "xorpd", Iop_XorV128 );
      goto decode_success;
   }

//..    /* 66 0F 6B = PACKSSDW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x6B) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "packssdw", Iop_QNarrow32Sx4, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 63 = PACKSSWB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x63) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "packsswb", Iop_QNarrow16Sx8, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 67 = PACKUSWB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x67) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "packuswb", Iop_QNarrow16Ux8, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F FC = PADDB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xFC) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddb", Iop_Add8x16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F FE = PADDD */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xFE) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddd", Iop_Add32x4, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE2 ---*** */
//..    /* 0F D4 = PADDQ -- add 64x1 */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xD4) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "paddq", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D4 = PADDQ */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD4) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddq", Iop_Add64x2, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F FD = PADDW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xFD) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddw", Iop_Add16x8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F EC = PADDSB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xEC) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddsb", Iop_QAdd8Sx16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F ED = PADDSW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xED) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddsw", Iop_QAdd16Sx8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F DC = PADDUSB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xDC) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddusb", Iop_QAdd8Ux16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F DD = PADDUSW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xDD) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "paddusw", Iop_QAdd16Ux8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F DB = PAND */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xDB) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "pand", Iop_And128 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F DF = PANDN */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xDF) {
//..       delta = dis_SSE_E_to_G_all_invG( sorb, delta+2, "pandn", Iop_And128 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E0 = PAVGB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE0) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pavgb", Iop_Avg8Ux16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E3 = PAVGW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE3) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pavgw", Iop_Avg16Ux8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 74 = PCMPEQB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x74) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pcmpeqb", Iop_CmpEQ8x16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 76 = PCMPEQD */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x76) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pcmpeqd", Iop_CmpEQ32x4, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 75 = PCMPEQW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x75) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pcmpeqw", Iop_CmpEQ16x8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 64 = PCMPGTB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x64) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pcmpgtb", Iop_CmpGT8Sx16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 66 = PCMPGTD */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x66) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pcmpgtd", Iop_CmpGT32Sx4, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 65 = PCMPGTW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x65) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pcmpgtw", Iop_CmpGT16Sx8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F C5 = PEXTRW -- extract 16-bit field from xmm(E) and put 
//..       zero-extend of it in ireg(G). */
//..    if (insn[0] == 0x0F && insn[1] == 0xC5) {
//..       modrm = insn[2];
//..       if (sz == 2 && epartIsReg(modrm)) {
//..          t5 = newTemp(Ity_V128);
//..          t4 = newTemp(Ity_I16);
//..          assign(t5, getXMMReg(eregOfRM(modrm)));
//..          breakup128to32s( t5, &t3, &t2, &t1, &t0 );
//..          switch (insn[3] & 7) {
//..             case 0:  assign(t4, unop(Iop_32to16,   mkexpr(t0))); break;
//..             case 1:  assign(t4, unop(Iop_32HIto16, mkexpr(t0))); break;
//..             case 2:  assign(t4, unop(Iop_32to16,   mkexpr(t1))); break;
//..             case 3:  assign(t4, unop(Iop_32HIto16, mkexpr(t1))); break;
//..             case 4:  assign(t4, unop(Iop_32to16,   mkexpr(t2))); break;
//..             case 5:  assign(t4, unop(Iop_32HIto16, mkexpr(t2))); break;
//..             case 6:  assign(t4, unop(Iop_32to16,   mkexpr(t3))); break;
//..             case 7:  assign(t4, unop(Iop_32HIto16, mkexpr(t3))); break;
//..             default: vassert(0);
//..          }
//..          putIReg(4, gregOfRM(modrm), unop(Iop_16Uto32, mkexpr(t4)));
//..          DIP("pextrw $%d,%s,%s\n",
//..              (Int)insn[3], nameXMMReg(eregOfRM(modrm)),
//..                            nameIReg(4,gregOfRM(modrm)));
//..          delta += 4;
//..          goto decode_success;
//..       } 
//..       /* else fall through */
//..    }
//.. 
//..    /* 66 0F C4 = PINSRW -- get 16 bits from E(mem or low half ireg) and
//..       put it into the specified lane of xmm(G). */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xC4) {
//..       Int lane;
//..       t4 = newTemp(Ity_I16);
//..       modrm = insn[2];
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign(t4, getIReg(2, eregOfRM(modrm)));
//..          lane = insn[3];
//..          delta += 2+2;
//..          DIP("pinsrw $%d,%s,%s\n", (Int)lane, 
//..                                    nameIReg(2,eregOfRM(modrm)),
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          /* awaiting test case */
//..          goto decode_failure;
//..       }
//.. 
//..       putXMMRegLane16( gregOfRM(modrm), lane & 7, mkexpr(t4) );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F EE = PMAXSW -- 16x8 signed max */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xEE) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pmaxsw", Iop_Max16Sx8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F DE = PMAXUB -- 8x16 unsigned max */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xDE) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pmaxub", Iop_Max8Ux16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F EA = PMINSW -- 16x8 signed min */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xEA) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pminsw", Iop_Min16Sx8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F DA = PMINUB -- 8x16 unsigned min */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xDA) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pminub", Iop_Min8Ux16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D7 = PMOVMSKB -- extract sign bits from each of 16 lanes in
//..       xmm(G), turn them into a byte, and put zero-extend of it in
//..       ireg(G).  Doing this directly is just too cumbersome; give up
//..       therefore and call a helper. */
//..    /* UInt x86g_calculate_sse_pmovmskb ( ULong w64hi, ULong w64lo ); */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD7) {
//..       modrm = insn[2];
//..       if (epartIsReg(modrm)) {
//..          t0 = newTemp(Ity_I64);
//..          t1 = newTemp(Ity_I64);
//..          assign(t0, getXMMRegLane64(eregOfRM(modrm), 0));
//..          assign(t1, getXMMRegLane64(eregOfRM(modrm), 1));
//..          t5 = newTemp(Ity_I32);
//..          assign(t5, mkIRExprCCall(
//..                        Ity_I32, 0/*regparms*/, 
//..                        "x86g_calculate_sse_pmovmskb",
//..                        &x86g_calculate_sse_pmovmskb,
//..                        mkIRExprVec_2( mkexpr(t1), mkexpr(t0) )));
//..          putIReg(4, gregOfRM(modrm), mkexpr(t5));
//..          DIP("pmovmskb %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                  nameIReg(4,gregOfRM(modrm)));
//..          delta += 3;
//..          goto decode_success;
//..       } 
//..       /* else fall through */
//..    }
//.. 
//..    /* 66 0F E4 = PMULHUW -- 16x8 hi-half of unsigned widening multiply */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE4) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pmulhuw", Iop_MulHi16Ux8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E5 = PMULHW -- 16x8 hi-half of signed widening multiply */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE5) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pmulhw", Iop_MulHi16Sx8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D5 = PMULHL -- 16x8 multiply */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD5) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "pmullw", Iop_Mul16x8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE2 ---*** */
//..    /* 0F F4 = PMULUDQ -- unsigned widening multiply of 32-lanes 0 x
//..       0 to form 64-bit result */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xF4) {
//..       IRTemp sV = newTemp(Ity_I64);
//..       IRTemp dV = newTemp(Ity_I64);
//..       t1 = newTemp(Ity_I32);
//..       t0 = newTemp(Ity_I32);
//..       modrm = insn[2];
//.. 
//..       do_MMX_preamble();
//..       assign( dV, getMMXReg(gregOfRM(modrm)) );
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getMMXReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("pmuludq %s,%s\n", nameMMXReg(eregOfRM(modrm)),
//..                                 nameMMXReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_I64, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("pmuludq %s,%s\n", dis_buf,
//..                                 nameMMXReg(gregOfRM(modrm)));
//..       }
//.. 
//..       assign( t0, unop(Iop_64to32, mkexpr(dV)) );
//..       assign( t1, unop(Iop_64to32, mkexpr(sV)) );
//..       putMMXReg( gregOfRM(modrm),
//..                  binop( Iop_MullU32, mkexpr(t0), mkexpr(t1) ) );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F F4 = PMULUDQ -- unsigned widening multiply of 32-lanes 0 x
//..       0 to form lower 64-bit half and lanes 2 x 2 to form upper 64-bit
//..       half */
//..    /* This is a really poor translation -- could be improved if
//..       performance critical */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xF4) {
//..       IRTemp sV, dV;
//..       IRTemp s3, s2, s1, s0, d3, d2, d1, d0;
//..       sV = newTemp(Ity_V128);
//..       dV = newTemp(Ity_V128);
//..       s3 = s2 = s1 = s0 = d3 = d2 = d1 = d0 = IRTemp_INVALID;
//..       t1 = newTemp(Ity_I64);
//..       t0 = newTemp(Ity_I64);
//..       modrm = insn[2];
//..       assign( dV, getXMMReg(gregOfRM(modrm)) );
//.. 
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          delta += 2+1;
//..          DIP("pmuludq %s,%s\n", nameXMMReg(eregOfRM(modrm)),
//..                                 nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//..          delta += 2+alen;
//..          DIP("pmuludq %s,%s\n", dis_buf,
//..                                 nameXMMReg(gregOfRM(modrm)));
//..       }
//.. 
//..       breakup128to32s( dV, &d3, &d2, &d1, &d0 );
//..       breakup128to32s( sV, &s3, &s2, &s1, &s0 );
//.. 
//..       assign( t0, binop( Iop_MullU32, mkexpr(d0), mkexpr(s0)) );
//..       putXMMRegLane64( gregOfRM(modrm), 0, mkexpr(t0) );
//..       assign( t1, binop( Iop_MullU32, mkexpr(d2), mkexpr(s2)) );
//..       putXMMRegLane64( gregOfRM(modrm), 1, mkexpr(t1) );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F EB = POR */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xEB) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "por", Iop_Or128 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 70 = PSHUFD -- rearrange 4x32 from E(xmm or mem) to G(xmm) */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x70) {
//..       Int order;
//..       IRTemp sV, dV, s3, s2, s1, s0;
//..       s3 = s2 = s1 = s0 = IRTemp_INVALID;
//..       sV = newTemp(Ity_V128);
//..       dV = newTemp(Ity_V128);
//..       modrm = insn[2];
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          order = (Int)insn[3];
//..          delta += 2+2;
//..          DIP("pshufd $%d,%s,%s\n", order, 
//..                                    nameXMMReg(eregOfRM(modrm)),
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+2, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//.. 	 order = (Int)insn[2+alen];
//..          delta += 3+alen;
//..          DIP("pshufd $%d,%s,%s\n", order, 
//..                                    dis_buf,
//..                                    nameXMMReg(gregOfRM(modrm)));
//..       }
//..       breakup128to32s( sV, &s3, &s2, &s1, &s0 );
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #     define SEL(n) \
/..                 ((n)==0 ? s0 : ((n)==1 ? s1 : ((n)==2 ? s2 : s3)))
#endif /* stop gcc multi-line comment warning */
//..       assign(dV,
//.. 	     mk128from32s( SEL((order>>6)&3), SEL((order>>4)&3),
//..                            SEL((order>>2)&3), SEL((order>>0)&3) )
//..       );
//..       putXMMReg(gregOfRM(modrm), mkexpr(dV));
//.. #     undef SEL
//..       goto decode_success;
//..    }
//.. 
//..    /* F3 0F 70 = PSHUFHW -- rearrange upper half 4x16 from E(xmm or
//..       mem) to G(xmm), and copy lower half */
//..    if (insn[0] == 0xF3 && insn[1] == 0x0F && insn[2] == 0x70) {
//..       Int order;
//..       IRTemp sVhi, dVhi, sV, dV, s3, s2, s1, s0;
//..       s3 = s2 = s1 = s0 = IRTemp_INVALID;
//..       sV   = newTemp(Ity_V128);
//..       dV   = newTemp(Ity_V128);
//..       sVhi = newTemp(Ity_I64);
//..       dVhi = newTemp(Ity_I64);
//..       modrm = insn[3];
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          order = (Int)insn[4];
//..          delta += 4+1;
//..          DIP("pshufhw $%d,%s,%s\n", order, 
//..                                     nameXMMReg(eregOfRM(modrm)),
//..                                     nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//.. 	 order = (Int)insn[3+alen];
//..          delta += 4+alen;
//..          DIP("pshufhw $%d,%s,%s\n", order, 
//..                                     dis_buf,
//..                                     nameXMMReg(gregOfRM(modrm)));
//..       }
//..       assign( sVhi, unop(Iop_128HIto64, mkexpr(sV)) );
//..       breakup64to16s( sVhi, &s3, &s2, &s1, &s0 );
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #     define SEL(n) \
/..                 ((n)==0 ? s0 : ((n)==1 ? s1 : ((n)==2 ? s2 : s3)))
#endif /* stop gcc multi-line comment warning */
//..       assign(dVhi,
//.. 	     mk64from16s( SEL((order>>6)&3), SEL((order>>4)&3),
//..                           SEL((order>>2)&3), SEL((order>>0)&3) )
//..       );
//..       assign(dV, binop( Iop_64HLto128, 
//..                         mkexpr(dVhi),
//..                         unop(Iop_128to64, mkexpr(sV))) );
//..       putXMMReg(gregOfRM(modrm), mkexpr(dV));
//.. #     undef SEL
//..       goto decode_success;
//..    }
//.. 
//..    /* F2 0F 70 = PSHUFLW -- rearrange lower half 4x16 from E(xmm or
//..       mem) to G(xmm), and copy upper half */
//..    if (insn[0] == 0xF2 && insn[1] == 0x0F && insn[2] == 0x70) {
//..       Int order;
//..       IRTemp sVlo, dVlo, sV, dV, s3, s2, s1, s0;
//..       s3 = s2 = s1 = s0 = IRTemp_INVALID;
//..       sV   = newTemp(Ity_V128);
//..       dV   = newTemp(Ity_V128);
//..       sVlo = newTemp(Ity_I64);
//..       dVlo = newTemp(Ity_I64);
//..       modrm = insn[3];
//..       if (epartIsReg(modrm)) {
//..          assign( sV, getXMMReg(eregOfRM(modrm)) );
//..          order = (Int)insn[4];
//..          delta += 4+1;
//..          DIP("pshuflw $%d,%s,%s\n", order, 
//..                                     nameXMMReg(eregOfRM(modrm)),
//..                                     nameXMMReg(gregOfRM(modrm)));
//..       } else {
//..          addr = disAMode ( &alen, sorb, delta+3, dis_buf );
//..          assign( sV, loadLE(Ity_V128, mkexpr(addr)) );
//.. 	 order = (Int)insn[3+alen];
//..          delta += 4+alen;
//..          DIP("pshuflw $%d,%s,%s\n", order, 
//..                                     dis_buf,
//..                                     nameXMMReg(gregOfRM(modrm)));
//..       }
//..       assign( sVlo, unop(Iop_128to64, mkexpr(sV)) );
//..       breakup64to16s( sVlo, &s3, &s2, &s1, &s0 );
//.. 
#if 0 /* stop gcc multi-line comment warning */
/.. #     define SEL(n) \
/..                 ((n)==0 ? s0 : ((n)==1 ? s1 : ((n)==2 ? s2 : s3)))
#endif /* stop gcc multi-line comment warning */
//..       assign(dVlo,
//.. 	     mk64from16s( SEL((order>>6)&3), SEL((order>>4)&3),
//..                           SEL((order>>2)&3), SEL((order>>0)&3) )
//..       );
//..       assign(dV, binop( Iop_64HLto128,
//..                         unop(Iop_128HIto64, mkexpr(sV)),
//..                         mkexpr(dVlo) ) );
//..       putXMMReg(gregOfRM(modrm), mkexpr(dV));
//.. #     undef SEL
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 72 /6 ib = PSLLD by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x72
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 6) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "pslld", Iop_ShlN32x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F F2 = PSLLD by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xF2) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "pslld", Iop_ShlN32x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 73 /7 ib = PSLLDQ by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x73
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 7) {
//..       IRTemp sV, dV, hi64, lo64, hi64r, lo64r;
//..       Int    imm = (Int)insn[3];
//..       Int    reg = eregOfRM(insn[2]);
//..       DIP("pslldq $%d,%s\n", imm, nameXMMReg(reg));
//..       vassert(imm >= 0 && imm <= 255);
//..       delta += 4;
//.. 
//..       sV    = newTemp(Ity_V128);
//..       dV    = newTemp(Ity_V128);
//..       hi64  = newTemp(Ity_I64);
//..       lo64  = newTemp(Ity_I64);
//..       hi64r = newTemp(Ity_I64);
//..       lo64r = newTemp(Ity_I64);
//.. 
//..       if (imm >= 16) {
//..          vassert(0); /* awaiting test case */
//..          putXMMReg(reg, mkV128(0x0000));
//..          goto decode_success;
//..       }
//.. 
//..       assign( sV, getXMMReg(reg) );
//..       assign( hi64, unop(Iop_128HIto64, mkexpr(sV)) );
//..       assign( lo64, unop(Iop_128to64, mkexpr(sV)) );
//.. 
//..       if (imm == 8) {
//..          assign( lo64r, mkU64(0) );
//..          assign( hi64r, mkexpr(lo64) );
//..       }
//..       else
//..       if (imm > 8) {
//..          vassert(0); /* awaiting test case */
//..          assign( lo64r, mkU64(0) );
//..          assign( hi64r, binop( Iop_Shl64, 
//..                                mkexpr(lo64),
//..                                mkU8( 8*(imm-8) ) ));
//..       } else {
//..          assign( lo64r, binop( Iop_Shl64, 
//..                                mkexpr(lo64),
//..                                mkU8(8 * imm) ));
//..          assign( hi64r, 
//..                  binop( Iop_Or64,
//..                         binop(Iop_Shl64, mkexpr(hi64), 
//..                                          mkU8(8 * imm)),
//..                         binop(Iop_Shr64, mkexpr(lo64),
//..                                          mkU8(8 * (8 - imm)) )
//..                       )
//..                );
//..       }
//..       assign( dV, binop(Iop_64HLto128, mkexpr(hi64r), mkexpr(lo64r)) );
//..       putXMMReg(reg, mkexpr(dV));
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 73 /6 ib = PSLLQ by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x73
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 6) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psllq", Iop_ShlN64x2 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F F3 = PSLLQ by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xF3) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psllq", Iop_ShlN64x2 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 71 /6 ib = PSLLW by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x71
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 6) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psllw", Iop_ShlN16x8 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F F1 = PSLLW by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xF1) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psllw", Iop_ShlN16x8 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 72 /4 ib = PSRAD by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x72
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 4) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psrad", Iop_SarN32x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E2 = PSRAD by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE2) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psrad", Iop_SarN32x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 71 /4 ib = PSRAW by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x71
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 4) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psraw", Iop_SarN16x8 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E1 = PSRAW by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE1) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psraw", Iop_SarN16x8 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 72 /2 ib = PSRLD by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x72
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 2) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psrld", Iop_ShrN32x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D2 = PSRLD by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD2) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psrld", Iop_ShrN32x4 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 73 /3 ib = PSRLDQ by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x73
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 3) {
//..       IRTemp sV, dV, hi64, lo64, hi64r, lo64r;
//..       Int    imm = (Int)insn[3];
//..       Int    reg = eregOfRM(insn[2]);
//..       DIP("psrldq $%d,%s\n", imm, nameXMMReg(reg));
//..       vassert(imm >= 0 && imm <= 255);
//..       delta += 4;
//.. 
//..       sV    = newTemp(Ity_V128);
//..       dV    = newTemp(Ity_V128);
//..       hi64  = newTemp(Ity_I64);
//..       lo64  = newTemp(Ity_I64);
//..       hi64r = newTemp(Ity_I64);
//..       lo64r = newTemp(Ity_I64);
//.. 
//..       if (imm >= 16) {
//..          vassert(0); /* awaiting test case */
//..          putXMMReg(reg, mkV128(0x0000));
//..          goto decode_success;
//..       }
//.. 
//..       assign( sV, getXMMReg(reg) );
//..       assign( hi64, unop(Iop_128HIto64, mkexpr(sV)) );
//..       assign( lo64, unop(Iop_128to64, mkexpr(sV)) );
//.. 
//..       if (imm == 8) {
//..          assign( hi64r, mkU64(0) );
//..          assign( lo64r, mkexpr(hi64) );
//..       }
//..       else 
//..       if (imm > 8) {
//..          vassert(0); /* awaiting test case */
//..          assign( hi64r, mkU64(0) );
//..          assign( lo64r, binop( Iop_Shr64, 
//..                                mkexpr(hi64),
//..                                mkU8( 8*(imm-8) ) ));
//..       } else {
//..          assign( hi64r, binop( Iop_Shr64, 
//..                                mkexpr(hi64),
//..                                mkU8(8 * imm) ));
//..          assign( lo64r, 
//..                  binop( Iop_Or64,
//..                         binop(Iop_Shr64, mkexpr(lo64), 
//..                                          mkU8(8 * imm)),
//..                         binop(Iop_Shl64, mkexpr(hi64),
//..                                          mkU8(8 * (8 - imm)) )
//..                       )
//..                );
//..       }
//.. 
//..       assign( dV, binop(Iop_64HLto128, mkexpr(hi64r), mkexpr(lo64r)) );
//..       putXMMReg(reg, mkexpr(dV));
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 73 /2 ib = PSRLQ by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x73
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 2) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psrlq", Iop_ShrN64x2 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D3 = PSRLQ by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD3) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psrlq", Iop_ShrN64x2 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 71 /2 ib = PSRLW by immediate */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x71
//..        && epartIsReg(insn[2])
//..        && gregOfRM(insn[2]) == 2) {
//..       delta = dis_SSE_shiftE_imm( delta+2, "psrlw", Iop_ShrN16x8 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D1 = PSRLW by E */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD1) {
//..       delta = dis_SSE_shiftG_byE( sorb, delta+2, "psrlw", Iop_ShrN16x8 );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F F8 = PSUBB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xF8) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubb", Iop_Sub8x16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F FA = PSUBD */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xFA) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubd", Iop_Sub32x4, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* ***--- this is an MMX class insn introduced in SSE2 ---*** */
//..    /* 0F FB = PSUBQ -- sub 64x1 */
//..    if (sz == 4 && insn[0] == 0x0F && insn[1] == 0xFB) {
//..       do_MMX_preamble();
//..       delta = dis_MMXop_regmem_to_reg ( 
//..                 sorb, delta+2, insn[1], "psubq", False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F FB = PSUBQ */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xFB) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubq", Iop_Sub64x2, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F F9 = PSUBW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xF9) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubw", Iop_Sub16x8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E8 = PSUBSB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE8) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubsb", Iop_QSub8Sx16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F E9 = PSUBSW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xE9) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubsw", Iop_QSub16Sx8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D8 = PSUBSB */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD8) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubusb", Iop_QSub8Ux16, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F D9 = PSUBSW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xD9) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "psubusw", Iop_QSub16Ux8, False );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 68 = PUNPCKHBW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x68) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpckhbw",
//..                                  Iop_InterleaveHI8x16, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 6A = PUNPCKHDQ */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x6A) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpckhdq",
//..                                  Iop_InterleaveHI32x4, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 6D = PUNPCKHQDQ */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x6D) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpckhqdq",
//..                                  Iop_InterleaveHI64x2, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 69 = PUNPCKHWD */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x69) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpckhwd",
//..                                  Iop_InterleaveHI16x8, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 60 = PUNPCKLBW */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x60) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpcklbw",
//..                                  Iop_InterleaveLO8x16, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 62 = PUNPCKLDQ */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x62) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpckldq",
//..                                  Iop_InterleaveLO32x4, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 6C = PUNPCKLQDQ */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x6C) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpcklqdq",
//..                                  Iop_InterleaveLO64x2, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F 61 = PUNPCKLWD */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0x61) {
//..       delta = dis_SSEint_E_to_G( sorb, delta+2, 
//..                                  "punpcklwd",
//..                                  Iop_InterleaveLO16x8, True );
//..       goto decode_success;
//..    }
//.. 
//..    /* 66 0F EF = PXOR */
//..    if (sz == 2 && insn[0] == 0x0F && insn[1] == 0xEF) {
//..       delta = dis_SSE_E_to_G_all( sorb, delta+2, "pxor", Iop_Xor128 );
//..       goto decode_success;
//..    }
//.. 
//.. 
//.. //--    /* FXSAVE/FXRSTOR m32 -- load/store the FPU/MMX/SSE state. */
//.. //--    if (insn[0] == 0x0F && insn[1] == 0xAE 
//.. //--        && (!epartIsReg(insn[2]))
//.. //--        && (gregOfRM(insn[2]) == 1 || gregOfRM(insn[2]) == 0) ) {
//.. //--       Bool store = gregOfRM(insn[2]) == 0;
//.. //--       vg_assert(sz == 4);
//.. //--       pair = disAMode ( cb, sorb, eip+2, dis_buf );
//.. //--       t1   = LOW24(pair);
//.. //--       eip += 2+HI8(pair);
//.. //--       uInstr3(cb, store ? SSE2a_MemWr : SSE2a_MemRd, 512,
//.. //--                   Lit16, (((UShort)insn[0]) << 8) | (UShort)insn[1],
//.. //--                   Lit16, (UShort)insn[2],
//.. //--                   TempReg, t1 );
//.. //--       DIP("fx%s %s\n", store ? "save" : "rstor", dis_buf );
//.. //--       goto decode_success;
//.. //--    }
//.. //-- 
//.. //--    /* CLFLUSH -- flush cache line */
//.. //--    if (insn[0] == 0x0F && insn[1] == 0xAE
//.. //--        && (!epartIsReg(insn[2]))
//.. //--        && (gregOfRM(insn[2]) == 7))
//.. //--    {
//.. //--       vg_assert(sz == 4);
//.. //--       pair = disAMode ( cb, sorb, eip+2, dis_buf );
//.. //--       t1   = LOW24(pair);
//.. //--       eip += 2+HI8(pair);
//.. //--       uInstr3(cb, SSE2a_MemRd, 0,  /* ignore sz for internal ops */
//.. //--                   Lit16, (((UShort)0x0F) << 8) | (UShort)0xAE,
//.. //--                   Lit16, (UShort)insn[2],
//.. //--                   TempReg, t1 );
//.. //--       DIP("clflush %s\n", dis_buf);
//.. //--       goto decode_success;
//.. //--    }


   /* ---------------------------------------------------- */
   /* --- end of the SSE/SSE2 decoder.                 --- */
   /* ---------------------------------------------------- */

   /*after_sse_decoders:*/

   /* Get the primary opcode. */
   opc = getUChar(delta); delta++;

   /* We get here if the current insn isn't SSE, or this CPU doesn't
      support SSE. */

   switch (opc) {

   /* ------------------------ Control flow --------------- */

//..    case 0xC2: /* RET imm16 */
//..       d32 = getUDisp16(delta); 
//..       delta += 2;
//..       dis_ret(d32);
//..       whatNext = Dis_StopHere;
//..       DIP("ret %d\n", d32);
//..       break;
   case 0xC3: /* RET */
      if (haveF2(pfx)) goto decode_failure;
      /* F3 is acceptable on AMD. */
      dis_ret(0);
      whatNext = Dis_StopHere;
      DIP(haveF3(pfx) ? "rep ; ret\n" : "ret\n");
      break;
      
   case 0xE8: /* CALL J4 */
      if (haveF2orF3(pfx)) goto decode_failure;
      d64 = getSDisp32(delta); delta += 4;
      d64 += (guest_rip_bbstart+delta); 
      /* (guest_rip_bbstart+delta) == return-to addr, d64 == call-to addr */
      t1 = newTemp(Ity_I64); 
      assign(t1, binop(Iop_Sub64, getIReg64(R_RSP), mkU64(8)));
      putIReg64(R_RSP, mkexpr(t1));
      storeLE( mkexpr(t1), mkU64(guest_rip_bbstart+delta));
      if (resteerOK && resteerOkFn((Addr64)d64)) {
         /* follow into the call target. */
         whatNext = Dis_Resteer;
         *whereNext = d64;
      } else {
         jmp_lit(Ijk_Call,d64);
         whatNext = Dis_StopHere;
      }
      DIP("call 0x%llx\n",d64);
      break;

//.. //--    case 0xC8: /* ENTER */ 
//.. //--       d32 = getUDisp16(eip); eip += 2;
//.. //--       abyte = getUChar(delta); delta++;
//.. //-- 
//.. //--       vg_assert(sz == 4);           
//.. //--       vg_assert(abyte == 0);
//.. //-- 
//.. //--       t1 = newTemp(cb); t2 = newTemp(cb);
//.. //--       uInstr2(cb, GET,   sz, ArchReg, R_EBP, TempReg, t1);
//.. //--       uInstr2(cb, GET,    4, ArchReg, R_ESP, TempReg, t2);
//.. //--       uInstr2(cb, SUB,    4, Literal, 0,     TempReg, t2);
//.. //--       uLiteral(cb, sz);
//.. //--       uInstr2(cb, PUT,    4, TempReg, t2,    ArchReg, R_ESP);
//.. //--       uInstr2(cb, STORE,  4, TempReg, t1,    TempReg, t2);
//.. //--       uInstr2(cb, PUT,    4, TempReg, t2,    ArchReg, R_EBP);
//.. //--       if (d32) {
//.. //--          uInstr2(cb, SUB,    4, Literal, 0,     TempReg, t2);
//.. //--          uLiteral(cb, d32);
//.. //--          uInstr2(cb, PUT,    4, TempReg, t2,    ArchReg, R_ESP);
//.. //--       }
//.. //--       DIP("enter 0x%x, 0x%x", d32, abyte);
//.. //--       break;

   case 0xC9: /* LEAVE */
      /* In 64-bit mode this defaults to a 64-bit operand size.  There
         is no way to encode a 32-bit variant.  Hence sz==4 but we do
         it as if sz=8. */
      if (sz != 4) 
         goto decode_failure;
      t1 = newTemp(Ity_I64); 
      t2 = newTemp(Ity_I64);
      assign(t1, getIReg64(R_RBP));
      /* First PUT RSP looks redundant, but need it because RSP must
         always be up-to-date for Memcheck to work... */
      putIReg64(R_RSP, mkexpr(t1));
      assign(t2, loadLE(Ity_I64,mkexpr(t1)));
      putIReg64(R_RBP, mkexpr(t2));
      putIReg64(R_RSP, binop(Iop_Add64, mkexpr(t1), mkU64(8)) );
      DIP("leave\n");
      break;

//.. //--    /* ---------------- Misc weird-ass insns --------------- */
//.. //-- 
//.. //--    case 0x27: /* DAA */
//.. //--    case 0x2F: /* DAS */
//.. //--       t1 = newTemp(cb);
//.. //--       uInstr2(cb, GET, 1, ArchReg, R_AL, TempReg, t1);
//.. //--       /* Widen %AL to 32 bits, so it's all defined when we push it. */
//.. //--       uInstr1(cb, WIDEN, 4, TempReg, t1);
//.. //--       uWiden(cb, 1, False);
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       uInstr1(cb, PUSH, 4, TempReg, t1);
//.. //--       uInstr1(cb, CALLM, 0, Lit16, 
//.. //--                   opc == 0x27 ? VGOFF_(helper_DAA) : VGOFF_(helper_DAS) );
//.. //--       uFlagsRWU(cb, FlagsAC, FlagsSZACP, FlagO);
//.. //--       uInstr1(cb, POP, 4, TempReg, t1);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       uInstr2(cb, PUT, 1, TempReg, t1, ArchReg, R_AL);
//.. //--       DIP(opc == 0x27 ? "daa\n" : "das\n");
//.. //--       break;
//.. //-- 
//.. //--    case 0x37: /* AAA */
//.. //--    case 0x3F: /* AAS */
//.. //--       t1 = newTemp(cb);
//.. //--       uInstr2(cb, GET, 2, ArchReg, R_EAX, TempReg, t1);
//.. //--       /* Widen %AL to 32 bits, so it's all defined when we push it. */
//.. //--       uInstr1(cb, WIDEN, 4, TempReg, t1);
//.. //--       uWiden(cb, 2, False);
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       uInstr1(cb, PUSH, 4, TempReg, t1);
//.. //--       uInstr1(cb, CALLM, 0, Lit16, 
//.. //--                   opc == 0x37 ? VGOFF_(helper_AAA) : VGOFF_(helper_AAS) );
//.. //--       uFlagsRWU(cb, FlagA, FlagsAC, FlagsEmpty);
//.. //--       uInstr1(cb, POP, 4, TempReg, t1);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       uInstr2(cb, PUT, 2, TempReg, t1, ArchReg, R_EAX);
//.. //--       DIP(opc == 0x37 ? "aaa\n" : "aas\n");
//.. //--       break;
//.. //-- 
//.. //--    case 0xD4: /* AAM */
//.. //--    case 0xD5: /* AAD */
//.. //--       d32 = getUChar(delta); delta++;
//.. //--       if (d32 != 10) VG_(core_panic)("disInstr: AAM/AAD but base not 10 !");
//.. //--       t1 = newTemp(cb);
//.. //--       uInstr2(cb, GET, 2, ArchReg, R_EAX, TempReg, t1);
//.. //--       /* Widen %AX to 32 bits, so it's all defined when we push it. */
//.. //--       uInstr1(cb, WIDEN, 4, TempReg, t1);
//.. //--       uWiden(cb, 2, False);
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       uInstr1(cb, PUSH, 4, TempReg, t1);
//.. //--       uInstr1(cb, CALLM, 0, Lit16, 
//.. //--                   opc == 0xD4 ? VGOFF_(helper_AAM) : VGOFF_(helper_AAD) );
//.. //--       uFlagsRWU(cb, FlagsEmpty, FlagsSZP, FlagsEmpty);
//.. //--       uInstr1(cb, POP, 4, TempReg, t1);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       uInstr2(cb, PUT, 2, TempReg, t1, ArchReg, R_EAX);
//.. //--       DIP(opc == 0xD4 ? "aam\n" : "aad\n");
//.. //--       break;

   /* ------------------------ CWD/CDQ -------------------- */

   case 0x98: /* CBW */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz == 8) {
         putIRegRAX( 8, unop(Iop_32Sto64, getIRegRAX(4)) );
         DIP(/*"cdqe\n"*/"cltq");
         break;
      }
      if (sz == 4) {
         putIRegRAX( 4, unop(Iop_16Sto32, getIRegRAX(2)) );
         DIP("cwtl\n");
         break;
      }
      if (sz == 2) {
         putIRegRAX( 2, unop(Iop_8Sto16, getIRegRAX(1)) );
         DIP("cbw\n");
         break;
      }
      goto decode_failure;

   case 0x99: /* CWD/CDQ/CQO */
      if (haveF2orF3(pfx)) goto decode_failure;
      vassert(sz == 2 || sz == 4 || sz == 8);
      ty = szToITy(sz);
      putIRegRDX( sz, 
                  binop(mkSizedOp(ty,Iop_Sar8), 
                        getIRegRAX(sz),
                        mkU8(sz == 2 ? 15 : (sz == 4 ? 31 : 63))) );
      DIP(sz == 2 ? "cwd\n" 
                  : (sz == 4 ? /*"cdq\n"*/ "cltd\n" 
                             : "cqo\n"));
      break;

   /* ------------------------ FPU ops -------------------- */

//..    case 0x9E: /* SAHF */
//..       codegen_SAHF();
//..       DIP("sahf\n");
//..       break;
//.. 
//.. //--    case 0x9F: /* LAHF */
//.. //--       codegen_LAHF ( cb );
//.. //--       DIP("lahf\n");
//.. //--       break;
//.. //-- 
//..    case 0x9B: /* FWAIT */
//..       /* ignore? */
//..       DIP("fwait\n");
//..       break;

   case 0xD8:
   case 0xD9:
   case 0xDA:
   case 0xDB:
   case 0xDC:
   case 0xDD:
   case 0xDE:
   case 0xDF:
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz == 4 && haveNo66noF2noF3(pfx)) {
         ULong delta0    = delta;
         Bool  decode_OK = False;
         delta = dis_FPU ( &decode_OK, pfx, delta );
         if (!decode_OK) {
            delta = delta0;
            goto decode_failure;
         }
         break;
      } else {
         goto decode_failure;
      }

//..    /* ------------------------ INC & DEC ------------------ */
//.. 
//..    case 0x40: /* INC eAX */
//..    case 0x41: /* INC eCX */
//..    case 0x42: /* INC eDX */
//..    case 0x43: /* INC eBX */
//..    case 0x44: /* INC eSP */
//..    case 0x45: /* INC eBP */
//..    case 0x46: /* INC eSI */
//..    case 0x47: /* INC eDI */
//..       vassert(sz == 2 || sz == 4);
//..       ty = szToITy(sz);
//..       t1 = newTemp(ty);
//..       assign( t1, binop(mkSizedOp(ty,Iop_Add8),
//..                         getIReg(sz, (UInt)(opc - 0x40)),
//..                         mkU(ty,1)) );
//..       setFlags_INC_DEC( True, t1, ty );
//..       putIReg(sz, (UInt)(opc - 0x40), mkexpr(t1));
//..       DIP("inc%c %s\n", nameISize(sz), nameIReg(sz,opc-0x40));
//..       break;
//.. 
//..    case 0x48: /* DEC eAX */
//..    case 0x49: /* DEC eCX */
//..    case 0x4A: /* DEC eDX */
//..    case 0x4B: /* DEC eBX */
//..    case 0x4C: /* DEC eSP */
//..    case 0x4D: /* DEC eBP */
//..    case 0x4E: /* DEC eSI */
//..    case 0x4F: /* DEC eDI */
//..       vassert(sz == 2 || sz == 4);
//..       ty = szToITy(sz);
//..       t1 = newTemp(ty);
//..       assign( t1, binop(mkSizedOp(ty,Iop_Sub8),
//..                         getIReg(sz, (UInt)(opc - 0x48)),
//..                         mkU(ty,1)) );
//..       setFlags_INC_DEC( False, t1, ty );
//..       putIReg(sz, (UInt)(opc - 0x48), mkexpr(t1));
//..       DIP("dec%c %s\n", nameISize(sz), nameIReg(sz,opc-0x48));
//..       break;

   /* ------------------------ Jcond, byte offset --------- */

   case 0xEB: /* Jb (jump, byte offset) */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz != 4) 
         goto decode_failure; /* JRS added 2004 July 11 */
      d64 = (guest_rip_bbstart+delta+1) + getSDisp8(delta); 
      delta++;
      if (resteerOK && resteerOkFn(d64)) {
         whatNext   = Dis_Resteer;
         *whereNext = d64;
      } else {
         jmp_lit(Ijk_Boring,d64);
         whatNext = Dis_StopHere;
      }
      DIP("jmp-8 0x%llx\n", d64);
      break;

   case 0xE9: /* Jv (jump, 16/32 offset) */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz != 4) 
         goto decode_failure; /* JRS added 2004 July 11 */
      d64 = (guest_rip_bbstart+delta+sz) + getSDisp(sz,delta); 
      delta += sz;
      if (resteerOK && resteerOkFn(d64)) {
         whatNext   = Dis_Resteer;
         *whereNext = d64;
      } else {
         jmp_lit(Ijk_Boring,d64);
         whatNext = Dis_StopHere;
      }
      DIP("jmp 0x%llx\n", d64);
      break;

   case 0x70:
   case 0x71:
   case 0x72: /* JBb/JNAEb (jump below) */
   case 0x73: /* JNBb/JAEb (jump not below) */
   case 0x74: /* JZb/JEb (jump zero) */
   case 0x75: /* JNZb/JNEb (jump not zero) */
   case 0x76: /* JBEb/JNAb (jump below or equal) */
   case 0x77: /* JNBEb/JAb (jump not below or equal) */
   case 0x78: /* JSb (jump negative) */
   case 0x79: /* JSb (jump not negative) */
   case 0x7A: /* JP (jump parity even) */
   case 0x7B: /* JNP/JPO (jump parity odd) */
   case 0x7C: /* JLb/JNGEb (jump less) */
   case 0x7D: /* JGEb/JNLb (jump greater or equal) */
   case 0x7E: /* JLEb/JNGb (jump less or equal) */
   case 0x7F: /* JGb/JNLEb (jump greater) */
      if (haveF2orF3(pfx)) goto decode_failure;
      d64 = (guest_rip_bbstart+delta+1) + getSDisp8(delta); 
      delta++;
      jcc_01( (AMD64Condcode)(opc - 0x70), 
              guest_rip_bbstart+delta,
              d64 );
      whatNext = Dis_StopHere;
      DIP("j%s-8 0x%llx\n", name_AMD64Condcode(opc - 0x70), d64);
      break;

//..    case 0xE3: /* JECXZ or perhaps JCXZ, depending on OSO ?  Intel
//..                  manual says it depends on address size override,
//..                  which doesn't sound right to me. */
//..       vassert(sz==4); /* possibly also OK for sz==2 */
//..       d32 = (((Addr32)guest_eip_bbstart)+delta+1) + getSDisp8(delta);
//..       delta++;
//..       ty = szToITy(sz);
//..       stmt( IRStmt_Exit(
//..                binop(mkSizedOp(ty,Iop_CmpEQ8),
//..                      getIReg(sz,R_ECX),
//..                      mkU(ty,0)),
//..             Ijk_Boring,
//..             IRConst_U32(d32)) 
//..           );
//.. 
//..       DIP("j%sz 0x%x\n", nameIReg(sz, R_ECX), d32);
//..       break;
//.. 
//.. //--    case 0xE0: /* LOOPNE disp8 */
//.. //--    case 0xE1: /* LOOPE  disp8 */
//.. //--    case 0xE2: /* LOOP   disp8 */
//.. //--       /* Again, the docs say this uses ECX/CX as a count depending on
//.. //--          the address size override, not the operand one.  Since we
//.. //--          don't handle address size overrides, I guess that means
//.. //--          ECX. */
//.. //--       d32 = (eip+1) + getSDisp8(eip); eip++;
//.. //--       t1 = newTemp(cb);
//.. //--       uInstr2(cb, GET,  4, ArchReg, R_ECX, TempReg, t1);
//.. //--       uInstr1(cb, DEC,  4, TempReg, t1);
//.. //--       uInstr2(cb, PUT,  4, TempReg, t1,    ArchReg, R_ECX);
//.. //--       uInstr2(cb, JIFZ, 4, TempReg, t1,    Literal, 0);
//.. //--       uLiteral(cb, eip);
//.. //--       if (opc == 0xE0 || opc == 0xE1) {   /* LOOPE/LOOPNE */
//.. //--          jcc_lit(cb, eip, (opc == 0xE1 ? CondNZ : CondZ));
//.. //--       }
//.. //--       jmp_lit(cb, d32);
//.. //--       whatNext = Dis_StopHere;
//.. //--       DIP("loop 0x%x\n", d32);
//.. //--       break;

   /* ------------------------ IMUL ----------------------- */

   case 0x69: /* IMUL Iv, Ev, Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_imul_I_E_G ( pfx, sz, delta, sz );
      break;
   case 0x6B: /* IMUL Ib, Ev, Gv */
      delta = dis_imul_I_E_G ( pfx, sz, delta, 1 );
      break;

   /* ------------------------ MOV ------------------------ */

   case 0x88: /* MOV Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_mov_G_E(pfx, 1, delta);
      break;

   case 0x89: /* MOV Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_mov_G_E(pfx, sz, delta);
      break;

   case 0x8A: /* MOV Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_mov_E_G(pfx, 1, delta);
      break;
 
   case 0x8B: /* MOV Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_mov_E_G(pfx, sz, delta);
      break;
 
   case 0x8D: /* LEA M,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz != 4 && sz != 8)
         goto decode_failure;
      modrm = getUChar(delta);
      if (epartIsReg(modrm)) 
         goto decode_failure;
      /* NOTE!  this is the one place where a segment override prefix
         has no effect on the address calculation.  Therefore we clear
         any segment override bits in pfx. */
      addr = disAMode ( &alen, clearSegBits(pfx), delta, dis_buf, 0 );
      delta += alen;
      /* This is a hack.  But it isn't clear that really doing the
         calculation at 32 bits is really worth it.  Hence for leal,
         do the full 64-bit calculation and then truncate it. */
      putIRegG( sz, pfx, modrm, 
                         sz == 4
                            ? unop(Iop_64to32, mkexpr(addr))
                            : mkexpr(addr)
              );
      DIP("lea%c %s, %s\n", nameISize(sz), dis_buf, 
                            nameIRegG(sz,pfx,modrm));
      break;

//..    case 0x8C: /* MOV Sw,Ew -- MOV from a SEGMENT REGISTER */
//..       delta = dis_mov_Sw_Ew(sorb, sz, delta);
//..       break;
//.. 
//..    case 0x8E: /* MOV Ew,Sw -- MOV to a SEGMENT REGISTER */
//..       delta = dis_mov_Ew_Sw(sorb, delta);
//..       break;
//..  
//..    case 0xA0: /* MOV Ob,AL */
//..       sz = 1;
//..       /* Fall through ... */
//..    case 0xA1: /* MOV Ov,eAX */
//..       d32 = getUDisp32(delta); delta += 4;
//..       ty = szToITy(sz);
//..       addr = newTemp(Ity_I32);
//..       assign( addr, handleSegOverride(sorb, mkU32(d32)) );
//..       putIReg(sz, R_EAX, loadLE(ty, mkexpr(addr)));
//..       DIP("mov%c %s0x%x, %s\n", nameISize(sz), sorbTxt(sorb),
//..                                 d32, nameIReg(sz,R_EAX));
//..       break;
//.. 
//..    case 0xA2: /* MOV Ob,AL */
//..       sz = 1;
//..       /* Fall through ... */
//..    case 0xA3: /* MOV eAX,Ov */
//..       d32 = getUDisp32(delta); delta += 4;
//..       ty = szToITy(sz);
//..       addr = newTemp(Ity_I32);
//..       assign( addr, handleSegOverride(sorb, mkU32(d32)) );
//..       storeLE( mkexpr(addr), getIReg(sz,R_EAX) );
//..       DIP("mov%c %s, %s0x%x\n", nameISize(sz), nameIReg(sz,R_EAX),
//..                                 sorbTxt(sorb), d32);
//..       break;

/* XXXX be careful here with moves to AH/BH/CH/DH */
   case 0xB0: /* MOV imm,AL */
   case 0xB1: /* MOV imm,CL */
   case 0xB2: /* MOV imm,DL */
   case 0xB3: /* MOV imm,BL */
   case 0xB4: /* MOV imm,AH */
   case 0xB5: /* MOV imm,CH */
   case 0xB6: /* MOV imm,DH */
   case 0xB7: /* MOV imm,BH */
      if (haveF2orF3(pfx)) goto decode_failure;
      d64 = getUChar(delta); 
      delta += 1;
      putIRegRexB(1, pfx, opc-0xB0, mkU8(d64));
      DIP("movb $%lld,%s\n", d64, nameIRegRexB(1,pfx,opc-0xB0));
      break;

   case 0xB8: /* MOV imm,eAX */
   case 0xB9: /* MOV imm,eCX */
   case 0xBA: /* MOV imm,eDX */
   case 0xBB: /* MOV imm,eBX */
   case 0xBC: /* MOV imm,eSP */
   case 0xBD: /* MOV imm,eBP */
   case 0xBE: /* MOV imm,eSI */
   case 0xBF: /* MOV imm,eDI */
      /* This is the one-and-only place where 64-bit literals are
         allowed in the instruction stream. */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz == 8) {
         d64 = getDisp64(delta);
         delta += 8;
         putIRegRexB(8, pfx, opc-0xB8, mkU64(d64));
         DIP("movabsq $%lld,%s\n", (Long)d64, 
                                   nameIRegRexB(8,pfx,opc-0xB8));
      } else {
         d64 = getSDisp(imin(4,sz),delta);
         delta += imin(4,sz);
         putIRegRexB(sz, pfx, opc-0xB8, 
                         mkU(szToITy(sz), d64 & mkSizeMask(sz)));
         DIP("mov%c $%lld,%s\n", nameISize(sz), 
                                 (Long)d64, 
                                 nameIRegRexB(sz,pfx,opc-0xB8));
      }
      break;

   case 0xC6: /* MOV Ib,Eb */
      sz = 1;
      goto do_Mov_I_E;
   case 0xC7: /* MOV Iv,Ev */
      goto do_Mov_I_E;

   do_Mov_I_E:
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      if (epartIsReg(modrm)) {
         delta++; /* mod/rm byte */
         d64 = getSDisp(imin(4,sz),delta); 
         delta += imin(4,sz);
         putIRegE(sz, pfx, modrm, 
                      mkU(szToITy(sz), d64 & mkSizeMask(sz)));
         DIP("mov%c $%lld, %s\n", nameISize(sz), 
                                  (Long)d64, 
                                  nameIRegE(sz,pfx,modrm));
      } else {
         addr = disAMode ( &alen, pfx, delta, dis_buf, 
                           /*xtra*/imin(4,sz) );
         delta += alen;
         d64 = getSDisp(imin(4,sz),delta);
         delta += imin(4,sz);
         storeLE(mkexpr(addr), 
                 mkU(szToITy(sz), d64 & mkSizeMask(sz)));
         DIP("mov%c $%lld, %s\n", nameISize(sz), (Long)d64, dis_buf);
      }
      break;

   /* ------------------------ MOVx ------------------------ */

   case 0x63: /* MOVSX */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (haveREX(pfx) && 1==getRexW(pfx)) {
         vassert(sz == 8);
         /* movsx r/m32 to r64 */
         modrm = getUChar(delta);
         if (epartIsReg(modrm)) {
            delta++;
            putIRegG(8, pfx, modrm, 
                             unop(Iop_32Sto64, 
                                  getIRegE(4, pfx, modrm)));
            DIP("movslq %s,%s\n",
                nameIRegE(4, pfx, modrm),
                nameIRegG(8, pfx, modrm));
            break;
         } else {
            addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
            delta += alen;
            putIRegG(8, pfx, modrm, 
                             unop(Iop_32Sto64, 
                                  loadLE(Ity_I32, mkexpr(addr))));
            DIP("movslq %s,%s\n", dis_buf, 
                nameIRegG(8, pfx, modrm));
            break;
         }
      } else {
         goto decode_failure;
      }

//..    /* ------------------------ opl imm, A ----------------- */
//.. 
//..    case 0x04: /* ADD Ib, AL */
//..       delta = dis_op_imm_A( 1, Iop_Add8, True, delta, "add" );
//..       break;
   case 0x05: /* ADD Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A(sz, Iop_Add8, True, delta, "add" );
      break;

   case 0x0C: /* OR Ib, AL */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( 1, Iop_Or8, True, delta, "or" );
      break;
   case 0x0D: /* OR Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( sz, Iop_Or8, True, delta, "or" );
      break;

//.. //--    case 0x14: /* ADC Ib, AL */
//.. //--       delta = dis_op_imm_A( 1, ADC, True, delta, "adc" );
//.. //--       break;
//.. //--    case 0x15: /* ADC Iv, eAX */
//.. //--       delta = dis_op_imm_A( sz, ADC, True, delta, "adc" );
//.. //--       break;
//.. //-- 
//.. //--    case 0x1C: /* SBB Ib, AL */
//.. //--       delta = dis_op_imm_A( 1, SBB, True, delta, "sbb" );
//.. //--       break;
//.. //--    case 0x1D: /* SBB Iv, eAX */
//.. //--       delta = dis_op_imm_A( sz, SBB, True, delta, "sbb" );
//.. //--       break;
//.. //-- 
   case 0x24: /* AND Ib, AL */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( 1, Iop_And8, True, delta, "and" );
      break;
   case 0x25: /* AND Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( sz, Iop_And8, True, delta, "and" );
      break;

   case 0x2C: /* SUB Ib, AL */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A(1, Iop_Sub8, True, delta, "sub" );
      break;
   case 0x2D: /* SUB Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( sz, Iop_Sub8, True, delta, "sub" );
      break;

//..    case 0x34: /* XOR Ib, AL */
//..       delta = dis_op_imm_A( 1, Iop_Xor8, True, delta, "xor" );
//..       break;
   case 0x35: /* XOR Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( sz, Iop_Xor8, True, delta, "xor" );
      break;

   case 0x3C: /* CMP Ib, AL */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( 1, Iop_Sub8, False, delta, "cmp" );
      break;
   case 0x3D: /* CMP Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( sz, Iop_Sub8, False, delta, "cmp" );
      break;

   case 0xA8: /* TEST Ib, AL */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( 1, Iop_And8, False, delta, "test" );
      break;
   case 0xA9: /* TEST Iv, eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op_imm_A( sz, Iop_And8, False, delta, "test" );
      break;

   /* ------------------------ opl Ev, Gv ----------------- */
 
   case 0x02: /* ADD Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Add8, True, 1, delta, "add" );
      break;
   case 0x03: /* ADD Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Add8, True, sz, delta, "add" );
      break;

   case 0x0A: /* OR Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Or8, True, 1, delta, "or" );
      break;
   case 0x0B: /* OR Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Or8, True, sz, delta, "or" );
      break;
//-- 
//.. //--    case 0x12: /* ADC Eb,Gb */
//.. //--       delta = dis_op2_E_G ( sorb, True, ADC, True, 1, delta, "adc" );
//.. //--       break;
//..    case 0x13: /* ADC Ev,Gv */
//..       delta = dis_op2_E_G ( sorb, True, Iop_Add8, True, sz, delta, "adc" );
//..       break;
//.. 
//.. //--    case 0x1A: /* SBB Eb,Gb */
//.. //--       delta = dis_op2_E_G ( sorb, True, SBB, True, 1, delta, "sbb" );
//.. //--       break;
//..    case 0x1B: /* SBB Ev,Gv */
//..       delta = dis_op2_E_G ( sorb, True, Iop_Sub8, True, sz, delta, "sbb" );
//..       break;

   case 0x22: /* AND Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_And8, True, 1, delta, "and" );
      break;
   case 0x23: /* AND Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_And8, True, sz, delta, "and" );
      break;

   case 0x2A: /* SUB Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Sub8, True, 1, delta, "sub" );
      break;
   case 0x2B: /* SUB Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Sub8, True, sz, delta, "sub" );
      break;

   case 0x32: /* XOR Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Xor8, True, 1, delta, "xor" );
      break;
   case 0x33: /* XOR Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Xor8, True, sz, delta, "xor" );
      break;

   case 0x3A: /* CMP Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Sub8, False, 1, delta, "cmp" );
      break;
   case 0x3B: /* CMP Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_Sub8, False, sz, delta, "cmp" );
      break;

   case 0x84: /* TEST Eb,Gb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_And8, False, 1, delta, "test" );
      break;
   case 0x85: /* TEST Ev,Gv */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_E_G ( pfx, False, Iop_And8, False, sz, delta, "test" );
      break;

   /* ------------------------ opl Gv, Ev ----------------- */

   case 0x00: /* ADD Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Add8, True, 1, delta, "add" );
      break;
   case 0x01: /* ADD Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Add8, True, sz, delta, "add" );
      break;

   case 0x08: /* OR Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Or8, True, 1, delta, "or" );
      break;
   case 0x09: /* OR Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Or8, True, sz, delta, "or" );
      break;

   case 0x10: /* ADC Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, True, Iop_Add8, True, 1, delta, "adc" );
      break;
   case 0x11: /* ADC Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, True, Iop_Add8, True, sz, delta, "adc" );
      break;

   case 0x18: /* SBB Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, True, Iop_Sub8, True, 1, delta, "sbb" );
      break;
   case 0x19: /* SBB Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, True, Iop_Sub8, True, sz, delta, "sbb" );
      break;

   case 0x20: /* AND Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_And8, True, 1, delta, "and" );
      break;
   case 0x21: /* AND Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_And8, True, sz, delta, "and" );
      break;

   case 0x28: /* SUB Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Sub8, True, 1, delta, "sub" );
      break;
   case 0x29: /* SUB Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Sub8, True, sz, delta, "sub" );
      break;

   case 0x30: /* XOR Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Xor8, True, 1, delta, "xor" );
      break;
   case 0x31: /* XOR Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Xor8, True, sz, delta, "xor" );
      break;

   case 0x38: /* CMP Gb,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Sub8, False, 1, delta, "cmp" );
      break;
   case 0x39: /* CMP Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_op2_G_E ( pfx, False, Iop_Sub8, False, sz, delta, "cmp" );
      break;

   /* ------------------------ POP ------------------------ */

   case 0x58: /* POP eAX */
   case 0x59: /* POP eCX */
   case 0x5A: /* POP eDX */
   case 0x5B: /* POP eBX */
   case 0x5D: /* POP eBP */
   case 0x5E: /* POP eSI */
   case 0x5F: /* POP eDI */
   case 0x5C: /* POP eSP */
      if (haveF2orF3(pfx)) goto decode_failure;
      vassert(sz == 2 || sz == 4 || sz == 8);
      if (sz == 4)
         sz = 8; /* there is no encoding for 32-bit pop in 64-bit mode */
      t1 = newTemp(szToITy(sz)); 
      t2 = newTemp(Ity_I64);
      assign(t2, getIReg64(R_RSP));
      assign(t1, loadLE(szToITy(sz),mkexpr(t2)));
      putIReg64(R_RSP, binop(Iop_Add64, mkexpr(t2), mkU64(sz)));
      putIRegRexB(sz, pfx, opc-0x58, mkexpr(t1));
      DIP("pop%c %s\n", nameISize(sz), nameIRegRexB(sz,pfx,opc-0x58));
      break;

   case 0x9D: /* POPF */
      /* Note.  There is no encoding for a 32-bit popf in 64-bit mode.
         So sz==4 actually means sz==8. */
      if (haveF2orF3(pfx)) goto decode_failure;
      vassert(sz == 2 || sz == 4);
      if (sz == 4) sz = 8;
      if (sz != 8) goto decode_failure; // until we know a sz==2 test case exists
      t1 = newTemp(Ity_I64); t2 = newTemp(Ity_I64);
      assign(t2, getIReg64(R_RSP));
      assign(t1, widenUto64(loadLE(szToITy(sz),mkexpr(t2))));
      putIReg64(R_RSP, binop(Iop_Add64, mkexpr(t2), mkU64(sz)));
      /* t1 is the flag word.  Mask out everything except OSZACP and 
         set the flags thunk to AMD64G_CC_OP_COPY. */
      stmt( IRStmt_Put( OFFB_CC_OP,   mkU64(AMD64G_CC_OP_COPY) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkU64(0) ));
      stmt( IRStmt_Put( OFFB_CC_DEP1, 
                        binop(Iop_And64,
                              mkexpr(t1), 
                              mkU64( AMD64G_CC_MASK_C | AMD64G_CC_MASK_P 
                                     | AMD64G_CC_MASK_A | AMD64G_CC_MASK_Z 
                                     | AMD64G_CC_MASK_S| AMD64G_CC_MASK_O )
                             )
                       )
          );

      /* Also need to set the D flag, which is held in bit 10 of t1.
         If zero, put 1 in OFFB_DFLAG, else -1 in OFFB_DFLAG. */
      stmt( IRStmt_Put( 
               OFFB_DFLAG,
               IRExpr_Mux0X( 
                  unop(Iop_32to8,
                  unop(Iop_64to32,
                       binop(Iop_And64, 
                             binop(Iop_Shr64, mkexpr(t1), mkU8(10)), 
                             mkU64(1)))),
                  mkU64(1), 
                  mkU64(0xFFFFFFFFFFFFFFFFULL))) 
          );

      /* And set the ID flag */
      stmt( IRStmt_Put( 
               OFFB_IDFLAG,
               IRExpr_Mux0X( 
                  unop(Iop_32to8,
                  unop(Iop_64to32,
                       binop(Iop_And64, 
                             binop(Iop_Shr64, mkexpr(t1), mkU8(21)), 
                             mkU64(1)))),
                  mkU64(0), 
                  mkU64(1))) 
          );

      DIP("popf%c\n", nameISize(sz));
      break;

//..    case 0x61: /* POPA */
//..       /* This is almost certainly wrong for sz==2.  So ... */
//..       if (sz != 4) goto decode_failure;
//.. 
//..       /* t5 is the old %ESP value. */
//..       t5 = newTemp(Ity_I32);
//..       assign( t5, getIReg(4, R_ESP) );
//.. 
//..       /* Reload all the registers, except %esp. */
//..       putIReg(4,R_EAX, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32(28)) ));
//..       putIReg(4,R_ECX, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32(24)) ));
//..       putIReg(4,R_EDX, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32(20)) ));
//..       putIReg(4,R_EBX, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32(16)) ));
//..       /* ignore saved %ESP */
//..       putIReg(4,R_EBP, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32( 8)) ));
//..       putIReg(4,R_ESI, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32( 4)) ));
//..       putIReg(4,R_EDI, loadLE(Ity_I32, binop(Iop_Add32,mkexpr(t5),mkU32( 0)) ));
//.. 
//..       /* and move %ESP back up */
//..       putIReg( 4, R_ESP, binop(Iop_Add32, mkexpr(t5), mkU32(8*4)) );
//.. 
//..       DIP("pusha%c\n", nameISize(sz));
//..       break;
//.. 
//..    case 0x8F: /* POPL/POPW m32 */
//..      { Int len;
//..        UChar rm = getUChar(delta);
//.. 
//..        /* make sure this instruction is correct POP */
//..        vassert(!epartIsReg(rm) && (gregOfRM(rm) == 0));
//..        /* and has correct size */
//..        vassert(sz == 4);      
//..        
//..        t1 = newTemp(Ity_I32); t3 = newTemp(Ity_I32);
//..        /* set t1 to ESP: t1 = ESP */
//..        assign( t1, getIReg(4, R_ESP) );
//..        /* load M[ESP] to virtual register t3: t3 = M[t1] */
//..        assign( t3, loadLE(Ity_I32, mkexpr(t1)) );
//..        
//..        /* increase ESP; must be done before the STORE.  Intel manual says:
//..             If the ESP register is used as a base register for addressing
//..             a destination operand in memory, the POP instruction computes
//..             the effective address of the operand after it increments the
//..             ESP register.
//..        */
//..        putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(t1), mkU32(sz)) );
//.. 
//..        /* resolve MODR/M */
//..        addr = disAMode ( &len, sorb, delta, dis_buf);
//..        storeLE( mkexpr(addr), mkexpr(t3) );
//.. 
//..        DIP("popl %s\n", dis_buf);
//.. 
//..        delta += len;
//..        break;
//..      }
//.. 
//.. //--    case 0x1F: /* POP %DS */
//.. //--       dis_pop_segreg( cb, R_DS, sz ); break;
//.. //--    case 0x07: /* POP %ES */
//.. //--       dis_pop_segreg( cb, R_ES, sz ); break;
//.. //--    case 0x17: /* POP %SS */
//.. //--       dis_pop_segreg( cb, R_SS, sz ); break;

   /* ------------------------ PUSH ----------------------- */

   case 0x50: /* PUSH eAX */
   case 0x51: /* PUSH eCX */
   case 0x52: /* PUSH eDX */
   case 0x53: /* PUSH eBX */
   case 0x55: /* PUSH eBP */
   case 0x56: /* PUSH eSI */
   case 0x57: /* PUSH eDI */
   case 0x54: /* PUSH eSP */
      /* This is the Right Way, in that the value to be pushed is
         established before %rsp is changed, so that pushq %rsp
         correctly pushes the old value. */
      if (haveF2orF3(pfx)) goto decode_failure;
      vassert(sz == 2 || sz == 4 || sz == 8);
      if (sz == 4)
         sz = 8; /* there is no encoding for 32-bit push in 64-bit mode */
      ty = sz==2 ? Ity_I16 : Ity_I64;
      t1 = newTemp(ty); 
      t2 = newTemp(Ity_I64);
      assign(t1, getIRegRexB(sz, pfx, opc-0x50));
      assign(t2, binop(Iop_Sub64, getIReg64(R_RSP), mkU64(sz)));
      putIReg64(R_RSP, mkexpr(t2) );
      storeLE(mkexpr(t2),mkexpr(t1));
      DIP("push%c %s\n", nameISize(sz), nameIRegRexB(sz,pfx,opc-0x50));
      break;

   case 0x68: /* PUSH Iv */
      if (haveF2orF3(pfx)) goto decode_failure;
      /* Note, sz==4 is not possible in 64-bit mode.  Hence ... */
      if (sz == 4) sz = 8;
      d64 = getSDisp(imin(4,sz),delta); 
      delta += imin(4,sz);
      goto do_push_I;
   case 0x6A: /* PUSH Ib, sign-extended to sz */
      if (haveF2orF3(pfx)) goto decode_failure;
      /* Note, sz==4 is not possible in 64-bit mode.  Hence ... */
      if (sz == 4) sz = 8;
      d64 = getSDisp8(delta); delta += 1;
      goto do_push_I;
   do_push_I:
      ty = szToITy(sz);
      t1 = newTemp(Ity_I64);
      t2 = newTemp(ty);
      assign( t1, binop(Iop_Sub64,getIReg64(R_RSP),mkU64(sz)) );
      putIReg64(R_RSP, mkexpr(t1) );
      storeLE( mkexpr(t1), mkU(ty,d64) );
      DIP("push%c $%lld\n", nameISize(sz), (Long)d64);
      break;

   case 0x9C: /* PUSHF */ {
      /* Note.  There is no encoding for a 32-bit pushf in 64-bit
         mode.  So sz==4 actually means sz==8. */
      if (haveF2orF3(pfx)) goto decode_failure;
      vassert(sz == 2 || sz == 4);
      if (sz == 4) sz = 8;
      if (sz != 8) goto decode_failure; // until we know a sz==2 test case exists

      t1 = newTemp(Ity_I64);
      assign( t1, binop(Iop_Sub64,getIReg64(R_RSP),mkU64(sz)) );
      putIReg64(R_RSP, mkexpr(t1) );

      t2 = newTemp(Ity_I64);
      assign( t2, mk_amd64g_calculate_rflags_all() );

      /* Patch in the D flag.  This can simply be a copy of bit 10 of
         baseBlock[OFFB_DFLAG]. */
      t3 = newTemp(Ity_I64);
      assign( t3, binop(Iop_Or64,
                        mkexpr(t2),
                        binop(Iop_And64,
                              IRExpr_Get(OFFB_DFLAG,Ity_I64),
                              mkU64(1<<10))) 
            );

      /* And patch in the ID flag. */
      t4 = newTemp(Ity_I64);
      assign( t4, binop(Iop_Or64,
                        mkexpr(t3),
                        binop(Iop_And64,
                              binop(Iop_Shl64, IRExpr_Get(OFFB_IDFLAG,Ity_I64), 
                                               mkU8(21)),
                              mkU64(1<<21)))
            );

      /* if sz==2, the stored value needs to be narrowed. */
      if (sz == 2)
        storeLE( mkexpr(t1), unop(Iop_32to16,
                             unop(Iop_64to32,mkexpr(t4))) );
      else 
        storeLE( mkexpr(t1), mkexpr(t4) );

      DIP("pushf%c\n", nameISize(sz));
      break;
   }

//..    case 0x60: /* PUSHA */
//..       /* This is almost certainly wrong for sz==2.  So ... */
//..       if (sz != 4) goto decode_failure;
//.. 
//..       /* This is the Right Way, in that the value to be pushed is
//..          established before %esp is changed, so that pusha
//..          correctly pushes the old %esp value.  New value of %esp is
//..          pushed at start. */
//..       /* t0 is the %ESP value we're going to push. */
//..       t0 = newTemp(Ity_I32);
//..       assign( t0, getIReg(4, R_ESP) );
//.. 
//..       /* t5 will be the new %ESP value. */
//..       t5 = newTemp(Ity_I32);
//..       assign( t5, binop(Iop_Sub32, mkexpr(t0), mkU32(8*4)) );
//.. 
//..       /* Update guest state before prodding memory. */
//..       putIReg(4, R_ESP, mkexpr(t5));
//.. 
//..       /* Dump all the registers. */
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32(28)), getIReg(4,R_EAX) );
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32(24)), getIReg(4,R_ECX) );
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32(20)), getIReg(4,R_EDX) );
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32(16)), getIReg(4,R_EBX) );
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32(12)), mkexpr(t0) /*esp*/);
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32( 8)), getIReg(4,R_EBP) );
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32( 4)), getIReg(4,R_ESI) );
//..       storeLE( binop(Iop_Add32,mkexpr(t5),mkU32( 0)), getIReg(4,R_EDI) );
//.. 
//..       DIP("pusha%c\n", nameISize(sz));
//..       break;
//.. 
//.. 
//.. //--    case 0x0E: /* PUSH %CS */
//.. //--       dis_push_segreg( cb, R_CS, sz ); break;
//.. //--    case 0x1E: /* PUSH %DS */
//.. //--       dis_push_segreg( cb, R_DS, sz ); break;
//.. //--    case 0x06: /* PUSH %ES */
//.. //--       dis_push_segreg( cb, R_ES, sz ); break;
//.. //--    case 0x16: /* PUSH %SS */
//.. //--       dis_push_segreg( cb, R_SS, sz ); break;
//.. 
//..    /* ------------------------ SCAS et al ----------------- */
//.. 
//..    case 0xA4: /* MOVS, no REP prefix */
//..    case 0xA5: 
//..       dis_string_op( dis_MOVS, ( opc == 0xA4 ? 1 : sz ), "movs", sorb );
//..       break;
//.. 
//..   case 0xA6: /* CMPSb, no REP prefix */
//.. //--    case 0xA7:
//..      dis_string_op( dis_CMPS, ( opc == 0xA6 ? 1 : sz ), "cmps", sorb );
//..      break;
//.. //-- 
//.. //--    
//.. //--    case 0xAC: /* LODS, no REP prefix */
//.. //--    case 0xAD:
//.. //--       dis_string_op( cb, dis_LODS, ( opc == 0xAC ? 1 : sz ), "lods", sorb );
//.. //--       break;
//.. 
//..    case 0xAE: /* SCAS, no REP prefix */
//..    case 0xAF:
//..       dis_string_op( dis_SCAS, ( opc == 0xAE ? 1 : sz ), "scas", sorb );
//..       break;


   case 0xFC: /* CLD */
      if (haveF2orF3(pfx)) goto decode_failure;
      stmt( IRStmt_Put( OFFB_DFLAG, mkU64(1)) );
      DIP("cld\n");
      break;

   case 0xFD: /* STD */
      if (haveF2orF3(pfx)) goto decode_failure;
      stmt( IRStmt_Put( OFFB_DFLAG, mkU64(-1ULL)) );
      DIP("std\n");
      break;

//.. //--    case 0xF8: /* CLC */
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       uInstr1(cb, CALLM, 0, Lit16, VGOFF_(helper_CLC));
//.. //--       uFlagsRWU(cb, FlagsEmpty, FlagC, FlagsOSZAP);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       DIP("clc\n");
//.. //--       break;
//.. //-- 
//.. //--    case 0xF9: /* STC */
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       uInstr1(cb, CALLM, 0, Lit16, VGOFF_(helper_STC));
//.. //--       uFlagsRWU(cb, FlagsEmpty, FlagC, FlagsOSZAP);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       DIP("stc\n");
//.. //--       break;
//.. //-- 
//.. //--    case 0xF5: /* CMC */
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       uInstr1(cb, CALLM, 0, Lit16, VGOFF_(helper_CMC));
//.. //--       uFlagsRWU(cb, FlagC, FlagC, FlagsOSZAP);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       DIP("cmc\n");
//.. //--       break;
//.. 
//..    /* REPNE prefix insn */
//..    case 0xF2: { 
//..       Addr32 eip_orig = guest_eip_bbstart + delta - 1;
//..       vassert(sorb == 0);
//..       abyte = getUChar(delta); delta++;
//.. 
//..       if (abyte == 0x66) { sz = 2; abyte = getUChar(delta); delta++; }
//..       whatNext = Dis_StopHere;         
//.. 
//..       switch (abyte) {
//..       /* According to the Intel manual, "repne movs" should never occur, but
//..        * in practice it has happened, so allow for it here... */
//..       case 0xA4: sz = 1;   /* REPNE MOVS<sz> */
//..         goto decode_failure;
//.. //--       case 0xA5: 
//..         //         dis_REP_op ( CondNZ, dis_MOVS, sz, eip_orig,
//..         //                              guest_eip_bbstart+delta, "repne movs" );
//..         //         break;
//.. //-- 
//.. //--       case 0xA6: sz = 1;   /* REPNE CMPS<sz> */
//.. //--       case 0xA7:
//.. //--          dis_REP_op ( cb, CondNZ, dis_CMPS, sz, eip_orig, eip, "repne cmps" );
//.. //--          break;
//.. //-- 
//..       case 0xAE: sz = 1;   /* REPNE SCAS<sz> */
//..       case 0xAF:
//..          dis_REP_op ( X86CondNZ, dis_SCAS, sz, eip_orig,
//..                                  guest_eip_bbstart+delta, "repne scas" );
//..          break;
//.. 
//..       default:
//..          goto decode_failure;
//..       }
//..       break;
//..    }

   /* ------ AE: SCAS variants ------ */
   case 0xAE:
   case 0xAF:
      /* F2 AE/AF: repne scasb/repne scas{w,l,q} */
      if (haveF2(pfx) && !haveF3(pfx)) {
         if (opc == 0xAE)
            sz = 1;
         dis_REP_op ( AMD64CondNZ, dis_SCAS, sz, 
                      guest_rip_curr_instr,
                      guest_rip_bbstart+delta, "repne scas", pfx );
         whatNext = Dis_StopHere;
         break;
      }
      /* AE/AF: scasb/scas{w,l,q} */
      if (!haveF2(pfx) && !haveF3(pfx)) {
         if (opc == 0xAE)
            sz = 1;
         dis_string_op( dis_SCAS, sz, "scas", pfx );
         break;
      }
      goto decode_failure;

   /* ------ A6, A7: CMPS variants ------ */
   case 0xA6:
   case 0xA7:
      /* F3 A6/A7: repe cmps/rep cmps{w,l,q} */
      if (haveF3(pfx) && !haveF2(pfx)) {
         if (opc == 0xA6)
            sz = 1;
         dis_REP_op ( AMD64CondZ, dis_CMPS, sz, 
                      guest_rip_curr_instr,
                      guest_rip_bbstart+delta, "repe cmps", pfx );
         whatNext = Dis_StopHere;
         break;
      }
      goto decode_failure;

   /* ------ AA, AB: STOS variants ------ */
   case 0xAA:
   case 0xAB:
      /* F3 AA/AB: rep stosb/rep stos{w,l,q} */
      if (haveF3(pfx) && !haveF2(pfx)) {
         if (opc == 0xAA)
            sz = 1;
         dis_REP_op ( AMD64CondAlways, dis_STOS, sz,
                      guest_rip_curr_instr,
                      guest_rip_bbstart+delta, "rep stos", pfx );
        whatNext = Dis_StopHere;
        break;
      }
      /* AA/AB: stosb/stos{w,l,q} */
      if (!haveF3(pfx) && !haveF2(pfx)) {
         if (opc == 0xAA)
            sz = 1;
         dis_string_op( dis_STOS, sz, "stos", pfx );
         break;
      }
      goto decode_failure;

   /* ------ A4, A5: MOVS variants ------ */
   case 0xA4:
   case 0xA5:
      /* F3 A4: rep movsb */
      if (haveF3(pfx) && !haveF2(pfx)) {
         if (opc == 0xA4)
            sz = 1;
         dis_REP_op ( AMD64CondAlways, dis_MOVS, sz,
                      guest_rip_curr_instr,
                      guest_rip_bbstart+delta, "rep movs", pfx );
        whatNext = Dis_StopHere;
        break;
      }
      /* A4: movsb */
      if (!haveF3(pfx) && !haveF2(pfx)) {
         if (opc == 0xA4)
            sz = 1;
         dis_string_op( dis_MOVS, sz, "movs", pfx );
         break;
      }
      goto decode_failure;

//..    case 0xA5: 
//..       dis_string_op( dis_MOVS, ( opc == 0xA4 ? 1 : sz ), "movs", sorb );
//..       break;

//..    case 0xA4: /* MOVS, no REP prefix */
//..    case 0xA5: 
//..       dis_string_op( dis_MOVS, ( opc == 0xA4 ? 1 : sz ), "movs", sorb );
//..       break;

//..   case 0xF3: { 
//..       Addr32 eip_orig = guest_eip_bbstart + delta - 1;
//..       vassert(sorb == 0);
//..       abyte = getUChar(delta); delta++;
//.. 
//..       if (abyte == 0x66) { sz = 2; abyte = getUChar(delta); delta++; }
//..       whatNext = Dis_StopHere;
//.. 
//..       switch (abyte) {
//..       case 0xA4: sz = 1;   /* REP MOVS<sz> */
//..       case 0xA5:
//..          dis_REP_op ( X86CondAlways, dis_MOVS, sz, eip_orig, 
//..                                      guest_eip_bbstart+delta, "rep movs" );
//..          break;
//.. 
//..       case 0xA6: sz = 1;   /* REPE CMP<sz> */
//..       case 0xA7:
//..          dis_REP_op ( X86CondZ, dis_CMPS, sz, eip_orig, 
//..                                 guest_eip_bbstart+delta, "repe cmps" );
//..          break;
//.. 
//..       case 0xAA: sz = 1;   /* REP STOS<sz> */
//..       case 0xAB:
//..          dis_REP_op ( X86CondAlways, dis_STOS, sz, eip_orig, 
//..                                      guest_eip_bbstart+delta, "rep stos" );
//..          break;
//.. //-- 
//.. //--       case 0xAE: sz = 1;   /* REPE SCAS<sz> */
//.. //--       case 0xAF: 
//.. //--          dis_REP_op ( cb, CondZ, dis_SCAS, sz, eip_orig, eip, "repe scas" );
//.. //--          break;
//..       
//..       case 0x90:           /* REP NOP (PAUSE) */
//..          /* a hint to the P4 re spin-wait loop */
//..          DIP("rep nop (P4 pause)\n");
//..          jmp_lit(Ijk_Yield, ((Addr32)guest_eip_bbstart)+delta);
//..          whatNext = Dis_StopHere;
//..          break;
//.. 
//.. //--       case 0xC3:           /* REP RET */
//.. //--          /* AMD K7/K8-specific optimisation; faster than vanilla RET */
//.. //--          dis_ret(cb, 0);
//.. //--          DIP("rep ret\n");
//.. //--          break;
//.. 
//..       default:
//..          goto decode_failure;
//..       }
//..       break;
//..    }

   /* ------------------------ XCHG ----------------------- */

//..    case 0x86: /* XCHG Gb,Eb */
//..       sz = 1;
//..       /* Fall through ... */
   case 0x87: /* XCHG Gv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      ty = szToITy(sz);
      t1 = newTemp(ty); t2 = newTemp(ty);
      if (epartIsReg(modrm)) {
         assign(t1, getIRegE(sz, pfx, modrm));
         assign(t2, getIRegG(sz, pfx, modrm));
         putIRegG(sz, pfx, modrm, mkexpr(t1));
         putIRegE(sz, pfx, modrm, mkexpr(t2));
         delta++;
         DIP("xchg%c %s, %s\n", 
             nameISize(sz), nameIRegG(sz, pfx, modrm), 
                            nameIRegE(sz, pfx, modrm));
      } else {
         addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
         assign( t1, loadLE(ty, mkexpr(addr)) );
         assign( t2, getIRegG(sz, pfx, modrm) );
         storeLE( mkexpr(addr), mkexpr(t2) );
         putIRegG( sz, pfx, modrm, mkexpr(t1) );
         delta += alen;
         DIP("xchg%c %s, %s\n", nameISize(sz), 
                                nameIRegG(sz, pfx, modrm), dis_buf);
      }
      break;

   case 0x90: /* XCHG eAX,eAX */
      if (haveF2orF3(pfx)) goto decode_failure;
      DIP("nop\n");
      break;
   case 0x91: /* XCHG rAX,rCX */
   case 0x92: /* XCHG rAX,rDX */
   case 0x93: /* XCHG rAX,rBX */
   case 0x94: /* XCHG rAX,rSP */
   case 0x95: /* XCHG rAX,rBP */
   case 0x96: /* XCHG rAX,rSI */
   case 0x97: /* XCHG rAX,rDI */
      if (haveF2orF3(pfx)) goto decode_failure;
      if (sz != 8) goto decode_failure; /* temp hack */
      codegen_xchg_rAX_Reg ( pfx, sz, opc - 0x90 );
      break;

//.. //--    /* ------------------------ XLAT ----------------------- */
//.. //-- 
//.. //--    case 0xD7: /* XLAT */
//.. //--       t1 = newTemp(cb); t2 = newTemp(cb);
//.. //--       uInstr2(cb, GET, sz, ArchReg, R_EBX, TempReg, t1); /* get eBX */
//.. //--       handleSegOverride( cb, sorb, t1 );               /* make t1 DS:eBX */
//.. //--       uInstr2(cb, GET, 1, ArchReg, R_AL, TempReg, t2); /* get AL */
//.. //--       /* Widen %AL to 32 bits, so it's all defined when we add it. */
//.. //--       uInstr1(cb, WIDEN, 4, TempReg, t2);
//.. //--       uWiden(cb, 1, False);
//.. //--       uInstr2(cb, ADD, sz, TempReg, t2, TempReg, t1);  /* add AL to eBX */
//.. //--       uInstr2(cb, LOAD, 1, TempReg, t1,  TempReg, t2); /* get byte at t1 into t2 */
//.. //--       uInstr2(cb, PUT, 1, TempReg, t2, ArchReg, R_AL); /* put byte into AL */
//.. //-- 
//.. //--       DIP("xlat%c [ebx]\n", nameISize(sz));
//.. //--       break;
//.. //-- 
//.. //--    /* ------------------------ IN / OUT ----------------------- */
//.. //-- 
//.. //--    case 0xE4: /* IN ib, %al        */
//.. //--    case 0xE5: /* IN ib, %{e}ax     */
//.. //--    case 0xEC: /* IN (%dx),%al      */
//.. //--    case 0xED: /* IN (%dx),%{e}ax   */
//.. //--       t1 = newTemp(cb);
//.. //--       t2 = newTemp(cb);
//.. //--       t3 = newTemp(cb);
//.. //-- 
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       /* operand size? */
//.. //--       uInstr2(cb, MOV,   4, Literal, 0, TempReg, t1);
//.. //--       uLiteral(cb, ( opc == 0xE4 || opc == 0xEC ) ? 1 : sz);
//.. //--       uInstr1(cb, PUSH,  4, TempReg, t1);
//.. //--       /* port number ? */
//.. //--       if ( opc == 0xE4 || opc == 0xE5 ) {
//.. //--          abyte = getUChar(eip); eip++;
//.. //--          uInstr2(cb, MOV,   4, Literal, 0, TempReg, t2);
//.. //--          uLiteral(cb, abyte);
//.. //--       }
//.. //--       else
//.. //--          uInstr2(cb, GET,   4, ArchReg, R_EDX, TempReg, t2);
//.. //-- 
//.. //--       uInstr1(cb, PUSH,  4, TempReg, t2);
//.. //--       uInstr1(cb, CALLM, 0, Lit16,   VGOFF_(helper_IN));
//.. //--       uFlagsRWU(cb, FlagsEmpty, FlagsEmpty, FlagsEmpty);
//.. //--       uInstr1(cb, POP,   4, TempReg, t2);
//.. //--       uInstr1(cb, CLEAR, 0, Lit16,   4);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       uInstr2(cb, PUT,   4, TempReg, t2, ArchReg, R_EAX);
//.. //--       if ( opc == 0xE4 || opc == 0xE5 ) {
//.. //--          DIP("in 0x%x, %%eax/%%ax/%%al\n", getUChar(eip-1) );
//.. //--       } else {
//.. //--          DIP("in (%%dx), %%eax/%%ax/%%al\n");
//.. //--       }
//.. //--       break;
//.. //--    case 0xE6: /* OUT %al,ib       */
//.. //--    case 0xE7: /* OUT %{e}ax,ib    */
//.. //--    case 0xEE: /* OUT %al,(%dx)    */
//.. //--    case 0xEF: /* OUT %{e}ax,(%dx) */
//.. //--       t1 = newTemp(cb);
//.. //--       t2 = newTemp(cb);
//.. //--       t3 = newTemp(cb);
//.. //-- 
//.. //--       uInstr0(cb, CALLM_S, 0);
//.. //--       /* operand size? */
//.. //--       uInstr2(cb, MOV,   4, Literal, 0, TempReg, t1);
//.. //--       uLiteral(cb, ( opc == 0xE6 || opc == 0xEE ) ? 1 : sz);
//.. //--       uInstr1(cb, PUSH,  4, TempReg, t1);
//.. //--       /* port number ? */
//.. //--       if ( opc == 0xE6 || opc == 0xE7 ) {
//.. //--          abyte = getUChar(eip); eip++;
//.. //--          uInstr2(cb, MOV,   4, Literal, 0, TempReg, t2);
//.. //--          uLiteral(cb, abyte);
//.. //--       }
//.. //--       else
//.. //--          uInstr2(cb, GET,   4, ArchReg, R_EDX, TempReg, t2);
//.. //--       uInstr1(cb, PUSH,  4, TempReg, t2);
//.. //--       uInstr2(cb, GET,   4, ArchReg, R_EAX, TempReg, t3);
//.. //--       uInstr1(cb, PUSH,  4, TempReg, t3);
//.. //--       uInstr1(cb, CALLM, 0, Lit16,   VGOFF_(helper_OUT));
//.. //--       uFlagsRWU(cb, FlagsEmpty, FlagsEmpty, FlagsEmpty);
//.. //--       uInstr1(cb, CLEAR,  0, Lit16,  12);
//.. //--       uInstr0(cb, CALLM_E, 0);
//.. //--       if ( opc == 0xE4 || opc == 0xE5 ) {
//.. //--          DIP("out %%eax/%%ax/%%al, 0x%x\n", getUChar(eip-1) );
//.. //--       } else {
//.. //--          DIP("out %%eax/%%ax/%%al, (%%dx)\n");
//.. //--       }
//.. //--       break;

   /* ------------------------ (Grp1 extensions) ---------- */

   case 0x80: /* Grp1 Ib,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      sz    = 1;
      d_sz  = 1;
      d64   = getSDisp8(delta + am_sz);
      delta = dis_Grp1 ( pfx, delta, modrm, am_sz, d_sz, sz, d64 );
      break;

   case 0x81: /* Grp1 Iv,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = imin(sz,4);
      d64   = getSDisp(d_sz, delta + am_sz);
      delta = dis_Grp1 ( pfx, delta, modrm, am_sz, d_sz, sz, d64 );
      break;

   case 0x83: /* Grp1 Ib,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 1;
      d64   = getSDisp8(delta + am_sz);
      delta = dis_Grp1 ( pfx, delta, modrm, am_sz, d_sz, sz, d64 );
      break;

   /* ------------------------ (Grp2 extensions) ---------- */

   case 0xC0: /* Grp2 Ib,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 1;
      d64   = getUChar(delta + am_sz);
      sz    = 1;
      delta = dis_Grp2 ( pfx, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d64 & 0xFF), NULL );
      break;

   case 0xC1: /* Grp2 Ib,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 1;
      d64   = getUChar(delta + am_sz);
      delta = dis_Grp2 ( pfx, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d64 & 0xFF), NULL );
      break;

   case 0xD0: /* Grp2 1,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 0;
      d64   = 1;
      sz    = 1;
      delta = dis_Grp2 ( pfx, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d64), NULL );
      break;

   case 0xD1: /* Grp2 1,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 0;
      d64   = 1;
      delta = dis_Grp2 ( pfx, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d64), NULL );
      break;

   case 0xD2: /* Grp2 CL,Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 0;
      sz    = 1;
      delta = dis_Grp2 ( pfx, delta, modrm, am_sz, d_sz, sz, 
                         getIRegCL(), "%cl" );
      break;

   case 0xD3: /* Grp2 CL,Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      modrm = getUChar(delta);
      am_sz = lengthAMode(pfx,delta);
      d_sz  = 0;
      delta = dis_Grp2 ( pfx, delta, modrm, am_sz, d_sz, sz, 
                         getIRegCL(), "%cl" );
      break;

   /* ------------------------ (Grp3 extensions) ---------- */

   case 0xF6: /* Grp3 Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_Grp3 ( pfx, 1, delta );
      break;
   case 0xF7: /* Grp3 Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_Grp3 ( pfx, sz, delta );
      break;

   /* ------------------------ (Grp4 extensions) ---------- */

   case 0xFE: /* Grp4 Eb */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_Grp4 ( pfx, delta );
      break;

   /* ------------------------ (Grp5 extensions) ---------- */

   case 0xFF: /* Grp5 Ev */
      if (haveF2orF3(pfx)) goto decode_failure;
      delta = dis_Grp5 ( pfx, sz, delta, &whatNext );
      break;

   /* ------------------------ Escapes to 2-byte opcodes -- */

   case 0x0F: {
      opc = getUChar(delta); delta++;
      switch (opc) {

      /* =-=-=-=-=-=-=-=-=- Grp8 =-=-=-=-=-=-=-=-=-=-=-= */

      case 0xBA: { /* Grp8 Ib,Ev */
         Bool decode_OK = False;
         if (haveF2orF3(pfx)) goto decode_failure;
         modrm = getUChar(delta);
         am_sz = lengthAMode(pfx,delta);
         d64   = getSDisp8(delta + am_sz);
         delta = dis_Grp8_Imm ( pfx, delta, modrm, am_sz, sz, d64,
                                &decode_OK );
         if (!decode_OK)
            goto decode_failure;
         break;
      }

      /* =-=-=-=-=-=-=-=-=- BSF/BSR -=-=-=-=-=-=-=-=-=-= */

      case 0xBC: /* BSF Gv,Ev */
         if (haveF2orF3(pfx)) goto decode_failure;
         delta = dis_bs_E_G ( pfx, sz, delta, True );
         break;
      case 0xBD: /* BSR Gv,Ev */
         if (haveF2orF3(pfx)) goto decode_failure;
         delta = dis_bs_E_G ( pfx, sz, delta, False );
         break;

      /* =-=-=-=-=-=-=-=-=- BSWAP -=-=-=-=-=-=-=-=-=-=-= */

      case 0xC8: /* BSWAP %eax */
      case 0xC9:
      case 0xCA:
      case 0xCB:
      case 0xCC:
      case 0xCD:
      case 0xCE:
      case 0xCF: /* BSWAP %edi */
         if (haveF2orF3(pfx)) goto decode_failure;
         /* According to the AMD64 docs, this insn can have size 4 or
            8. */
         if (sz == 4) {
            t1 = newTemp(Ity_I32);
            t2 = newTemp(Ity_I32);
            assign( t1, getIRegRexB(4, pfx, opc-0xC8) );
            assign( t2,
               binop(Iop_Or32,
                  binop(Iop_Shl32, mkexpr(t1), mkU8(24)),
               binop(Iop_Or32,
                  binop(Iop_And32, binop(Iop_Shl32, mkexpr(t1), mkU8(8)), 
                                   mkU32(0x00FF0000)),
               binop(Iop_Or32,
                  binop(Iop_And32, binop(Iop_Shr32, mkexpr(t1), mkU8(8)),
                                   mkU32(0x0000FF00)),
                  binop(Iop_And32, binop(Iop_Shr32, mkexpr(t1), mkU8(24)),
                                   mkU32(0x000000FF) )
               )))
            );
            putIRegRexB(4, pfx, opc-0xC8, mkexpr(t2));
            DIP("bswapl %s\n", nameIRegRexB(4, pfx, opc-0xC8));
            break;
         } else {
            goto decode_failure;
         }

//..       /* =-=-=-=-=-=-=-=-=- BT/BTS/BTR/BTC =-=-=-=-=-=-= */
//.. 
//..       case 0xA3: /* BT Gv,Ev */
//..          delta = dis_bt_G_E ( sorb, sz, delta, BtOpNone );
//..          break;
//..       case 0xB3: /* BTR Gv,Ev */
//..          delta = dis_bt_G_E ( sorb, sz, delta, BtOpReset );
//..          break;
//..       case 0xAB: /* BTS Gv,Ev */
//..          delta = dis_bt_G_E ( sorb, sz, delta, BtOpSet );
//..          break;
//..       case 0xBB: /* BTC Gv,Ev */
//..          delta = dis_bt_G_E ( sorb, sz, delta, BtOpComp );
//..          break;

      /* =-=-=-=-=-=-=-=-=- CMOV =-=-=-=-=-=-=-=-=-=-=-= */
 
      case 0x40:
      case 0x41:
      case 0x42: /* CMOVBb/CMOVNAEb (cmov below) */
      case 0x43: /* CMOVNBb/CMOVAEb (cmov not below) */
      case 0x44: /* CMOVZb/CMOVEb (cmov zero) */
      case 0x45: /* CMOVNZb/CMOVNEb (cmov not zero) */
      case 0x46: /* CMOVBEb/CMOVNAb (cmov below or equal) */
      case 0x47: /* CMOVNBEb/CMOVAb (cmov not below or equal) */
      case 0x48: /* CMOVSb (cmov negative) */
      case 0x49: /* CMOVSb (cmov not negative) */
      case 0x4A: /* CMOVP (cmov parity even) */
      case 0x4B: /* CMOVNP (cmov parity odd) */
      case 0x4C: /* CMOVLb/CMOVNGEb (cmov less) */
      case 0x4D: /* CMOVGEb/CMOVNLb (cmov greater or equal) */
      case 0x4E: /* CMOVLEb/CMOVNGb (cmov less or equal) */
      case 0x4F: /* CMOVGb/CMOVNLEb (cmov greater) */
         if (haveF2orF3(pfx)) goto decode_failure;
         delta = dis_cmov_E_G(pfx, sz, (AMD64Condcode)(opc - 0x40), delta);
         break;

      /* =-=-=-=-=-=-=-=-=- CMPXCHG -=-=-=-=-=-=-=-=-=-= */

//..       case 0xB0: /* CMPXCHG Gb,Eb */
//..          delta = dis_cmpxchg_G_E ( sorb, 1, delta );
//..          break;
      case 0xB1: /* CMPXCHG Gv,Ev */
         if (haveF2orF3(pfx)) goto decode_failure;
         delta = dis_cmpxchg_G_E ( pfx, sz, delta );
         break;
//.. //--       case 0xC7: /* CMPXCHG8B Gv */
//.. //--          eip = dis_cmpxchg8b ( cb, sorb, eip );
//.. //--          break;
//.. //-- 
      /* =-=-=-=-=-=-=-=-=- CPUID -=-=-=-=-=-=-=-=-=-=-= */

      case 0xA2: { /* CPUID */
         /* Uses dirty helper: 
               void amd64g_dirtyhelper_CPUID ( VexGuestAMD64State* )
            declared to mod rax, wr rbx, rcx, rdx
         */
         IRDirty* d     = NULL;
         HChar*   fName = NULL;
         void*    fAddr = NULL;
         if (haveF2orF3(pfx)) goto decode_failure;
         switch (subarch) {
            case VexSubArch_NONE:
               fName = "amd64g_dirtyhelper_CPUID";
               fAddr = &amd64g_dirtyhelper_CPUID; 
               break;
            default:
               vpanic("disInstr(amd64)(cpuid)");
         }
         vassert(fName); vassert(fAddr);
         d = unsafeIRDirty_0_N ( 0/*regparms*/, 
                                 fName, fAddr, mkIRExprVec_0() );
         /* declare guest state effects */
         d->needsBBP = True;
         d->nFxState = 4;
         d->fxState[0].fx     = Ifx_Modify;
         d->fxState[0].offset = OFFB_RAX;
         d->fxState[0].size   = 8;
         d->fxState[1].fx     = Ifx_Write;
         d->fxState[1].offset = OFFB_RBX;
         d->fxState[1].size   = 8;
         d->fxState[2].fx     = Ifx_Write;
         d->fxState[2].offset = OFFB_RCX;
         d->fxState[2].size   = 8;
         d->fxState[3].fx     = Ifx_Write;
         d->fxState[3].offset = OFFB_RDX;
         d->fxState[3].size   = 8;
         /* execute the dirty call, side-effecting guest state */
         stmt( IRStmt_Dirty(d) );
         /* CPUID is a serialising insn.  So, just in case someone is
            using it as a memory fence ... */
         stmt( IRStmt_MFence() );
         DIP("cpuid\n");
         break;
      }

      /* =-=-=-=-=-=-=-=-=- MOVZX, MOVSX =-=-=-=-=-=-=-= */

      case 0xB6: /* MOVZXb Eb,Gv */
         if (haveF2orF3(pfx)) goto decode_failure;
         if (sz != 2 && sz != 4 && sz != 8)
            goto decode_failure;
         delta = dis_movx_E_G ( pfx, delta, 1, sz, False );
         break;
      case 0xB7: /* MOVZXw Ew,Gv */
         if (haveF2orF3(pfx)) goto decode_failure;
         if (sz != 4 && sz != 8)
            goto decode_failure;
         delta = dis_movx_E_G ( pfx, delta, 2, sz, False );
         break;

      case 0xBE: /* MOVSXb Eb,Gv */
         if (haveF2orF3(pfx)) goto decode_failure;
         if (sz != 2 && sz != 4 && sz != 8)
            goto decode_failure;
         delta = dis_movx_E_G ( pfx, delta, 1, sz, True );
         break;
      case 0xBF: /* MOVSXw Ew,Gv */
         if (haveF2orF3(pfx)) goto decode_failure;
         if (sz != 4 && sz != 8)
            goto decode_failure;
         delta = dis_movx_E_G ( pfx, delta, 2, sz, True );
         break;

//.. //--       /* =-=-=-=-=-=-=-=-=-=-= MOVNTI -=-=-=-=-=-=-=-=-= */
//.. //-- 
//.. //--       case 0xC3: /* MOVNTI Gv,Ev */
//.. //--          vg_assert(sz == 4);
//.. //--          modrm = getUChar(eip);
//.. //--          vg_assert(!epartIsReg(modrm));
//.. //--          t1 = newTemp(cb);
//.. //--          uInstr2(cb, GET, 4, ArchReg, gregOfRM(modrm), TempReg, t1);
//.. //--          pair = disAMode ( cb, sorb, eip, dis_buf );
//.. //--          t2 = LOW24(pair);
//.. //--          eip += HI8(pair);
//.. //--          uInstr2(cb, STORE, 4, TempReg, t1, TempReg, t2);
//.. //--          DIP("movnti %s,%s\n", nameIReg(4,gregOfRM(modrm)), dis_buf);
//.. //--          break;

      /* =-=-=-=-=-=-=-=-=- MUL/IMUL =-=-=-=-=-=-=-=-=-= */

      case 0xAF: /* IMUL Ev, Gv */
         if (haveF2orF3(pfx)) goto decode_failure;
         delta = dis_mul_E_G ( pfx, sz, delta );
         break;

      /* =-=-=-=-=-=-=-=-=- Jcond d32 -=-=-=-=-=-=-=-=-= */
      case 0x80:
      case 0x81:
      case 0x82: /* JBb/JNAEb (jump below) */
      case 0x83: /* JNBb/JAEb (jump not below) */
      case 0x84: /* JZb/JEb (jump zero) */
      case 0x85: /* JNZb/JNEb (jump not zero) */
      case 0x86: /* JBEb/JNAb (jump below or equal) */
      case 0x87: /* JNBEb/JAb (jump not below or equal) */
      case 0x88: /* JSb (jump negative) */
      case 0x89: /* JSb (jump not negative) */
      case 0x8A: /* JP (jump parity even) */
      case 0x8B: /* JNP/JPO (jump parity odd) */
      case 0x8C: /* JLb/JNGEb (jump less) */
      case 0x8D: /* JGEb/JNLb (jump greater or equal) */
      case 0x8E: /* JLEb/JNGb (jump less or equal) */
      case 0x8F: /* JGb/JNLEb (jump greater) */
         if (haveF2orF3(pfx)) goto decode_failure;
         d64 = (guest_rip_bbstart+delta+4) + getSDisp32(delta); 
         delta += 4;
         jcc_01( (AMD64Condcode)(opc - 0x80), 
                 guest_rip_bbstart+delta, 
                 d64 );
         whatNext = Dis_StopHere;
         DIP("j%s-32 0x%llx\n", name_AMD64Condcode(opc - 0x80), d64);
         break;

      /* =-=-=-=-=-=-=-=-=- RDTSC -=-=-=-=-=-=-=-=-=-=-= */

      case 0x31: /* RDTSC */
         if (haveF2orF3(pfx)) goto decode_failure;
         if (0) vex_printf("vex amd64->IR: kludged rdtsc\n");
         putIRegRAX(4, mkU32(1));
         putIRegRDX(4, mkU32(0));

//.. //--          t1 = newTemp(cb);
//.. //--          t2 = newTemp(cb);
//.. //--          t3 = newTemp(cb);
//.. //--          uInstr0(cb, CALLM_S, 0);
//.. //--          // Nb: even though these args aren't used by RDTSC_helper, need
//.. //--          // them to be defined (for Memcheck).  The TempRegs pushed must
//.. //--          // also be distinct.
//.. //--          uInstr2(cb, MOV,   4, Literal, 0, TempReg, t1);
//.. //--          uLiteral(cb, 0);
//.. //--          uInstr1(cb, PUSH,  4, TempReg, t1);
//.. //--          uInstr2(cb, MOV,   4, Literal, 0, TempReg, t2);
//.. //--          uLiteral(cb, 0);
//.. //--          uInstr1(cb, PUSH,  4, TempReg, t2);
//.. //--          uInstr1(cb, CALLM, 0, Lit16,   VGOFF_(helper_RDTSC));
//.. //--          uFlagsRWU(cb, FlagsEmpty, FlagsEmpty, FlagsEmpty);
//.. //--          uInstr1(cb, POP,   4, TempReg, t3);
//.. //--          uInstr2(cb, PUT,   4, TempReg, t3, ArchReg, R_EDX);
//.. //--          uInstr1(cb, POP,   4, TempReg, t3);
//.. //--          uInstr2(cb, PUT,   4, TempReg, t3, ArchReg, R_EAX);
//.. //--          uInstr0(cb, CALLM_E, 0);
         DIP("rdtsc\n");
         break;

//..       /* =-=-=-=-=-=-=-=-=- PUSH/POP Sreg =-=-=-=-=-=-=-=-=-= */
//.. 
//..       case 0xA1: /* POP %FS */
//..          dis_pop_segreg( R_FS, sz ); break;
//..       case 0xA9: /* POP %GS */
//..          dis_pop_segreg( R_GS, sz ); break;
//.. 
//..       case 0xA0: /* PUSH %FS */
//..          dis_push_segreg( R_FS, sz ); break;
//..       case 0xA8: /* PUSH %GS */
//..          dis_push_segreg( R_GS, sz ); break;

      /* =-=-=-=-=-=-=-=-=- SETcc Eb =-=-=-=-=-=-=-=-=-= */
      case 0x90:
      case 0x91:
      case 0x92: /* set-Bb/set-NAEb (set if below) */
      case 0x93: /* set-NBb/set-AEb (set if not below) */
      case 0x94: /* set-Zb/set-Eb (set if zero) */
      case 0x95: /* set-NZb/set-NEb (set if not zero) */
      case 0x96: /* set-BEb/set-NAb (set if below or equal) */
      case 0x97: /* set-NBEb/set-Ab (set if not below or equal) */
      case 0x98: /* set-Sb (set if negative) */
      case 0x99: /* set-Sb (set if not negative) */
      case 0x9A: /* set-P (set if parity even) */
      case 0x9B: /* set-NP (set if parity odd) */
      case 0x9C: /* set-Lb/set-NGEb (set if less) */
      case 0x9D: /* set-GEb/set-NLb (set if greater or equal) */
      case 0x9E: /* set-LEb/set-NGb (set if less or equal) */
      case 0x9F: /* set-Gb/set-NLEb (set if greater) */
         if (haveF2orF3(pfx)) goto decode_failure;
         t1 = newTemp(Ity_I8);
         assign( t1, unop(Iop_1Uto8,mk_amd64g_calculate_condition(opc-0x90)) );
         modrm = getUChar(delta);
         if (epartIsReg(modrm)) {
            delta++;
            putIRegE(1, pfx, modrm, mkexpr(t1));
            DIP("set%s %s\n", name_AMD64Condcode(opc-0x90), 
                              nameIRegE(1,pfx,modrm));
         } else {
            addr = disAMode ( &alen, pfx, delta, dis_buf, 0 );
            delta += alen;
            storeLE( mkexpr(addr), mkexpr(t1) );
            DIP("set%s %s\n", name_AMD64Condcode(opc-0x90), dis_buf);
         }
         break;

//..       /* =-=-=-=-=-=-=-=-=- SHLD/SHRD -=-=-=-=-=-=-=-=-= */
//.. 
//..       case 0xA4: /* SHLDv imm8,Gv,Ev */
//..          modrm = getUChar(delta);
//..          d32   = delta + lengthAMode(delta);
//..          vex_sprintf(dis_buf, "$%d", delta);
//..          delta = dis_SHLRD_Gv_Ev ( 
//..                   sorb, delta, modrm, sz, 
//..                   mkU8(getUChar(d32)), True, /* literal */
//..                   dis_buf, True );
//..          break;
//..       case 0xA5: /* SHLDv %cl,Gv,Ev */
//..          modrm = getUChar(delta);
//..          delta = dis_SHLRD_Gv_Ev ( 
//..                     sorb, delta, modrm, sz,
//..                     getIReg(1,R_ECX), False, /* not literal */
//..                     "%cl", True );
//..          break;
//.. 
//..       case 0xAC: /* SHRDv imm8,Gv,Ev */
//..          modrm = getUChar(delta);
//..          d32   = delta + lengthAMode(delta);
//..          vex_sprintf(dis_buf, "$%d", delta);
//..          delta = dis_SHLRD_Gv_Ev ( 
//..                     sorb, delta, modrm, sz, 
//..                     mkU8(getUChar(d32)), True, /* literal */
//..                     dis_buf, False );
//..          break;
//..       case 0xAD: /* SHRDv %cl,Gv,Ev */
//..          modrm = getUChar(delta);
//..          delta = dis_SHLRD_Gv_Ev ( 
//..                     sorb, delta, modrm, sz, 
//..                     getIReg(1,R_ECX), False, /* not literal */
//..                     "%cl", False );
//..          break;

      /* =-=-=-=-=-=-=-=-=- SYSCALL -=-=-=-=-=-=-=-=-=-= */
      case 0x05: /* SYSCALL */
         guest_rip_next_mustcheck = True;
         guest_rip_next_assumed = guest_rip_bbstart + delta;
         putIReg64( R_RCX, mkU64(guest_rip_next_assumed) );
         /* It's important that all guest state is up-to-date
            at this point.  So we declare an end-of-block here, which
            forces any cached guest state to be flushed. */
        jmp_lit(Ijk_Syscall, guest_rip_next_assumed);
        whatNext = Dis_StopHere;
        DIP("syscall\n");
        break;

      /* =-=-=-=-=-=-=-=-=- XADD -=-=-=-=-=-=-=-=-=-= */

//.. //--       case 0xC0: /* XADD Gb,Eb */
//.. //--          eip = dis_xadd_G_E ( cb, sorb, 1, eip );
//.. //--          break;
      case 0xC1: { /* XADD Gv,Ev */ 
         Bool decode_OK = False;
         delta = dis_xadd_G_E ( &decode_OK, pfx, sz, delta );
         if (!decode_OK)
            goto decode_failure;
         break;
      }

//..       /* =-=-=-=-=-=-=-=-=- MMXery =-=-=-=-=-=-=-=-=-=-= */
//.. 
//..       case 0x71: 
//..       case 0x72: 
//..       case 0x73: /* PSLLgg/PSRAgg/PSRLgg mmxreg by imm8 */
//.. 
//..       case 0x6E: /* MOVD (src)ireg-or-mem, (dst)mmxreg */
//..       case 0x7E: /* MOVD (src)mmxreg, (dst)ireg-or-mem */
//..       case 0x7F: /* MOVQ (src)mmxreg, (dst)mmxreg-or-mem */
//..       case 0x6F: /* MOVQ (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xFC: 
//..       case 0xFD: 
//..       case 0xFE: /* PADDgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xEC: 
//..       case 0xED: /* PADDSgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xDC:
//..       case 0xDD: /* PADDUSgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xF8: 
//..       case 0xF9: 
//..       case 0xFA: /* PSUBgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xE8: 
//..       case 0xE9: /* PSUBSgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xD8: 
//..       case 0xD9: /* PSUBUSgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xE5: /* PMULHW (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xD5: /* PMULLW (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xF5: /* PMADDWD (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0x74: 
//..       case 0x75: 
//..       case 0x76: /* PCMPEQgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0x64: 
//..       case 0x65: 
//..       case 0x66: /* PCMPGTgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0x6B: /* PACKSSDW (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0x63: /* PACKSSWB (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0x67: /* PACKUSWB (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0x68: 
//..       case 0x69: 
//..       case 0x6A: /* PUNPCKHgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0x60: 
//..       case 0x61: 
//..       case 0x62: /* PUNPCKLgg (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xDB: /* PAND (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xDF: /* PANDN (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xEB: /* POR (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xEF: /* PXOR (src)mmxreg-or-mem, (dst)mmxreg */
//.. 
//..       case 0xF1: /* PSLLgg (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xF2: 
//..       case 0xF3: 
//.. 
//..       case 0xD1: /* PSRLgg (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xD2: 
//..       case 0xD3: 
//.. 
//..       case 0xE1: /* PSRAgg (src)mmxreg-or-mem, (dst)mmxreg */
//..       case 0xE2: 
//..       {
//..          ULong delta0    = delta-1;
//..          Bool decode_OK = False;
//.. 
//..          /* If sz==2 this is SSE, and we assume sse idec has
//..             already spotted those cases by now. */
//..          if (sz != 4)
//..             goto decode_failure;
//.. 
//..          delta = dis_MMX ( &decode_OK, sorb, sz, delta-1 );
//..          if (!decode_OK) {
//..             delta = delta0;
//..             goto decode_failure;
//..          }
//..          break;
//..       }
//.. 
//..       case 0x77: /* EMMS */
//..          if (sz != 4)
//..             goto decode_failure;
//..          do_EMMS_preamble();
//..          DIP("emms\n");
//..          break;

      /* =-=-=-=-=-=-=-=-=- unimp2 =-=-=-=-=-=-=-=-=-=-= */

      default:
         goto decode_failure;
   } /* switch (opc) for the 2-byte opcodes */
   goto decode_success;
   } /* case 0x0F: of primary opcode */

   /* ------------------------ ??? ------------------------ */
  
  default:
  decode_failure:
   /* All decode failures end up here. */
   vex_printf("vex amd64->IR: unhandled instruction bytes: "
              "0x%x 0x%x 0x%x 0x%x\n",
              (Int)getUChar(delta_start+0),
              (Int)getUChar(delta_start+1),
              (Int)getUChar(delta_start+2),
              (Int)getUChar(delta_start+3) );

   /* Tell the dispatcher that this insn cannot be decoded, and so has
      not been executed, and (is currently) the next to be executed.
      RIP should be up-to-date since it made so at the start of each
      insn, but nevertheless be paranoid and update it again right
      now. */
   stmt( IRStmt_Put( OFFB_RIP, mkU64(guest_rip_curr_instr) ) );
   jmp_lit(Ijk_NoDecode, guest_rip_curr_instr);
   whatNext = Dis_StopHere;
   *size = 0;
   return whatNext;

   } /* switch (opc) for the main (primary) opcode switch. */

  decode_success:
   /* All decode successes end up here. */
   DIP("\n");
   *size = delta - delta_start;
   return whatNext;
}

#undef DIP
#undef DIS

/*--------------------------------------------------------------------*/
/*--- end                                       guest-amd64/toIR.c ---*/
/*--------------------------------------------------------------------*/
