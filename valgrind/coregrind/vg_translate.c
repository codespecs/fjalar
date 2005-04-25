
/*--------------------------------------------------------------------*/
/*--- The JITter proper: register allocation & code improvement    ---*/
/*---                                               vg_translate.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Julian Seward 
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

#include "core.h"
#include "pub_core_aspacemgr.h"


/*------------------------------------------------------------*/
/*--- %SP-update pass                                      ---*/
/*------------------------------------------------------------*/

/* NOTE: this comment is out of date */

/* For tools that want to know about %ESP changes, this pass adds
   in the appropriate hooks.  We have to do it after the tool's
   instrumentation, so the tool doesn't have to worry about the CCALLs
   it adds in, and we must do it before register allocation because
   spilled temps make it much harder to work out the %esp deltas.
   Thus we have it as an extra phase between the two. 
   
   We look for "GETL %ESP, t_ESP", then track ADDs and SUBs of
   literal values to t_ESP, and the total delta of the ADDs/SUBs.  Then if
   "PUTL t_ESP, %ESP" happens, we call the helper with the known delta.  We
   also cope with "MOVL t_ESP, tX", making tX the new t_ESP.  If any other
   instruction clobbers t_ESP, we don't track it anymore, and fall back to
   the delta-is-unknown case.  That case is also used when the delta is not
   a nice small amount, or an unknown amount.
*/

static
IRBB* vg_SP_update_pass ( IRBB* bb_in, VexGuestLayout* layout, 
                          IRType gWordTy, IRType hWordTy )
{
   Int      i, j, minoff_ST, maxoff_ST, sizeof_SP, offset_SP;
   IRDirty  *dcall, *d;
   IRStmt*  st;
   IRExpr*  e;
   IRArray* descr;
   IRTemp   curr;
   IRType   typeof_SP;
   Long     delta;

   /* Set up BB */
   IRBB* bb     = emptyIRBB();
   bb->tyenv    = dopyIRTypeEnv(bb_in->tyenv);
   bb->next     = dopyIRExpr(bb_in->next);
   bb->jumpkind = bb_in->jumpkind;

   curr  = IRTemp_INVALID;
   delta = 0;

   sizeof_SP = layout->sizeof_SP;
   offset_SP = layout->offset_SP;
   typeof_SP = sizeof_SP==4 ? Ity_I32 : Ity_I64;
   vg_assert(sizeof_SP == 4 || sizeof_SP == 8);

#  define IS_ADD(op) (sizeof_SP==4 ? ((op)==Iop_Add32) : ((op)==Iop_Add64))
#  define IS_SUB(op) (sizeof_SP==4 ? ((op)==Iop_Sub32) : ((op)==Iop_Sub64))

#  define IS_ADD_OR_SUB(op) (IS_ADD(op) || IS_SUB(op))

#  define GET_CONST(con)                                                \
       (sizeof_SP==4 ? (Long)(Int)(con->Ico.U32)                        \
                     : (Long)(con->Ico.U64))

#  define DO(kind, syze)                                                \
      do {                                                              \
         if (!VG_(defined_##kind##_mem_stack_##syze)())                 \
            goto generic;                                               \
                                                                        \
         /* I don't know if it's really necessary to say that the */    \
         /* call reads the stack pointer.  But anyway, we do. */        \
         dcall = unsafeIRDirty_0_N(                                     \
                    1/*regparms*/,                                      \
                    "track_" #kind "_mem_stack_" #syze,                 \
                    VG_(tdict).track_##kind##_mem_stack_##syze,         \
                    mkIRExprVec_1(IRExpr_Tmp(curr))                     \
                 );                                                     \
         dcall->nFxState = 1;                                           \
         dcall->fxState[0].fx     = Ifx_Read;                           \
         dcall->fxState[0].offset = layout->offset_SP;                  \
         dcall->fxState[0].size   = layout->sizeof_SP;                  \
                                                                        \
         addStmtToIRBB( bb, IRStmt_Dirty(dcall) );                      \
      } while (0)

   for (i = 0; i <  bb_in->stmts_used; i++) {

      st = bb_in->stmts[i];
      if (!st)
         continue;

      /* t = Get(sp):   curr = t, delta = 0 */
      if (st->tag != Ist_Tmp) goto case2;
      e = st->Ist.Tmp.data;
      if (e->tag != Iex_Get)              goto case2;
      if (e->Iex.Get.offset != offset_SP) goto case2;
      if (e->Iex.Get.ty != typeof_SP)     goto case2;
      curr = st->Ist.Tmp.tmp;
      delta = 0;
      addStmtToIRBB( bb, st );
      continue;

     case2:
      /* t' = curr +/- const:   curr = t',  delta +=/-= const */
      if (st->tag != Ist_Tmp) goto case3;
      e = st->Ist.Tmp.data;
      if (e->tag != Iex_Binop) goto case3;
      if (e->Iex.Binop.arg1->tag != Iex_Tmp) goto case3;
      if (e->Iex.Binop.arg1->Iex.Tmp.tmp != curr) goto case3;
      if (e->Iex.Binop.arg2->tag != Iex_Const) goto case3;
      if (!IS_ADD_OR_SUB(e->Iex.Binop.op)) goto case3;
      curr = st->Ist.Tmp.tmp;
      if (IS_ADD(e->Iex.Binop.op))
         delta += GET_CONST(e->Iex.Binop.arg2->Iex.Const.con);
      else
         delta -= GET_CONST(e->Iex.Binop.arg2->Iex.Const.con);
      addStmtToIRBB( bb, st );
      continue;

     case3:
      /* t' = curr:   curr = t' */
      if (st->tag != Ist_Tmp) goto case4;
      e = st->Ist.Tmp.data;
      if (e->tag != Iex_Tmp) goto case4;
      if (e->Iex.Tmp.tmp != curr) goto case4;
      curr = st->Ist.Tmp.tmp;
      addStmtToIRBB( bb, st );
      continue;

     case4:
      /* Put(sp) = curr */
      if (st->tag != Ist_Put) goto case5;
      if (st->Ist.Put.offset != offset_SP) goto case5;
      if (st->Ist.Put.data->tag != Iex_Tmp) goto case5;
      if (st->Ist.Put.data->Iex.Tmp.tmp == curr) {
         switch (delta) {
            case   0:              addStmtToIRBB(bb,st); delta = 0; continue;
            case   4: DO(die, 4);  addStmtToIRBB(bb,st); delta = 0; continue;
            case  -4: DO(new, 4);  addStmtToIRBB(bb,st); delta = 0; continue;
            case   8: DO(die, 8);  addStmtToIRBB(bb,st); delta = 0; continue;
            case  -8: DO(new, 8);  addStmtToIRBB(bb,st); delta = 0; continue;
            case  12: DO(die, 12); addStmtToIRBB(bb,st); delta = 0; continue;
            case -12: DO(new, 12); addStmtToIRBB(bb,st); delta = 0; continue;
            case  16: DO(die, 16); addStmtToIRBB(bb,st); delta = 0; continue;
            case -16: DO(new, 16); addStmtToIRBB(bb,st); delta = 0; continue;
            case  32: DO(die, 32); addStmtToIRBB(bb,st); delta = 0; continue;
            case -32: DO(new, 32); addStmtToIRBB(bb,st); delta = 0; continue;
            default:  goto generic;
         }
      } else {
         IRTemp old_SP;
        generic:
         /* Pass both the old and new SP values to this helper. */
         old_SP = newIRTemp(bb->tyenv, typeof_SP);
         addStmtToIRBB( 
            bb,
            IRStmt_Tmp( old_SP, IRExpr_Get(offset_SP, typeof_SP) ) 
         );

         dcall = unsafeIRDirty_0_N( 
                    2/*regparms*/, 
                    "VG_(unknown_SP_update)", &VG_(unknown_SP_update),
                    mkIRExprVec_2( IRExpr_Tmp(old_SP), st->Ist.Put.data ) 
                 );
         addStmtToIRBB( bb, IRStmt_Dirty(dcall) );

         addStmtToIRBB( bb, st );

         curr = st->Ist.Put.data->Iex.Tmp.tmp;
         delta = 0;
         continue;
      }

     case5:
      /* PutI or Dirty call which overlaps SP: complain.  We can't
         deal with SP changing in weird ways (well, we can, but not at
         this time of night).  */
      if (st->tag == Ist_PutI) {
         descr = st->Ist.PutI.descr;
         minoff_ST = descr->base;
         maxoff_ST = descr->base + descr->nElems * sizeofIRType(descr->elemTy) - 1;
         if (!(offset_SP > maxoff_ST || (offset_SP + sizeof_SP - 1) < minoff_ST))
            goto complain;
      }
      if (st->tag == Ist_Dirty) {
         d = st->Ist.Dirty.details;
         for (j = 0; j < d->nFxState; j++) {
            minoff_ST = d->fxState[j].offset;
            maxoff_ST = d->fxState[j].offset + d->fxState[j].size - 1;
            if (d->fxState[j].fx == Ifx_Read || d->fxState[j].fx == Ifx_None)
               continue;
            if (!(offset_SP > maxoff_ST || (offset_SP + sizeof_SP - 1) < minoff_ST))
               goto complain;
         }
      }

      /* well, not interesting.  Just copy and keep going. */
      addStmtToIRBB( bb, st );

   } /* for (i = 0; i <  bb_in->stmts_used; i++) */

   return bb;

  complain:
   VG_(core_panic)("vg_SP_update_pass: PutI or Dirty which overlaps SP");

}



#if 0
   for (i = 0; i <  bb_in->stmts_used; i++) {
      st = bb_in->stmts[i];
      if (!st)
         continue;
      if (st->tag != Ist_Put) 
         goto boring;
      offP = st->Ist.Put.offset;
      if (offP != layout->offset_SP) 
         goto boring;
      szP = sizeofIRType(typeOfIRExpr(bb_in->tyenv, st->Ist.Put.data));
      if (szP != layout->sizeof_SP)
         goto boring;
      vg_assert(isAtom(st->Ist.Put.data));

      /* I don't know if it's really necessary to say that the call reads
         the stack pointer.  But anyway, we do. */      
      dcall = unsafeIRDirty_0_N( 
                 mkIRCallee(1, "VG_(unknown_esp_update)", 
                            (HWord)&VG_(unknown_esp_update)),
                 mkIRExprVec_1(st->Ist.Put.data) 
              );
      dcall->nFxState = 1;
      dcall->fxState[0].fx     = Ifx_Read;
      dcall->fxState[0].offset = layout->offset_SP;
      dcall->fxState[0].size   = layout->sizeof_SP;

      addStmtToIRBB( bb, IRStmt_Dirty(dcall) );

     boring:
      addStmtToIRBB( bb, st );
   }
#endif


/*------------------------------------------------------------*/
/*--- Main entry point for the JITter.                     ---*/
/*------------------------------------------------------------*/

/* Vex dumps the final code in here.  Then we can copy it off
   wherever we like. */
#define N_TMPBUF 20000
static UChar tmpbuf[N_TMPBUF];

/* Function pointers we must supply to LibVEX in order that it
   can bomb out and emit messages under Valgrind's control. */
__attribute__ ((noreturn))
static
void failure_exit ( void )
{
   LibVEX_ShowAllocStats();
   VG_(core_panic)("LibVEX called failure_exit().");
}

static
void log_bytes ( HChar* bytes, Int nbytes )
{
  Int i;
  for (i = 0; i < nbytes-3; i += 4)
     VG_(printf)("%c%c%c%c", bytes[i], bytes[i+1], bytes[i+2], bytes[i+3]);
  for (; i < nbytes; i++) 
     VG_(printf)("%c", bytes[i]);
}

/* Translate the basic block beginning at orig_addr, and add it to
   the translation cache & translation table.  Unless 'debugging' is true,
   in which case the call is being done for debugging purposes, so
   (a) throw away the translation once it is made, and (b) produce a
   load of debugging output. 

   'tid' is the identity of the thread needing this block.
*/

/* This stops Vex from chasing into function entry points that we wish
   to redirect.  Chasing across them obviously defeats the redirect
   mechanism, with bad effects for Memcheck, Addrcheck, and possibly
   others. */
static Bool chase_into_ok ( Addr64 addr64 )
{
  Addr addr = (Addr)addr64;
  if (addr != VG_(code_redirect)(addr)) {
     if (0) VG_(printf)("not chasing into 0x%x\n", addr);
     return False;
  } else {
     return True; /* ok to chase into 'addr' */
  }
}

static Bool need_to_handle_SP_assignment(void)
{
   return ( VG_(defined_new_mem_stack_4)()  ||
            VG_(defined_die_mem_stack_4)()  ||
            VG_(defined_new_mem_stack_8)()  ||
            VG_(defined_die_mem_stack_8)()  ||
            VG_(defined_new_mem_stack_12)() ||
            VG_(defined_die_mem_stack_12)() ||
            VG_(defined_new_mem_stack_16)() ||
            VG_(defined_die_mem_stack_16)() ||
            VG_(defined_new_mem_stack_32)() ||
            VG_(defined_die_mem_stack_32)() ||
            VG_(defined_new_mem_stack)()    ||
            VG_(defined_die_mem_stack)()
          );
}


Bool VG_(translate) ( ThreadId tid, 
                      Addr64   orig_addr,
                      Bool     debugging_translation,
                      Int      debugging_verbosity )
{
   Addr64    redir, orig_addr0 = orig_addr;
   Int       tmpbuf_used, verbosity;
   Bool      notrace_until_done;
   UInt      notrace_until_limit = 0;
   Segment*  seg;
   VexGuestExtents vge;

   /* Make sure Vex is initialised right. */
   VexTranslateResult tres;
   static Bool vex_init_done = False;

   if (!vex_init_done) {
      LibVEX_Init ( &failure_exit, &log_bytes, 
                    1,     /* debug_paranoia */ 
                    False, /* valgrind support */
                    &VG_(clo_vex_control) );
      vex_init_done = True;
   }

   /* profiling ... */
   VGP_PUSHCC(VgpTranslate);

   /* Look in the code redirect table to see if we should
      translate an alternative address for orig_addr. */
   redir = VG_(code_redirect)(orig_addr);

   if (redir != orig_addr && VG_(clo_verbosity) >= 2) {
      Bool ok;
      Char name1[64] = "";
      Char name2[64] = "";
      name1[0] = name2[0] = 0;
      ok = VG_(get_fnname_w_offset)(orig_addr, name1, 64);
      if (!ok) VG_(strcpy)(name1, "???");
      ok = VG_(get_fnname_w_offset)(redir, name2, 64);
      if (!ok) VG_(strcpy)(name2, "???");
      VG_(message)(Vg_DebugMsg, 
                   "TRANSLATE: 0x%llx (%s) redirected to 0x%llx (%s)",
                   orig_addr, name1,
                   redir, name2 );
   }
   orig_addr = redir;

   /* If codegen tracing, don't start tracing until
      notrace_until_limit blocks have gone by.  This avoids printing
      huge amounts of useless junk when all we want to see is the last
      few blocks translated prior to a failure.  Set
      notrace_until_limit to be the number of translations to be made
      before --trace-codegen= style printing takes effect. */
   notrace_until_done
      = VG_(get_bbs_translated)() >= notrace_until_limit;

   seg = VG_(find_segment)(orig_addr);

   if (!debugging_translation)
      VG_TRACK( pre_mem_read, Vg_CoreTranslate, tid, "", orig_addr, 1 );

   /* If doing any code printing, print a basic block start marker */
   if (VG_(clo_trace_flags) || debugging_translation) {
      Char fnname[64] = "";
      VG_(get_fnname_w_offset)(orig_addr, fnname, 64);
      VG_(printf)(
              "==== BB %d %s(0x%llx) approx BBs exec'd %lld ====\n",
              VG_(get_bbs_translated)(), fnname, orig_addr, 
              VG_(bbs_done));
   }

   if (seg == NULL ||
       !VG_(seg_contains)(seg, orig_addr, 1) || 
       (seg->prot & (VKI_PROT_READ|VKI_PROT_EXEC)) == 0) {
      /* Code address is bad - deliver a signal instead */
      vg_assert(!VG_(is_addressable)(orig_addr, 1, 
                                     VKI_PROT_READ|VKI_PROT_EXEC));

      if (seg != NULL && VG_(seg_contains)(seg, orig_addr, 1)) {
         vg_assert((seg->prot & VKI_PROT_EXEC) == 0);
         VG_(synth_fault_perms)(tid, orig_addr);
      } else
         VG_(synth_fault_mapping)(tid, orig_addr);

      return False;
   } else
      seg->flags |= SF_CODE;        /* contains cached code */

   /* True if a debug trans., or if bit N set in VG_(clo_trace_codegen). */
   verbosity = 0;
   if (debugging_translation) {
      verbosity = debugging_verbosity;
   }
   else
   if ( (VG_(clo_trace_flags) > 0
        && VG_(get_bbs_translated)() >= VG_(clo_trace_notbelow) )) {
      verbosity = VG_(clo_trace_flags);
   }

   /* Actually do the translation. */
   tres = LibVEX_Translate ( 
             VG_(vex_arch), VG_(vex_subarch),
             VG_(vex_arch), VG_(vex_subarch),
             (UChar*)ULong_to_Ptr(orig_addr), 
             (Addr64)orig_addr, 
             chase_into_ok,
             &vge,
             tmpbuf, N_TMPBUF, &tmpbuf_used,
             TL_(instrument),
             need_to_handle_SP_assignment()
                ? vg_SP_update_pass
                : NULL,
             True, /* cleanup after instrumentation */
             NULL,
             verbosity
          );

   vg_assert(tres == VexTransOK);
   vg_assert(tmpbuf_used <= N_TMPBUF);
   vg_assert(tmpbuf_used > 0);

#undef DECIDE_IF_PRINTING_CODEGEN

   /* Copy data at trans_addr into the translation cache. */
   vg_assert(tmpbuf_used > 0 && tmpbuf_used < 65536);

   // If debugging, don't do anything with the translated block;  we
   // only did this for the debugging output produced along the way.
   if (!debugging_translation) {
      // Note that we use orig_addr0, not orig_addr, which might have been
      // changed by the redirection
      VG_(add_to_trans_tab)( &vge,
                             orig_addr0,
                             (Addr)(&tmpbuf[0]), 
                             tmpbuf_used );
   }

   VGP_POPCC(VgpTranslate);

   return True;
}

/*--------------------------------------------------------------------*/
/*--- end                                           vg_translate.c ---*/
/*--------------------------------------------------------------------*/

