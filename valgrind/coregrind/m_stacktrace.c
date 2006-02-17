
/*--------------------------------------------------------------------*/
/*--- Take snapshots of client stacks.              m_stacktrace.c ---*/
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

#include "pub_core_basics.h"
#include "pub_core_threadstate.h"
#include "pub_core_debuginfo.h"
#include "pub_core_aspacemgr.h"     // For VG_(is_addressable)()
#include "pub_core_libcbase.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcprint.h"
#include "pub_core_machine.h"
#include "pub_core_options.h"
#include "pub_core_stacktrace.h"
#include "pub_core_trampoline.h"

/*------------------------------------------------------------*/
/*--- Exported functions.                                  ---*/
/*------------------------------------------------------------*/

/* Take a snapshot of the client's stack, putting the up to 'n_ips'
   IPs into 'ips'.  In order to be thread-safe, we pass in the
   thread's IP SP, FP if that's meaningful, and LR if that's
   meaningful.  Returns number of IPs put in 'ips'.

   If you know what the thread ID for this stack is, send that as the
   first parameter, else send zero.  This helps generate better stack
   traces on ppc64-linux and has no effect on other platforms.
*/
UInt VG_(get_StackTrace2) ( ThreadId tid_if_known,
                            Addr* ips, UInt n_ips, 
                            Addr ip, Addr sp, Addr fp, Addr lr,
                            Addr fp_min, Addr fp_max_orig )
{
#if defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   Bool  lr_is_first_RA = False; /* ppc only */
#endif
   Bool  debug = False;
   Int   i;
   Addr  fp_max;
   UInt  n_found = 0;

   vg_assert(sizeof(Addr) == sizeof(UWord));
   vg_assert(sizeof(Addr) == sizeof(void*));

   /* Snaffle IPs from the client's stack into ips[0 .. n_ips-1],
      stopping when the trail goes cold, which we guess to be
      when FP is not a reasonable stack location. */

   // JRS 2002-sep-17: hack, to round up fp_max to the end of the
   // current page, at least.  Dunno if it helps.
   // NJN 2002-sep-17: seems to -- stack traces look like 1.0.X again
   fp_max = VG_PGROUNDUP(fp_max_orig);
   fp_max -= sizeof(Addr);

   if (debug)
      VG_(printf)("n_ips=%d fp_min=%p fp_max_orig=%p, fp_max=%p ip=%p fp=%p\n",
		  n_ips, fp_min, fp_max_orig, fp_max, ip, fp);

   /* Assertion broken before main() is reached in pthreaded programs;  the
    * offending stack traces only have one item.  --njn, 2002-aug-16 */
   /* vg_assert(fp_min <= fp_max);*/

   if (fp_min + VG_(clo_max_stackframe) <= fp_max) {
      /* If the stack is ridiculously big, don't poke around ... but
         don't bomb out either.  Needed to make John Regehr's
         user-space threads package work. JRS 20021001 */
      ips[0] = ip;
      return 1;
   } 

   /* Otherwise unwind the stack in a platform-specific way.  Trying
      to merge the x86, amd64, ppc32 and ppc64 logic into a single
      piece of code is just too confusing and difficult to
      performance-tune.  */

#  if defined(VGP_x86_linux)

   /*--------------------- x86 ---------------------*/

   /* fp is %ebp.  sp is %esp.  ip is %eip. */

   ips[0] = ip;
   i = 1;

   /* Loop unwinding the stack. Note that the IP value we get on
    * each pass (whether from CFI info or a stack frame) is a
    * return address so is actually after the calling instruction
    * in the calling function.
    *
    * Because of this we subtract one from the IP after each pass
    * of the loop so that we find the right CFI block on the next
    * pass - otherwise we can find the wrong CFI info if it happens
    * to change after the calling instruction and that will mean
    * that we will fail to unwind the next step.
    *
    * This most frequently happens at the end of a function when
    * a tail call occurs and we wind up using the CFI info for the
    * next function which is completely wrong.
    */
   while (True) {

      if (i >= n_ips)
         break;

      /* Try to derive a new (ip,sp,fp) triple from the current
         set. */

      /* On x86, first try the old-fashioned method of following the
         %ebp-chain.  Code which doesn't use this (that is, compiled
         with -fomit-frame-pointer) is not ABI compliant and so
         relatively rare.  Besides, trying the CFI first almost always
         fails, and is expensive. */
      /* Deal with frames resulting from functions which begin "pushl%
         ebp ; movl %esp, %ebp" which is the ABI-mandated preamble. */
      if (fp_min <= fp && fp <= fp_max) {
         /* fp looks sane, so use it. */
         ip = (((UWord*)fp)[1]);
         sp = fp + sizeof(Addr) /*saved %ebp*/ 
                 + sizeof(Addr) /*ra*/;
         fp = (((UWord*)fp)[0]);
         ips[i++] = ip;
         if (debug)
            VG_(printf)("     ipsF[%d]=%08p\n", i-1, ips[i-1]);
         ip = ip - 1;
         continue;
      }

      /* That didn't work out, so see if there is any CFI info to hand
         which can be used. */
      if ( VG_(use_CFI_info)( &ip, &sp, &fp, fp_min, fp_max ) ) {
         ips[i++] = ip;
         if (debug)
            VG_(printf)("     ipsC[%d]=%08p\n", i-1, ips[i-1]);
         ip = ip - 1;
         continue;
      }

      /* No luck.  We have to give up. */
      break;
   }

#  elif defined(VGP_amd64_linux)

   /*--------------------- amd64 ---------------------*/

   /* fp is %rbp.  sp is %rsp.  ip is %rip. */

   ips[0] = ip;
   i = 1;

   /* Loop unwinding the stack. Note that the IP value we get on
    * each pass (whether from CFI info or a stack frame) is a
    * return address so is actually after the calling instruction
    * in the calling function.
    *
    * Because of this we subtract one from the IP after each pass
    * of the loop so that we find the right CFI block on the next
    * pass - otherwise we can find the wrong CFI info if it happens
    * to change after the calling instruction and that will mean
    * that we will fail to unwind the next step.
    *
    * This most frequently happens at the end of a function when
    * a tail call occurs and we wind up using the CFI info for the
    * next function which is completely wrong.
    */
   while (True) {

      if (i >= n_ips)
         break;

      /* Try to derive a new (ip,sp,fp) triple from the current
         set. */

      /* First off, see if there is any CFI info to hand which can
         be used. */
      if ( VG_(use_CFI_info)( &ip, &sp, &fp, fp_min, fp_max ) ) {
         ips[i++] = ip;
         if (debug)
            VG_(printf)("     ipsC[%d]=%08p\n", i-1, ips[i-1]);
         ip = ip - 1;
         continue;
      }

      /* If VG_(use_CFI_info) fails, it won't modify ip/sp/fp, so
         we can safely try the old-fashioned method. */
      /* This bit is supposed to deal with frames resulting from
         functions which begin "pushq %rbp ; movq %rsp, %rbp".
         Unfortunately, since we can't (easily) look at the insns at
         the start of the fn, like GDB does, there's no reliable way
         to tell.  Hence the hack of first trying out CFI, and if that
         fails, then use this as a fallback. */
      if (fp_min <= fp && fp <= fp_max) {
         /* fp looks sane, so use it. */
         ip = (((UWord*)fp)[1]);
         sp = fp + sizeof(Addr) /*saved %rbp*/ 
                 + sizeof(Addr) /*ra*/;
         fp = (((UWord*)fp)[0]);
         ips[i++] = ip;
         if (debug)
            VG_(printf)("     ipsF[%d]=%08p\n", i-1, ips[i-1]);
         ip = ip - 1;
         continue;
      }

      /* No luck there.  We have to give up. */
      break;
   }

#  elif defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)

   /*--------------------- ppc32/64 ---------------------*/

   /* fp is %r1.  ip is %cia.  Note, ppc uses r1 as both the stack and
      frame pointers. */

#  if defined(VGP_ppc64_linux)
   /* Deal with bogus LR values caused by function
      interception/wrapping; see comment on similar code a few lines
      further down. */
   if (lr == (Addr)&VG_(ppc64_linux_magic_redirect_return_stub)
       && VG_(is_valid_tid)(tid_if_known)) {
      Long hsp = VG_(threads)[tid_if_known].arch.vex.guest_REDIR_SP;
      if (hsp >= 1 && hsp < VEX_GUEST_PPC64_REDIR_STACK_SIZE)
         lr = VG_(threads)[tid_if_known]
                 .arch.vex.guest_REDIR_STACK[hsp-1];
   }
#  endif

   lr_is_first_RA = False;
   {
#     define M_VG_ERRTXT 1000
      UChar buf_lr[M_VG_ERRTXT], buf_ip[M_VG_ERRTXT];
      if (VG_(get_fnname_nodemangle) (lr, buf_lr, M_VG_ERRTXT))
         if (VG_(get_fnname_nodemangle) (ip, buf_ip, M_VG_ERRTXT))
            if (VG_(strncmp)(buf_lr, buf_ip, M_VG_ERRTXT))
               lr_is_first_RA = True;
#     undef M_VG_ERRTXT
   }

   ips[0] = ip;
   i = 1;

   if (fp_min <= fp && fp < fp_max-VG_WORDSIZE+1) {

      /* initial FP is sane; keep going */
      fp = (((UWord*)fp)[0]);

      while (True) {

        /* on ppc64-linux (ppc64-elf, really), the lr save slot is 2
           words back from sp, whereas on ppc32-elf(?) it's only one
           word back. */
#        if defined(VGP_ppc64_linux)
         const Int lr_offset = 2;
#        else
         const Int lr_offset = 1;
#        endif

         if (i >= n_ips)
            break;

         /* Try to derive a new (ip,fp) pair from the current set. */

         if (fp_min <= fp && fp <= fp_max) {
            /* fp looks sane, so use it. */

            if (i == 1 && lr_is_first_RA)
               ip = lr;
            else
               ip = (((UWord*)fp)[lr_offset]);

#           if defined(VGP_ppc64_linux)
            /* Nasty hack to do with function replacement/wrapping on
               ppc64-linux.  If LR points to our magic return stub,
               then we are in a wrapped or intercepted function, in
               which LR has been messed with.  The original LR will
               have been pushed onto the thread's hidden REDIR stack
               one down from the top (top element is the saved R2) and
               so we should restore the value from there instead. */
            if (i == 1 
                && ip == (Addr)&VG_(ppc64_linux_magic_redirect_return_stub)
                && VG_(is_valid_tid)(tid_if_known)) {
               Long hsp = VG_(threads)[tid_if_known].arch.vex.guest_REDIR_SP;
               if (hsp >= 1 && hsp < VEX_GUEST_PPC64_REDIR_STACK_SIZE)
                  ip = VG_(threads)[tid_if_known]
                          .arch.vex.guest_REDIR_STACK[hsp-1];
            }
#           endif

            fp = (((UWord*)fp)[0]);
            ips[i++] = ip;
            if (debug)
               VG_(printf)("     ipsF[%d]=%08p\n", i-1, ips[i-1]);
            continue;
         }

         /* No luck there.  We have to give up. */
         break;
      }
   }

#  else
#    error "Unknown platform"
#  endif

   n_found = i;
   return n_found;
}

UInt VG_(get_StackTrace) ( ThreadId tid, StackTrace ips, UInt n_ips )
{
   /* thread in thread table */
   Addr ip                 = VG_(get_IP)(tid);
   Addr fp                 = VG_(get_FP)(tid);
   Addr sp                 = VG_(get_SP)(tid);
   Addr lr                 = VG_(get_LR)(tid);
   Addr stack_highest_word = VG_(threads)[tid].client_stack_highest_word;

#  if defined(VGP_x86_linux)
   /* Nasty little hack to deal with sysinfo syscalls - if libc is
      using the sysinfo page for syscalls (the TLS version does), then
      ip will always appear to be in that page when doing a syscall,
      not the actual libc function doing the syscall.  This check sees
      if IP is within the syscall code, and pops the return address
      off the stack so that ip is placed within the library function
      calling the syscall.  This makes stack backtraces much more
      useful.  */
   if (ip >= (Addr)&VG_(trampoline_stuff_start) 
       && ip < (Addr)&VG_(trampoline_stuff_end)
       && VG_(am_is_valid_for_client)(sp, sizeof(Addr), VKI_PROT_READ)) {
      ip = *(Addr *)sp;
      sp += sizeof(Addr);
   }
#  endif

   if (0)
      VG_(printf)("tid %d: stack_highest=%p ip=%p sp=%p fp=%p\n",
		  tid, stack_highest_word, ip, sp, fp);

   return VG_(get_StackTrace2)(tid, ips, n_ips, ip, sp, fp, lr, sp, 
                                    stack_highest_word);
}

static void printIpDesc(UInt n, Addr ip)
{
   #define BUF_LEN   4096
   
   static UChar buf[BUF_LEN];

   VG_(describe_IP)(ip, buf, BUF_LEN);

   if (VG_(clo_xml)) {
      VG_(message)(Vg_UserMsg, "    %s", buf);
   } else {
      VG_(message)(Vg_UserMsg, "   %s %s", ( n == 0 ? "at" : "by" ), buf);
   }
}

/* Print a StackTrace. */
void VG_(pp_StackTrace) ( StackTrace ips, UInt n_ips )
{
   vg_assert( n_ips > 0 );

   if (VG_(clo_xml))
      VG_(message)(Vg_UserMsg, "  <stack>");

   VG_(apply_StackTrace)( printIpDesc, ips, n_ips );

   if (VG_(clo_xml))
      VG_(message)(Vg_UserMsg, "  </stack>");
}

/* Get and immediately print a StackTrace. */
void VG_(get_and_pp_StackTrace) ( ThreadId tid, UInt n_ips )
{
   Addr ips[n_ips];
   VG_(get_StackTrace)(tid, ips, n_ips);
   VG_(pp_StackTrace) (     ips, n_ips);
}


void VG_(apply_StackTrace)( void(*action)(UInt n, Addr ip),
                            StackTrace ips, UInt n_ips )
{
   #define MYBUF_LEN 50  // only needs to be long enough for 
                         // the names specially tested for

   Bool main_done = False;
   Char mybuf[MYBUF_LEN];     // ok to stack allocate mybuf[] -- it's tiny
   Int i = 0;

   vg_assert(n_ips > 0);
   do {
      Addr ip = ips[i];
      if (i > 0) 
         ip -= VG_MIN_INSTR_SZB;   // point to calling line

      // Stop after the first appearance of "main" or one of the other names
      // (the appearance of which is a pretty good sign that we've gone past
      // main without seeing it, for whatever reason)
      if ( ! VG_(clo_show_below_main)) {
         VG_(get_fnname_nodemangle)( ip, mybuf, MYBUF_LEN );
         mybuf[MYBUF_LEN-1] = 0; // paranoia
         if ( VG_STREQ("main", mybuf)
#             if defined(VGO_linux)
              || VG_STREQ("__libc_start_main", mybuf)   // glibc glibness
              || VG_STREQ("generic_start_main", mybuf)  // Yellow Dog doggedness
#             endif
            )
            main_done = True;
      }

      // Act on the ip
      action(i, ip);

      i++;
   } while (i < n_ips && ips[i] != 0 && !main_done);

   #undef MYBUF_LEN
}


/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
