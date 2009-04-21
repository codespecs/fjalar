
/*--------------------------------------------------------------------*/
/*--- Implementation of POSIX signals.                 m_signals.c ---*/
/*--------------------------------------------------------------------*/
 
/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2008 Julian Seward 
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

/* 
   Signal handling.

   There are 4 distinct classes of signal:

   1. Synchronous, instruction-generated (SIGILL, FPE, BUS, SEGV and
   TRAP): these are signals as a result of an instruction fault.  If
   we get one while running client code, then we just do the
   appropriate thing.  If it happens while running Valgrind code, then
   it indicates a Valgrind bug.  Note that we "manually" implement
   automatic stack growth, such that if a fault happens near the
   client process stack, it is extended in the same way the kernel
   would, and the fault is never reported to the client program.

   2. Asynchronous varients of the above signals: If the kernel tries
   to deliver a sync signal while it is blocked, it just kills the
   process.  Therefore, we can't block those signals if we want to be
   able to report on bugs in Valgrind.  This means that we're also
   open to receiving those signals from other processes, sent with
   kill.  We could get away with just dropping them, since they aren't
   really signals that processes send to each other.

   3. Synchronous, general signals.  If a thread/process sends itself
   a signal with kill, its expected to be synchronous: ie, the signal
   will have been delivered by the time the syscall finishes.
   
   4. Asyncronous, general signals.  All other signals, sent by
   another process with kill.  These are generally blocked, except for
   two special cases: we poll for them each time we're about to run a
   thread for a time quanta, and while running blocking syscalls.


   In addition, we define two signals for internal use: SIGVGCHLD and
   SIGVGKILL.  SIGVGCHLD is used to indicate thread death to any
   reaping thread (the master thread).  It is always blocked and never
   delivered as a signal; it is always polled with sigtimedwait.

   SIGVGKILL is used to terminate threads.  When one thread wants
   another to exit, it will set its exitreason and send it SIGVGKILL
   if it appears to be blocked in a syscall.


   We use a kernel thread for each application thread.  When the
   thread allows itself to be open to signals, it sets the thread
   signal mask to what the client application set it to.  This means
   that we get the kernel to do all signal routing: under Valgrind,
   signals get delivered in the same way as in the non-Valgrind case
   (the exception being for the sync signal set, since they're almost
   always unblocked).
 */

#include "pub_core_basics.h"
#include "pub_core_vki.h"
#include "pub_core_vkiscnums.h"
#include "pub_core_debuglog.h"
#include "pub_core_threadstate.h"
#include "pub_core_xarray.h"
#include "pub_core_clientstate.h"
#include "pub_core_aspacemgr.h"
#include "pub_core_debugger.h"      // For VG_(start_debugger)
#include "pub_core_errormgr.h"
#include "pub_core_libcbase.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcprint.h"
#include "pub_core_libcproc.h"
#include "pub_core_libcsignal.h"
#include "pub_core_machine.h"
#include "pub_core_mallocfree.h"
#include "pub_core_options.h"
#include "pub_core_scheduler.h"
#include "pub_core_signals.h"
#include "pub_core_sigframe.h"      // For VG_(sigframe_create)()
#include "pub_core_stacks.h"        // For VG_(change_stack)()
#include "pub_core_stacktrace.h"    // For VG_(get_and_pp_StackTrace)()
#include "pub_core_syscall.h"
#include "pub_core_syswrap.h"
#include "pub_core_tooliface.h"
#include "pub_core_coredump.h"


/* ---------------------------------------------------------------------
   Forwards decls.
   ------------------------------------------------------------------ */

static void sync_signalhandler  ( Int sigNo, vki_siginfo_t *info, struct vki_ucontext * );
static void async_signalhandler ( Int sigNo, vki_siginfo_t *info, struct vki_ucontext * );
static void sigvgkill_handler	( Int sigNo, vki_siginfo_t *info, struct vki_ucontext * );

static const Char *signame(Int sigNo);

/* Maximum usable signal. */
Int VG_(max_signal) = _VKI_NSIG;

#define N_QUEUED_SIGNALS	8

typedef struct SigQueue {
   Int	next;
   vki_siginfo_t sigs[N_QUEUED_SIGNALS];
} SigQueue;

/* ------ Macros for pulling stuff out of ucontexts ------ */

#if defined(VGP_x86_linux)
#  define VG_UCONTEXT_INSTR_PTR(uc)       ((uc)->uc_mcontext.eip)
#  define VG_UCONTEXT_STACK_PTR(uc)       ((uc)->uc_mcontext.esp)
#  define VG_UCONTEXT_FRAME_PTR(uc)       ((uc)->uc_mcontext.ebp)
#  define VG_UCONTEXT_SYSCALL_NUM(uc)     ((uc)->uc_mcontext.eax)
#  define VG_UCONTEXT_SYSCALL_SYSRES(uc)                        \
      /* Convert the value in uc_mcontext.eax into a SysRes. */ \
      VG_(mk_SysRes_x86_linux)( (uc)->uc_mcontext.eax )
#  define VG_UCONTEXT_LINK_REG(uc)        0 /* Dude, where's my LR? */

#elif defined(VGP_amd64_linux)
#  define VG_UCONTEXT_INSTR_PTR(uc)       ((uc)->uc_mcontext.rip)
#  define VG_UCONTEXT_STACK_PTR(uc)       ((uc)->uc_mcontext.rsp)
#  define VG_UCONTEXT_FRAME_PTR(uc)       ((uc)->uc_mcontext.rbp)
#  define VG_UCONTEXT_SYSCALL_NUM(uc)     ((uc)->uc_mcontext.rax)
#  define VG_UCONTEXT_SYSCALL_SYSRES(uc)                        \
      /* Convert the value in uc_mcontext.rax into a SysRes. */ \
      VG_(mk_SysRes_amd64_linux)( (uc)->uc_mcontext.rax )
#  define VG_UCONTEXT_LINK_REG(uc)        0 /* No LR on amd64 either */

#elif defined(VGP_ppc32_linux)
/* Comments from Paul Mackerras 25 Nov 05:

   > I'm tracking down a problem where V's signal handling doesn't
   > work properly on a ppc440gx running 2.4.20.  The problem is that
   > the ucontext being presented to V's sighandler seems completely
   > bogus.

   > V's kernel headers and hence ucontext layout are derived from
   > 2.6.9.  I compared include/asm-ppc/ucontext.h from 2.4.20 and
   > 2.6.13.

   > Can I just check my interpretation: the 2.4.20 one contains the
   > uc_mcontext field in line, whereas the 2.6.13 one has a pointer
   > to said struct?  And so if V is using the 2.6.13 struct then a
   > 2.4.20 one will make no sense to it.

   Not quite... what is inline in the 2.4.20 version is a
   sigcontext_struct, not an mcontext.  The sigcontext looks like
   this:

     struct sigcontext_struct {
        unsigned long   _unused[4];
        int             signal;
        unsigned long   handler;
        unsigned long   oldmask;
        struct pt_regs  *regs;
     };

   The regs pointer of that struct ends up at the same offset as the
   uc_regs of the 2.6 struct ucontext, and a struct pt_regs is the
   same as the mc_gregs field of the mcontext.  In fact the integer
   regs are followed in memory by the floating point regs on 2.4.20.

   Thus if you are using the 2.6 definitions, it should work on 2.4.20
   provided that you go via uc->uc_regs rather than looking in
   uc->uc_mcontext directly.

   There is another subtlety: 2.4.20 doesn't save the vector regs when
   delivering a signal, and 2.6.x only saves the vector regs if the
   process has ever used an altivec instructions.  If 2.6.x does save
   the vector regs, it sets the MSR_VEC bit in
   uc->uc_regs->mc_gregs[PT_MSR], otherwise it clears it.  That bit
   will always be clear under 2.4.20.  So you can use that bit to tell
   whether uc->uc_regs->mc_vregs is valid. */
#  define VG_UCONTEXT_INSTR_PTR(uc)       ((uc)->uc_regs->mc_gregs[VKI_PT_NIP])
#  define VG_UCONTEXT_STACK_PTR(uc)       ((uc)->uc_regs->mc_gregs[VKI_PT_R1])
#  define VG_UCONTEXT_FRAME_PTR(uc)       ((uc)->uc_regs->mc_gregs[VKI_PT_R1])
#  define VG_UCONTEXT_SYSCALL_NUM(uc)     ((uc)->uc_regs->mc_gregs[VKI_PT_R0])
#  define VG_UCONTEXT_SYSCALL_SYSRES(uc)                            \
      /* Convert the values in uc_mcontext r3,cr into a SysRes. */  \
      VG_(mk_SysRes_ppc32_linux)(                                   \
         (uc)->uc_regs->mc_gregs[VKI_PT_R3],                        \
         (((uc)->uc_regs->mc_gregs[VKI_PT_CCR] >> 28) & 1)          \
      )
#  define VG_UCONTEXT_LINK_REG(uc)        ((uc)->uc_regs->mc_gregs[VKI_PT_LNK]) 

#elif defined(VGP_ppc64_linux)
#  define VG_UCONTEXT_INSTR_PTR(uc)       ((uc)->uc_mcontext.gp_regs[VKI_PT_NIP])
#  define VG_UCONTEXT_STACK_PTR(uc)       ((uc)->uc_mcontext.gp_regs[VKI_PT_R1])
#  define VG_UCONTEXT_FRAME_PTR(uc)       ((uc)->uc_mcontext.gp_regs[VKI_PT_R1])
#  define VG_UCONTEXT_SYSCALL_NUM(uc)     ((uc)->uc_mcontext.gp_regs[VKI_PT_R0])
   /* Dubious hack: if there is an error, only consider the lowest 8
      bits of r3.  memcheck/tests/post-syscall shows a case where an
      interrupted syscall should have produced a ucontext with 0x4
      (VKI_EINTR) in r3 but is in fact producing 0x204. */
   /* Awaiting clarification from PaulM.  Evidently 0x204 is
      ERESTART_RESTARTBLOCK, which shouldn't have made it into user
      space. */
   static inline SysRes VG_UCONTEXT_SYSCALL_SYSRES( struct vki_ucontext* uc )
   {
      ULong err = (uc->uc_mcontext.gp_regs[VKI_PT_CCR] >> 28) & 1;
      ULong r3  = uc->uc_mcontext.gp_regs[VKI_PT_R3];
      if (err) r3 &= 0xFF;
      return VG_(mk_SysRes_ppc64_linux)( r3, err );
   }
#  define VG_UCONTEXT_LINK_REG(uc)        ((uc)->uc_mcontext.gp_regs[VKI_PT_LNK]) 

#elif defined(VGP_ppc32_aix5)

   /* --- !!! --- EXTERNAL HEADERS start --- !!! --- */
#  include <ucontext.h>
   /* --- !!! --- EXTERNAL HEADERS end --- !!! --- */
   static inline Addr VG_UCONTEXT_INSTR_PTR( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct mstsave* jc = &mc->jmp_context;
      return jc->iar;
   }
   static inline Addr VG_UCONTEXT_STACK_PTR( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct mstsave* jc = &mc->jmp_context;
      return jc->gpr[1];
   }
   static inline Addr VG_UCONTEXT_SYSCALL_NUM( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct mstsave* jc = &mc->jmp_context;
      return jc->gpr[2];
   }
   static inline SysRes VG_UCONTEXT_SYSCALL_SYSRES( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct mstsave* jc = &mc->jmp_context;
      return VG_(mk_SysRes_ppc32_aix5)( jc->gpr[3], jc->gpr[4] );
   }
   static inline Addr VG_UCONTEXT_LINK_REG( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct mstsave* jc = &mc->jmp_context;
      return jc->lr;
   }
   static inline Addr VG_UCONTEXT_FRAME_PTR( void* ucV ) {
      return VG_UCONTEXT_STACK_PTR(ucV);
   }

#elif defined(VGP_ppc64_aix5)

   /* --- !!! --- EXTERNAL HEADERS start --- !!! --- */
#  include <ucontext.h>
   /* --- !!! --- EXTERNAL HEADERS end --- !!! --- */
   static inline Addr VG_UCONTEXT_INSTR_PTR( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct __context64* jc = &mc->jmp_context;
      return jc->iar;
   }
   static inline Addr VG_UCONTEXT_STACK_PTR( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct __context64* jc = &mc->jmp_context;
      return jc->gpr[1];
   }
   static inline Addr VG_UCONTEXT_SYSCALL_NUM( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct __context64* jc = &mc->jmp_context;
      return jc->gpr[2];
   }
   static inline SysRes VG_UCONTEXT_SYSCALL_SYSRES( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct __context64* jc = &mc->jmp_context;
      return VG_(mk_SysRes_ppc32_aix5)( jc->gpr[3], jc->gpr[4] );
   }
   static inline Addr VG_UCONTEXT_LINK_REG( void* ucV ) {
      ucontext_t* uc = (ucontext_t*)ucV;
      struct __jmpbuf* mc = &(uc->uc_mcontext);
      struct __context64* jc = &mc->jmp_context;
      return jc->lr;
   }
   static inline Addr VG_UCONTEXT_FRAME_PTR( void* ucV ) {
      return VG_UCONTEXT_STACK_PTR(ucV);
   }

#else 
#  error Unknown platform
#endif


/* ------ Macros for pulling stuff out of siginfos ------ */

/* These macros allow use of uniform names when working with
   both the Linux and AIX vki definitions. */
#if defined(VGO_linux)
#  define VKI_SIGINFO_si_addr  _sifields._sigfault._addr
#  define VKI_SIGINFO_si_pid   _sifields._kill._pid
#elif defined(VGO_aix5)
#  define VKI_SIGINFO_si_addr  si_addr
#  define VKI_SIGINFO_si_pid   si_pid
#else
#  error Unknown OS
#endif


/* ---------------------------------------------------------------------
   HIGH LEVEL STUFF TO DO WITH SIGNALS: POLICY (MOSTLY)
   ------------------------------------------------------------------ */

/* ---------------------------------------------------------------------
   Signal state for this process.
   ------------------------------------------------------------------ */


/* Base-ment of these arrays[_VKI_NSIG].

   Valid signal numbers are 1 .. _VKI_NSIG inclusive.
   Rather than subtracting 1 for indexing these arrays, which
   is tedious and error-prone, they are simply dimensioned 1 larger,
   and entry [0] is not used. 
 */


/* -----------------------------------------------------
   Static client signal state (SCSS).  This is the state
   that the client thinks it has the kernel in.  
   SCSS records verbatim the client's settings.  These 
   are mashed around only when SKSS is calculated from it.
   -------------------------------------------------- */

typedef 
   struct {
      void* scss_handler;  /* VKI_SIG_DFL or VKI_SIG_IGN or ptr to
                              client's handler */
      UInt  scss_flags;
      vki_sigset_t scss_mask;
      void* scss_restorer; /* where sigreturn goes */
   }
   SCSS_Per_Signal;

typedef 
   struct {
      /* per-signal info */
      SCSS_Per_Signal scss_per_sig[1+_VKI_NSIG];

      /* Additional elements to SCSS not stored here:
         - for each thread, the thread's blocking mask
         - for each thread in WaitSIG, the set of waited-on sigs
      */
      } 
      SCSS;

static SCSS scss;


/* -----------------------------------------------------
   Static kernel signal state (SKSS).  This is the state
   that we have the kernel in.  It is computed from SCSS.
   -------------------------------------------------- */

/* Let's do: 
     sigprocmask assigns to all thread masks
     so that at least everything is always consistent
   Flags:
     SA_SIGINFO -- we always set it, and honour it for the client
     SA_NOCLDSTOP -- passed to kernel
     SA_ONESHOT or SA_RESETHAND -- pass through
     SA_RESTART -- we observe this but set our handlers to always restart
     SA_NOMASK or SA_NODEFER -- we observe this, but our handlers block everything
     SA_ONSTACK -- pass through
     SA_NOCLDWAIT -- pass through
*/


typedef 
   struct {
      void* skss_handler;  /* VKI_SIG_DFL or VKI_SIG_IGN 
                              or ptr to our handler */
      UInt skss_flags;
      /* There is no skss_mask, since we know that we will always ask
         for all signals to be blocked in our sighandlers. */
      /* Also there is no skss_restorer. */
   }
   SKSS_Per_Signal;

typedef 
   struct {
      SKSS_Per_Signal skss_per_sig[1+_VKI_NSIG];
   } 
   SKSS;

static SKSS skss;

static Bool is_sig_ign(Int sigNo)
{
   vg_assert(sigNo >= 1 && sigNo <= _VKI_NSIG);

   return scss.scss_per_sig[sigNo].scss_handler == VKI_SIG_IGN;
}

/* ---------------------------------------------------------------------
   Compute the SKSS required by the current SCSS.
   ------------------------------------------------------------------ */

static 
void pp_SKSS ( void )
{
   Int sig;
   VG_(printf)("\n\nSKSS:\n");
   for (sig = 1; sig <= _VKI_NSIG; sig++) {
      VG_(printf)("sig %d:  handler %p,  flags 0x%x\n", sig,
                  skss.skss_per_sig[sig].skss_handler,
                  skss.skss_per_sig[sig].skss_flags );

   }
}

/* This is the core, clever bit.  Computation is as follows:

   For each signal
      handler = if client has a handler, then our handler
                else if client is DFL, then our handler as well
                else (client must be IGN)
			then hander is IGN
*/
static
void calculate_SKSS_from_SCSS ( SKSS* dst )
{
   Int   sig;
   UInt  scss_flags;
   UInt  skss_flags;

   for (sig = 1; sig <= _VKI_NSIG; sig++) {
      void *skss_handler;
      void *scss_handler;
      
      scss_handler = scss.scss_per_sig[sig].scss_handler;
      scss_flags   = scss.scss_per_sig[sig].scss_flags;

      switch(sig) {
      case VKI_SIGSEGV:
      case VKI_SIGBUS:
      case VKI_SIGFPE:
      case VKI_SIGILL:
      case VKI_SIGTRAP:
	 /* For these, we always want to catch them and report, even
	    if the client code doesn't. */
	 skss_handler = sync_signalhandler;
	 break;

      case VKI_SIGCONT:
	 /* Let the kernel handle SIGCONT unless the client is actually
	    catching it. */
      case VKI_SIGCHLD:                                                        
      case VKI_SIGWINCH:                                                       
      case VKI_SIGURG:                                                         
         /* For signals which are have a default action of Ignore,             
            only set a handler if the client has set a signal handler.         
            Otherwise the kernel will interrupt a syscall which                
            wouldn't have otherwise been interrupted. */                 
	 if (scss.scss_per_sig[sig].scss_handler == VKI_SIG_DFL)
	    skss_handler = VKI_SIG_DFL;
	 else if (scss.scss_per_sig[sig].scss_handler == VKI_SIG_IGN)
	    skss_handler = VKI_SIG_IGN;
	 else
	    skss_handler = async_signalhandler;
	 break;

      default:
         // VKI_SIGVG* are runtime variables, so we can't make them            
         // cases in the switch, so we handle them in the 'default' case.
	 if (sig == VG_SIGVGKILL)
	    skss_handler = sigvgkill_handler;
	 else {
	    if (scss_handler == VKI_SIG_IGN)
	       skss_handler = VKI_SIG_IGN;
	    else 
	       skss_handler = async_signalhandler;
	 }
	 break;
      }

      /* Flags */

      skss_flags = 0;

      /* SA_NOCLDSTOP, SA_NOCLDWAIT: pass to kernel */
      skss_flags |= scss_flags & (VKI_SA_NOCLDSTOP | VKI_SA_NOCLDWAIT);

      /* SA_ONESHOT: ignore client setting */
      
      /* SA_RESTART: ignore client setting and always set it for us.
	 Though we never rely on the kernel to restart a
	 syscall, we observe whether it wanted to restart the syscall
	 or not, which is needed by 
         VG_(fixup_guest_state_after_syscall_interrupted) */
      skss_flags |= VKI_SA_RESTART;

      /* SA_NOMASK: ignore it */

      /* SA_ONSTACK: client setting is irrelevant here */
      /* We don't set a signal stack, so ignore */

      /* always ask for SA_SIGINFO */
      skss_flags |= VKI_SA_SIGINFO;

      /* use our own restorer */
      skss_flags |= VKI_SA_RESTORER;

      /* Create SKSS entry for this signal. */
      if (sig != VKI_SIGKILL && sig != VKI_SIGSTOP)
         dst->skss_per_sig[sig].skss_handler = skss_handler;
      else
         dst->skss_per_sig[sig].skss_handler = VKI_SIG_DFL;

      dst->skss_per_sig[sig].skss_flags   = skss_flags;
   }

   /* Sanity checks. */
   vg_assert(dst->skss_per_sig[VKI_SIGKILL].skss_handler == VKI_SIG_DFL);
   vg_assert(dst->skss_per_sig[VKI_SIGSTOP].skss_handler == VKI_SIG_DFL);

   if (0)
      pp_SKSS();
}


/* ---------------------------------------------------------------------
   After a possible SCSS change, update SKSS and the kernel itself.
   ------------------------------------------------------------------ */

// We need two levels of macro-expansion here to convert __NR_rt_sigreturn
// to a number before converting it to a string... sigh.
extern void my_sigreturn(void);

#if defined(VGP_x86_linux)
#  define _MYSIG(name) \
   ".text\n" \
   "my_sigreturn:\n" \
   "	movl	$" #name ", %eax\n" \
   "	int	$0x80\n" \
   ".previous\n"
#elif defined(VGP_amd64_linux)
#  define _MYSIG(name) \
   ".text\n" \
   "my_sigreturn:\n" \
   "	movq	$" #name ", %rax\n" \
   "	syscall\n" \
   ".previous\n"
#elif defined(VGP_ppc32_linux)
#  define _MYSIG(name) \
   ".text\n" \
   "my_sigreturn:\n" \
   "	li	0, " #name "\n" \
   "	sc\n" \
   ".previous\n"
#elif defined(VGP_ppc64_linux)
#  define _MYSIG(name) \
   ".align   2\n" \
   ".globl   my_sigreturn\n" \
   ".section \".opd\",\"aw\"\n" \
   ".align   3\n" \
   "my_sigreturn:\n" \
   ".quad    .my_sigreturn,.TOC.@tocbase,0\n" \
   ".previous\n" \
   ".type    .my_sigreturn,@function\n" \
   ".globl   .my_sigreturn\n" \
   ".my_sigreturn:\n" \
   "	li	0, " #name "\n" \
   "	sc\n"
#elif defined(VGP_ppc32_aix5)
#  define _MYSIG(name) \
   ".globl my_sigreturn\n" \
   "my_sigreturn:\n" \
   ".long 0\n"
#elif defined(VGP_ppc64_aix5)
#  define _MYSIG(name) \
   ".globl my_sigreturn\n" \
   "my_sigreturn:\n" \
   ".long 0\n"
#else
#  error Unknown platform
#endif

#define MYSIG(name)  _MYSIG(name)
asm(
   MYSIG(__NR_rt_sigreturn)
);


static void handle_SCSS_change ( Bool force_update )
{
   Int  res, sig;
   SKSS skss_old;
   struct vki_sigaction ksa, ksa_old;

   /* Remember old SKSS and calculate new one. */
   skss_old = skss;
   calculate_SKSS_from_SCSS ( &skss );

   /* Compare the new SKSS entries vs the old ones, and update kernel
      where they differ. */
   for (sig = 1; sig <= VG_(max_signal); sig++) {

      /* Trying to do anything with SIGKILL is pointless; just ignore
         it. */
      if (sig == VKI_SIGKILL || sig == VKI_SIGSTOP)
         continue;

      if (!force_update) {
         if ((skss_old.skss_per_sig[sig].skss_handler
              == skss.skss_per_sig[sig].skss_handler)
             && (skss_old.skss_per_sig[sig].skss_flags
                 == skss.skss_per_sig[sig].skss_flags))
            /* no difference */
            continue;
      }

      ksa.ksa_handler = skss.skss_per_sig[sig].skss_handler;
      ksa.sa_flags    = skss.skss_per_sig[sig].skss_flags;
#     if !defined(VGP_ppc32_linux) && !defined(VGP_ppc32_aix5) \
                                   && !defined(VGP_ppc64_aix5)
      ksa.sa_restorer = my_sigreturn;
#     endif
      /* Re above ifdef (also the assertion below), PaulM says:
         The sa_restorer field is not used at all on ppc.  Glibc
         converts the sigaction you give it into a kernel sigaction,
         but it doesn't put anything in the sa_restorer field.
      */

      /* block all signals in handler */
      VG_(sigfillset)( &ksa.sa_mask );
      VG_(sigdelset)( &ksa.sa_mask, VKI_SIGKILL );
      VG_(sigdelset)( &ksa.sa_mask, VKI_SIGSTOP );

      if (VG_(clo_trace_signals) && VG_(clo_verbosity) > 2)
         VG_(message)(Vg_DebugMsg, 
            "setting ksig %d to: hdlr %p, flags 0x%lx, "
            "mask(63..0) 0x%lx 0x%lx",
            sig, ksa.ksa_handler,
            (UWord)ksa.sa_flags,
            (UWord)ksa.sa_mask.sig[1], 
            (UWord)ksa.sa_mask.sig[0] 
         );

      res = VG_(sigaction)( sig, &ksa, &ksa_old );
      vg_assert(res == 0);

      /* Since we got the old sigaction more or less for free, might
         as well extract the maximum sanity-check value from it. */
      if (!force_update) {
         vg_assert(ksa_old.ksa_handler 
                   == skss_old.skss_per_sig[sig].skss_handler);
         vg_assert(ksa_old.sa_flags 
                   == skss_old.skss_per_sig[sig].skss_flags);
#        if !defined(VGP_ppc32_linux) && !defined(VGP_ppc32_aix5) \
                                      && !defined(VGP_ppc64_aix5)
         vg_assert(ksa_old.sa_restorer 
                   == my_sigreturn);
#        endif
         VG_(sigaddset)( &ksa_old.sa_mask, VKI_SIGKILL );
         VG_(sigaddset)( &ksa_old.sa_mask, VKI_SIGSTOP );
         vg_assert(VG_(isfullsigset)( &ksa_old.sa_mask ));
      }
   }
}


/* ---------------------------------------------------------------------
   Update/query SCSS in accordance with client requests.
   ------------------------------------------------------------------ */

/* Logic for this alt-stack stuff copied directly from do_sigaltstack
   in kernel/signal.[ch] */

/* True if we are on the alternate signal stack.  */
static Bool on_sig_stack ( ThreadId tid, Addr m_SP )
{
   ThreadState *tst = VG_(get_ThreadState)(tid);

   return (m_SP - (Addr)tst->altstack.ss_sp < tst->altstack.ss_size);
}

static Int sas_ss_flags ( ThreadId tid, Addr m_SP )
{
   ThreadState *tst = VG_(get_ThreadState)(tid);

   return (tst->altstack.ss_size == 0 
              ? VKI_SS_DISABLE
              : on_sig_stack(tid, m_SP) ? VKI_SS_ONSTACK : 0);
}


SysRes VG_(do_sys_sigaltstack) ( ThreadId tid, vki_stack_t* ss, vki_stack_t* oss )
{
   Addr m_SP;

   vg_assert(VG_(is_valid_tid)(tid));
   m_SP  = VG_(get_SP)(tid);

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugExtraMsg, 
         "sys_sigaltstack: tid %d, "
         "ss %p, oss %p (current SP %p)",
         tid, (void*)ss, (void*)oss, (void*)m_SP );

   if (oss != NULL) {
      oss->ss_sp    = VG_(threads)[tid].altstack.ss_sp;
      oss->ss_size  = VG_(threads)[tid].altstack.ss_size;
      oss->ss_flags = VG_(threads)[tid].altstack.ss_flags | sas_ss_flags(tid, m_SP);
   }

   if (ss != NULL) {
      if (on_sig_stack(tid, VG_(get_SP)(tid))) {
         return VG_(mk_SysRes_Error)( VKI_EPERM );
      }
      if (ss->ss_flags != VKI_SS_DISABLE 
          && ss->ss_flags != VKI_SS_ONSTACK 
          && ss->ss_flags != 0) {
         return VG_(mk_SysRes_Error)( VKI_EINVAL );
      }
      if (ss->ss_flags == VKI_SS_DISABLE) {
         VG_(threads)[tid].altstack.ss_flags = VKI_SS_DISABLE;
      } else {
         if (ss->ss_size < VKI_MINSIGSTKSZ) {
            return VG_(mk_SysRes_Error)( VKI_ENOMEM );
         }

	 VG_(threads)[tid].altstack.ss_sp    = ss->ss_sp;
	 VG_(threads)[tid].altstack.ss_size  = ss->ss_size;
	 VG_(threads)[tid].altstack.ss_flags = 0;
      }
   }
   return VG_(mk_SysRes_Success)( 0 );
}


SysRes VG_(do_sys_sigaction) ( Int signo, 
                               const struct vki_sigaction *new_act, 
                               struct vki_sigaction *old_act )
{
   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugExtraMsg, 
         "sys_sigaction: sigNo %d, "
         "new %#lx, old %#lx, new flags 0x%llx",
         signo, (UWord)new_act, (UWord)old_act,
         (ULong)(new_act ? new_act->sa_flags : 0) );

   /* Rule out various error conditions.  The aim is to ensure that if
      when the call is passed to the kernel it will definitely
      succeed. */

   /* Reject out-of-range signal numbers. */
   if (signo < 1 || signo > VG_(max_signal)) goto bad_signo;

   /* don't let them use our signals */
   if ( (signo > VG_SIGVGRTUSERMAX)
	&& new_act
	&& !(new_act->ksa_handler == VKI_SIG_DFL 
             || new_act->ksa_handler == VKI_SIG_IGN) )
      goto bad_signo_reserved;

   /* Reject attempts to set a handler (or set ignore) for SIGKILL. */
   if ( (signo == VKI_SIGKILL || signo == VKI_SIGSTOP)
       && new_act
       && new_act->ksa_handler != VKI_SIG_DFL)
      goto bad_sigkill_or_sigstop;

   /* If the client supplied non-NULL old_act, copy the relevant SCSS
      entry into it. */
   if (old_act) {
      old_act->ksa_handler = scss.scss_per_sig[signo].scss_handler;
      old_act->sa_flags    = scss.scss_per_sig[signo].scss_flags;
      old_act->sa_mask     = scss.scss_per_sig[signo].scss_mask;
#     if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
      old_act->sa_restorer = scss.scss_per_sig[signo].scss_restorer;
#     endif
   }

   /* And now copy new SCSS entry from new_act. */
   if (new_act) {
      scss.scss_per_sig[signo].scss_handler  = new_act->ksa_handler;
      scss.scss_per_sig[signo].scss_flags    = new_act->sa_flags;
      scss.scss_per_sig[signo].scss_mask     = new_act->sa_mask;

      scss.scss_per_sig[signo].scss_restorer = 0;
#     if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
      scss.scss_per_sig[signo].scss_restorer = new_act->sa_restorer;
#     endif

      VG_(sigdelset)(&scss.scss_per_sig[signo].scss_mask, VKI_SIGKILL);
      VG_(sigdelset)(&scss.scss_per_sig[signo].scss_mask, VKI_SIGSTOP);
   }

   /* All happy bunnies ... */
   if (new_act) {
      handle_SCSS_change( False /* lazy update */ );
   }
   return VG_(mk_SysRes_Success)( 0 );

  bad_signo:
   if (VG_(showing_core_errors)() && !VG_(clo_xml)) {
      VG_(message)(Vg_UserMsg,
                   "Warning: bad signal number %d in sigaction()", 
                   signo);
   }
   return VG_(mk_SysRes_Error)( VKI_EINVAL );

  bad_signo_reserved:
   if (VG_(showing_core_errors)() && !VG_(clo_xml)) {
      VG_(message)(Vg_UserMsg,
		   "Warning: ignored attempt to set %s handler in sigaction();",
		   signame(signo));
      VG_(message)(Vg_UserMsg,
		   "         the %s signal is used internally by Valgrind", 
		   signame(signo));
   }
   return VG_(mk_SysRes_Error)( VKI_EINVAL );

  bad_sigkill_or_sigstop:
   if (VG_(showing_core_errors)() && !VG_(clo_xml)) {
      VG_(message)(Vg_UserMsg,
		   "Warning: ignored attempt to set %s handler in sigaction();",
		   signame(signo));
      VG_(message)(Vg_UserMsg,
		   "         the %s signal is uncatchable", 
		   signame(signo));
   }
   return VG_(mk_SysRes_Error)( VKI_EINVAL );
}


static
void do_sigprocmask_bitops ( Int vki_how, 
			     vki_sigset_t* orig_set,
			     vki_sigset_t* modifier )
{
   switch (vki_how) {
      case VKI_SIG_BLOCK: 
         VG_(sigaddset_from_set)( orig_set, modifier );
         break;
      case VKI_SIG_UNBLOCK:
         VG_(sigdelset_from_set)( orig_set, modifier );
         break;
      case VKI_SIG_SETMASK:
         *orig_set = *modifier;
         break;
      default:
         VG_(core_panic)("do_sigprocmask_bitops");
	 break;
   }
}

static
const Char *format_sigset ( const vki_sigset_t* set )
{
   static Char buf[128];
   int w;

   VG_(strcpy)(buf, "");

   for (w = _VKI_NSIG_WORDS - 1; w >= 0; w--)
   {
#     if _VKI_NSIG_BPW == 32
      VG_(sprintf)(buf + VG_(strlen)(buf), "%08llx",
                   set ? (ULong)set->sig[w] : 0);
#     elif _VKI_NSIG_BPW == 64
      VG_(sprintf)(buf + VG_(strlen)(buf), "%16llx",
                   set ? (ULong)set->sig[w] : 0);
#     else
#       error "Unsupported value for _VKI_NSIG_BPW"
#     endif
   }

   return buf;
}

/* 
   This updates the thread's signal mask.  There's no such thing as a
   process-wide signal mask.

   Note that the thread signal masks are an implicit part of SCSS,
   which is why this routine is allowed to mess with them.  
*/
static
void do_setmask ( ThreadId tid,
                  Int how,
                  vki_sigset_t* newset,
		  vki_sigset_t* oldset )
{
   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugExtraMsg, 
		   "do_setmask: tid = %d how = %d (%s), set = %p %s", 
		   tid, how,
		   how==VKI_SIG_BLOCK ? "SIG_BLOCK" : (
		      how==VKI_SIG_UNBLOCK ? "SIG_UNBLOCK" : (
			 how==VKI_SIG_SETMASK ? "SIG_SETMASK" : "???")),
		   newset, format_sigset(newset));

   /* Just do this thread. */
   vg_assert(VG_(is_valid_tid)(tid));
   if (oldset) {
      *oldset = VG_(threads)[tid].sig_mask;
      if (VG_(clo_trace_signals))
	      VG_(message)(Vg_DebugExtraMsg, 
			   "\toldset=%p %s",
			   oldset, format_sigset(oldset));
   }
   if (newset) {
      do_sigprocmask_bitops (how, &VG_(threads)[tid].sig_mask, newset );
      VG_(sigdelset)(&VG_(threads)[tid].sig_mask, VKI_SIGKILL);
      VG_(sigdelset)(&VG_(threads)[tid].sig_mask, VKI_SIGSTOP);
      VG_(threads)[tid].tmp_sig_mask = VG_(threads)[tid].sig_mask;
   }
}


SysRes VG_(do_sys_sigprocmask) ( ThreadId tid,
                                 Int how, 
                                 vki_sigset_t* set,
                                 vki_sigset_t* oldset )
{
   switch(how) {
   case VKI_SIG_BLOCK:
   case VKI_SIG_UNBLOCK:
   case VKI_SIG_SETMASK:
      vg_assert(VG_(is_valid_tid)(tid));
      do_setmask ( tid, how, set, oldset );
      return VG_(mk_SysRes_Success)( 0 );

   default:
      VG_(message)(Vg_DebugMsg, 
                  "sigprocmask: unknown 'how' field %d", how);
      return VG_(mk_SysRes_Error)( VKI_EINVAL );
   }
}


/* ---------------------------------------------------------------------
   LOW LEVEL STUFF TO DO WITH SIGNALS: IMPLEMENTATION
   ------------------------------------------------------------------ */

/* ---------------------------------------------------------------------
   Handy utilities to block/restore all host signals.
   ------------------------------------------------------------------ */

/* Block all host signals, dumping the old mask in *saved_mask. */
static void block_all_host_signals ( /* OUT */ vki_sigset_t* saved_mask )
{
   Int           ret;
   vki_sigset_t block_procmask;
   VG_(sigfillset)(&block_procmask);
   ret = VG_(sigprocmask)
            (VKI_SIG_SETMASK, &block_procmask, saved_mask);
   vg_assert(ret == 0);
}

/* Restore the blocking mask using the supplied saved one. */
static void restore_all_host_signals ( /* IN */ vki_sigset_t* saved_mask )
{
   Int ret;
   ret = VG_(sigprocmask)(VKI_SIG_SETMASK, saved_mask, NULL);
   vg_assert(ret == 0);
}

void VG_(clear_out_queued_signals)( ThreadId tid, vki_sigset_t* saved_mask )
{
   block_all_host_signals(saved_mask);
   if (VG_(threads)[tid].sig_queue != NULL) {
      VG_(arena_free)(VG_AR_CORE, VG_(threads)[tid].sig_queue);
      VG_(threads)[tid].sig_queue = NULL;
   }
   restore_all_host_signals(saved_mask);
}

/* ---------------------------------------------------------------------
   The signal simulation proper.  A simplified version of what the 
   Linux kernel does.
   ------------------------------------------------------------------ */

/* Set up a stack frame (VgSigContext) for the client's signal
   handler. */
static
void push_signal_frame ( ThreadId tid, const vki_siginfo_t *siginfo, const struct vki_ucontext *uc )
{
   Addr         esp_top_of_frame;
   ThreadState* tst;
   Int		sigNo = siginfo->si_signo;

   vg_assert(sigNo >= 1 && sigNo <= VG_(max_signal));
   vg_assert(VG_(is_valid_tid)(tid));
   tst = & VG_(threads)[tid];

   if (VG_(clo_trace_signals)) {
      VG_(message)(Vg_DebugMsg, 
         "push_signal_frame (thread %d): signal %d", tid, sigNo);
      VG_(get_and_pp_StackTrace)(tid, 10);
   }

   if (/* this signal asked to run on an alt stack */
       (scss.scss_per_sig[sigNo].scss_flags & VKI_SA_ONSTACK )
       && /* there is a defined and enabled alt stack, which we're not
             already using.  Logic from get_sigframe in
             arch/i386/kernel/signal.c. */
          sas_ss_flags(tid, VG_(get_SP)(tid)) == 0
      ) {
      esp_top_of_frame 
         = (Addr)(tst->altstack.ss_sp) + tst->altstack.ss_size;
      if (VG_(clo_trace_signals))
         VG_(message)(Vg_DebugMsg,
		      "delivering signal %d (%s) to thread %d: on ALT STACK (%p-%p; %ld bytes)",
		      sigNo, signame(sigNo), tid, 
		      tst->altstack.ss_sp,
		      (UChar *)tst->altstack.ss_sp + tst->altstack.ss_size,
		      (unsigned long)tst->altstack.ss_size );

      /* Signal delivery to tools */
      VG_TRACK( pre_deliver_signal, tid, sigNo, /*alt_stack*/True );
      
   } else {
      esp_top_of_frame = VG_(get_SP)(tid) - VG_STACK_REDZONE_SZB;

      /* Signal delivery to tools */
      VG_TRACK( pre_deliver_signal, tid, sigNo, /*alt_stack*/False );
   }

   vg_assert(scss.scss_per_sig[sigNo].scss_handler != VKI_SIG_IGN);
   vg_assert(scss.scss_per_sig[sigNo].scss_handler != VKI_SIG_DFL);

   /* This may fail if the client stack is busted; if that happens,
      the whole process will exit rather than simply calling the
      signal handler. */
   VG_(sigframe_create) (tid, esp_top_of_frame, siginfo, uc,
                         scss.scss_per_sig[sigNo].scss_handler,
                         scss.scss_per_sig[sigNo].scss_flags,
                         &tst->sig_mask,
                         scss.scss_per_sig[sigNo].scss_restorer);
}


static const Char *signame(Int sigNo)
{
   static Char buf[10];

   switch(sigNo) {
      case VKI_SIGHUP:    return "SIGHUP";
      case VKI_SIGINT:    return "SIGINT";
      case VKI_SIGQUIT:   return "SIGQUIT";
      case VKI_SIGILL:    return "SIGILL";
      case VKI_SIGTRAP:   return "SIGTRAP";
      case VKI_SIGABRT:   return "SIGABRT";
      case VKI_SIGBUS:    return "SIGBUS";
      case VKI_SIGFPE:    return "SIGFPE";
      case VKI_SIGKILL:   return "SIGKILL";
      case VKI_SIGUSR1:   return "SIGUSR1";
      case VKI_SIGUSR2:   return "SIGUSR2";
      case VKI_SIGSEGV:   return "SIGSEGV";
      case VKI_SIGPIPE:   return "SIGPIPE";
      case VKI_SIGALRM:   return "SIGALRM";
      case VKI_SIGTERM:   return "SIGTERM";
#     if defined(VKI_SIGSTKFLT)
      case VKI_SIGSTKFLT: return "SIGSTKFLT";
#     endif
      case VKI_SIGCHLD:   return "SIGCHLD";
      case VKI_SIGCONT:   return "SIGCONT";
      case VKI_SIGSTOP:   return "SIGSTOP";
      case VKI_SIGTSTP:   return "SIGTSTP";
      case VKI_SIGTTIN:   return "SIGTTIN";
      case VKI_SIGTTOU:   return "SIGTTOU";
      case VKI_SIGURG:    return "SIGURG";
      case VKI_SIGXCPU:   return "SIGXCPU";
      case VKI_SIGXFSZ:   return "SIGXFSZ";
      case VKI_SIGVTALRM: return "SIGVTALRM";
      case VKI_SIGPROF:   return "SIGPROF";
      case VKI_SIGWINCH:  return "SIGWINCH";
      case VKI_SIGIO:     return "SIGIO";
      case VKI_SIGPWR:    return "SIGPWR";
#     if defined(VKI_SIGUNUSED)
      case VKI_SIGUNUSED: return "SIGUNUSED";
#     endif

   case VKI_SIGRTMIN ... VKI_SIGRTMAX:
      VG_(sprintf)(buf, "SIGRT%d", sigNo-VKI_SIGRTMIN);
      return buf;

   default:
      VG_(sprintf)(buf, "SIG%d", sigNo);
      return buf;
   }
}

/* Hit ourselves with a signal using the default handler */
void VG_(kill_self)(Int sigNo)
{
   vki_sigset_t	        mask, origmask;
   struct vki_sigaction sa, origsa;   

   sa.ksa_handler = VKI_SIG_DFL;
   sa.sa_flags = 0;
#  if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
   sa.sa_restorer = 0;
#  endif
   VG_(sigemptyset)(&sa.sa_mask);
      
   VG_(sigaction)(sigNo, &sa, &origsa);

   VG_(sigemptyset)(&mask);
   VG_(sigaddset)(&mask, sigNo);
   VG_(sigprocmask)(VKI_SIG_UNBLOCK, &mask, &origmask);

   VG_(kill)(VG_(getpid)(), sigNo);

   VG_(sigaction)(sigNo, &origsa, NULL);
   VG_(sigprocmask)(VKI_SIG_SETMASK, &origmask, NULL);
}

/* 
   Perform the default action of a signal.  If the signal is fatal, it
   marks all threads as needing to exit, but it doesn't actually kill
   the process or thread.

   If we're not being quiet, then print out some more detail about
   fatal signals (esp. core dumping signals).
 */
static void default_action(const vki_siginfo_t *info, ThreadId tid)
{
   Int  sigNo     = info->si_signo;
   Bool terminate = False;	/* kills process         */
   Bool core      = False;	/* kills process w/ core */
   struct vki_rlimit corelim;
   Bool could_core;

   vg_assert(VG_(is_running_thread)(tid));
   
   switch(sigNo) {
   case VKI_SIGQUIT:	/* core */
   case VKI_SIGILL:	/* core */
   case VKI_SIGABRT:	/* core */
   case VKI_SIGFPE:	/* core */
   case VKI_SIGSEGV:	/* core */
   case VKI_SIGBUS:	/* core */
   case VKI_SIGTRAP:	/* core */
   case VKI_SIGXCPU:	/* core */
   case VKI_SIGXFSZ:	/* core */
      terminate = True;
      core = True;
      break;

   case VKI_SIGHUP:	/* term */
   case VKI_SIGINT:	/* term */
   case VKI_SIGKILL:	/* term - we won't see this */
   case VKI_SIGPIPE:	/* term */
   case VKI_SIGALRM:	/* term */
   case VKI_SIGTERM:	/* term */
   case VKI_SIGUSR1:	/* term */
   case VKI_SIGUSR2:	/* term */
   case VKI_SIGIO:	/* term */
   case VKI_SIGPWR:	/* term */
   case VKI_SIGSYS:	/* term */
   case VKI_SIGPROF:	/* term */
   case VKI_SIGVTALRM:	/* term */
   case VKI_SIGRTMIN ... VKI_SIGRTMAX: /* term */
      terminate = True;
      break;
   }

   vg_assert(!core || (core && terminate));

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugMsg, "delivering %d (code %d) to default handler; action: %s%s",
		   sigNo, info->si_code, terminate ? "terminate" : "ignore", core ? "+core" : "");

   if (!terminate)
      return;			/* nothing to do */

   could_core = core;

   if (core) {
      /* If they set the core-size limit to zero, don't generate a
	 core file */
	 
      VG_(getrlimit)(VKI_RLIMIT_CORE, &corelim);

      if (corelim.rlim_cur == 0)
	 core = False;
   }

   if ( (VG_(clo_verbosity) > 1 || (could_core && info->si_code > VKI_SI_USER)) 
        && !VG_(clo_xml) ) {
      VG_(message)(Vg_UserMsg, "");
      VG_(message)(Vg_UserMsg, 
                   "Process terminating with default action of signal %d (%s)%s", 
		   sigNo, signame(sigNo), core ? ": dumping core" : "");

      /* Be helpful - decode some more details about this fault */
      if (info->si_code > VKI_SI_USER) {
	 const Char *event = NULL;
	 Bool haveaddr = True;

	 switch(sigNo) {
	 case VKI_SIGSEGV:
	    switch(info->si_code) {
	    case VKI_SEGV_MAPERR: event = "Access not within mapped region"; break;
	    case VKI_SEGV_ACCERR: event = "Bad permissions for mapped region"; break;
	    case 128:
	       /* General Protection Fault: The CPU/kernel
		  isn't telling us anything useful, but this
		  is commonly the result of exceeding a
		  segment limit. */
	       event = "General Protection Fault"; 
	       haveaddr = False;
	       break;
	    }
#if 0
            {
              HChar buf[110];
              VG_(am_show_nsegments)(0,"post segfault");
              VG_(sprintf)(buf, "/bin/cat /proc/%d/maps", VG_(getpid)());
              VG_(system)(buf);
            }
#endif
	    break;

	 case VKI_SIGILL:
	    switch(info->si_code) {
	    case VKI_ILL_ILLOPC: event = "Illegal opcode"; break;
	    case VKI_ILL_ILLOPN: event = "Illegal operand"; break;
	    case VKI_ILL_ILLADR: event = "Illegal addressing mode"; break;
	    case VKI_ILL_ILLTRP: event = "Illegal trap"; break;
	    case VKI_ILL_PRVOPC: event = "Privileged opcode"; break;
	    case VKI_ILL_PRVREG: event = "Privileged register"; break;
	    case VKI_ILL_COPROC: event = "Coprocessor error"; break;
	    case VKI_ILL_BADSTK: event = "Internal stack error"; break;
	    }
	    break;

	 case VKI_SIGFPE:
	    switch (info->si_code) {
	    case VKI_FPE_INTDIV: event = "Integer divide by zero"; break;
	    case VKI_FPE_INTOVF: event = "Integer overflow"; break;
	    case VKI_FPE_FLTDIV: event = "FP divide by zero"; break;
	    case VKI_FPE_FLTOVF: event = "FP overflow"; break;
	    case VKI_FPE_FLTUND: event = "FP underflow"; break;
	    case VKI_FPE_FLTRES: event = "FP inexact"; break;
	    case VKI_FPE_FLTINV: event = "FP invalid operation"; break;
	    case VKI_FPE_FLTSUB: event = "FP subscript out of range"; break;
	    }
	    break;

	 case VKI_SIGBUS:
	    switch (info->si_code) {
	    case VKI_BUS_ADRALN: event = "Invalid address alignment"; break;
	    case VKI_BUS_ADRERR: event = "Non-existent physical address"; break;
	    case VKI_BUS_OBJERR: event = "Hardware error"; break;
	    }
	    break;
	 } /* switch (sigNo) */

	 if (event != NULL) {
	    if (haveaddr)
	       VG_(message)(Vg_UserMsg, " %s at address %p", 
			    event, info->VKI_SIGINFO_si_addr);
	    else
	       VG_(message)(Vg_UserMsg, " %s", event);
	 }
      }
      /* Print a stack trace.  Be cautious if the thread's SP is in an
         obviously stupid place (not mapped readable) that would
         likely cause a segfault. */
      if (VG_(is_valid_tid)(tid)) {
         ExeContext* ec = VG_(am_is_valid_for_client)
                             (VG_(get_SP)(tid), sizeof(Addr), VKI_PROT_READ)
                        ? VG_(record_ExeContext)( tid, 0/*first_ip_delta*/ )
                      : VG_(record_depth_1_ExeContext)( tid );
         vg_assert(ec);
         VG_(pp_ExeContext)( ec );
      }
      if (sigNo == VKI_SIGSEGV 
          && info && info->si_code > VKI_SI_USER 
          && info->si_code == VKI_SEGV_MAPERR) {
         VG_(message)(Vg_UserMsg, " If you believe this happened as a "
                                  "result of a stack overflow in your");
         VG_(message)(Vg_UserMsg, " program's main thread (unlikely but"
                                  " possible), you can try to increase");
         VG_(message)(Vg_UserMsg, " the size of the main thread stack"
                                  " using the --main-stacksize= flag.");
         // FIXME: assumes main ThreadId == 1
         if (VG_(is_valid_tid)(1)) {
            VG_(message)(Vg_UserMsg, 
               " The main thread stack size used in this run was %d.",
               (Int)VG_(threads)[1].client_stack_szB);
         }
      }
   }

   if (VG_(is_action_requested)( "Attach to debugger", & VG_(clo_db_attach) )) {
      VG_(start_debugger)( tid );
   }

   if (core) {
      const static struct vki_rlimit zero = { 0, 0 };

      VG_(make_coredump)(tid, info, corelim.rlim_cur);

      /* Make sure we don't get a confusing kernel-generated
	 coredump when we finally exit */
      VG_(setrlimit)(VKI_RLIMIT_CORE, &zero);
   }

   /* stash fatal signal in main thread */
   // what's this for?
   //VG_(threads)[VG_(master_tid)].os_state.fatalsig = sigNo;

   /* everyone dies */
   VG_(nuke_all_threads_except)(tid, VgSrc_FatalSig);
   VG_(threads)[tid].exitreason = VgSrc_FatalSig;
   VG_(threads)[tid].os_state.fatalsig = sigNo;
}

/* 
   This does the business of delivering a signal to a thread.  It may
   be called from either a real signal handler, or from normal code to
   cause the thread to enter the signal handler.

   This updates the thread state, but it does not set it to be
   Runnable.
*/
static void deliver_signal ( ThreadId tid, const vki_siginfo_t *info, const struct vki_ucontext *uc )
{
   Int			sigNo = info->si_signo;
   SCSS_Per_Signal	*handler = &scss.scss_per_sig[sigNo];
   void			*handler_fn;
   ThreadState		*tst = VG_(get_ThreadState)(tid);

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugMsg,"delivering signal %d (%s):%d to thread %d", 
		   sigNo, signame(sigNo), info->si_code, tid );

   if (sigNo == VG_SIGVGKILL) {
      /* If this is a SIGVGKILL, we're expecting it to interrupt any
	 blocked syscall.  It doesn't matter whether the VCPU state is
	 set to restart or not, because we don't expect it will
	 execute any more client instructions. */
      vg_assert(VG_(is_exiting)(tid));
      return;
   }

   /* If the client specifies SIG_IGN, treat it as SIG_DFL.

      If deliver_signal() is being called on a thread, we want
      the signal to get through no matter what; if they're ignoring
      it, then we do this override (this is so we can send it SIGSEGV,
      etc). */
   handler_fn = handler->scss_handler;
   if (handler_fn == VKI_SIG_IGN) 
      handler_fn = VKI_SIG_DFL;

   vg_assert(handler_fn != VKI_SIG_IGN);

   if (handler_fn == VKI_SIG_DFL) {
      default_action(info, tid);
   } else {
      /* Create a signal delivery frame, and set the client's %ESP and
	 %EIP so that when execution continues, we will enter the
	 signal handler with the frame on top of the client's stack,
	 as it expects.

	 Signal delivery can fail if the client stack is too small or
	 missing, and we can't push the frame.  If that happens,
	 push_signal_frame will cause the whole process to exit when
	 we next hit the scheduler.
      */
      vg_assert(VG_(is_valid_tid)(tid));

      push_signal_frame ( tid, info, uc );

      if (handler->scss_flags & VKI_SA_ONESHOT) {
	 /* Do the ONESHOT thing. */
	 handler->scss_handler = VKI_SIG_DFL;

	 handle_SCSS_change( False /* lazy update */ );
      }

      /* At this point:
	 tst->sig_mask is the current signal mask
	 tst->tmp_sig_mask is the same as sig_mask, unless we're in sigsuspend
	 handler->scss_mask is the mask set by the handler

	 Handler gets a mask of tmp_sig_mask|handler_mask|signo
       */
      tst->sig_mask = tst->tmp_sig_mask;
      if (!(handler->scss_flags & VKI_SA_NOMASK)) {
	 VG_(sigaddset_from_set)(&tst->sig_mask, &handler->scss_mask);
	 VG_(sigaddset)(&tst->sig_mask, sigNo);

	 tst->tmp_sig_mask = tst->sig_mask;
      }
   }

   /* Thread state is ready to go - just add Runnable */
}

static void resume_scheduler(ThreadId tid)
{
   ThreadState *tst = VG_(get_ThreadState)(tid);

   vg_assert(tst->os_state.lwpid == VG_(gettid)());

   if (tst->sched_jmpbuf_valid) {
      /* Can't continue; must longjmp back to the scheduler and thus
         enter the sighandler immediately. */
      __builtin_longjmp(tst->sched_jmpbuf, True);
   }
}

static void synth_fault_common(ThreadId tid, Addr addr, Int si_code)
{
   vki_siginfo_t info;

   vg_assert(VG_(threads)[tid].status == VgTs_Runnable);

   info.si_signo = VKI_SIGSEGV;
   info.si_code = si_code;
   info.VKI_SIGINFO_si_addr = (void*)addr;

   /* If they're trying to block the signal, force it to be delivered */
   if (VG_(sigismember)(&VG_(threads)[tid].sig_mask, VKI_SIGSEGV))
      VG_(set_default_handler)(VKI_SIGSEGV);

   deliver_signal(tid, &info, NULL);
}

// Synthesize a fault where the address is OK, but the page
// permissions are bad.
void VG_(synth_fault_perms)(ThreadId tid, Addr addr)
{
   synth_fault_common(tid, addr, 2);
}

// Synthesize a fault where the address there's nothing mapped at the address.
void VG_(synth_fault_mapping)(ThreadId tid, Addr addr)
{
   synth_fault_common(tid, addr, 1);
}

// Synthesize a misc memory fault.
void VG_(synth_fault)(ThreadId tid)
{
   synth_fault_common(tid, 0, 0x80);
}

// Synthesise a SIGILL.
void VG_(synth_sigill)(ThreadId tid, Addr addr)
{
   vki_siginfo_t info;

   vg_assert(VG_(threads)[tid].status == VgTs_Runnable);

   info.si_signo = VKI_SIGILL;
   info.si_code  = VKI_ILL_ILLOPC; /* jrs: no idea what this should be */
   info.VKI_SIGINFO_si_addr = (void*)addr;

   resume_scheduler(tid);
   deliver_signal(tid, &info, NULL);
}

// Synthesise a SIGTRAP.
void VG_(synth_sigtrap)(ThreadId tid)
{
   vki_siginfo_t info;
   struct vki_ucontext uc;

   vg_assert(VG_(threads)[tid].status == VgTs_Runnable);

   info.si_signo = VKI_SIGTRAP;
   info.si_code = VKI_TRAP_BRKPT; /* tjh: only ever called for a brkpt ins */
#if defined(VGA_x86) || defined(VGA_amd64)
   uc.uc_mcontext.trapno = 3;     /* tjh: this is the x86 trap number
                                          for a breakpoint trap... */
   uc.uc_mcontext.err = 0;        /* tjh: no error code for x86
                                          breakpoint trap... */
#endif

   resume_scheduler(tid);
   deliver_signal(tid, &info, &uc);
}

/* Make a signal pending for a thread, for later delivery.
   VG_(poll_signals) will arrange for it to be delivered at the right
   time. 

   tid==0 means add it to the process-wide queue, and not sent it to a
   specific thread.
*/
static 
void queue_signal(ThreadId tid, const vki_siginfo_t *si)
{
   ThreadState *tst;
   SigQueue *sq;
   vki_sigset_t savedmask;

   tst = VG_(get_ThreadState)(tid);

   /* Protect the signal queue against async deliveries */
   block_all_host_signals(&savedmask);

   if (tst->sig_queue == NULL) {
      tst->sig_queue = VG_(arena_malloc)(VG_AR_CORE, "signals.qs.1",
                                         sizeof(*tst->sig_queue));
      VG_(memset)(tst->sig_queue, 0, sizeof(*tst->sig_queue));
   }
   sq = tst->sig_queue;

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugMsg, "Queueing signal %d (idx %d) to thread %d",
		   si->si_signo, sq->next, tid);

   /* Add signal to the queue.  If the queue gets overrun, then old
      queued signals may get lost. 

      XXX We should also keep a sigset of pending signals, so that at
      least a non-siginfo signal gets deliviered.
   */
   if (sq->sigs[sq->next].si_signo != 0)
      VG_(message)(Vg_UserMsg, "Signal %d being dropped from thread %d's queue",
		   sq->sigs[sq->next].si_signo, tid);

   sq->sigs[sq->next] = *si;
   sq->next = (sq->next+1) % N_QUEUED_SIGNALS;

   restore_all_host_signals(&savedmask);
}

/*
   Returns the next queued signal for thread tid which is in "set".
   tid==0 means process-wide signal.  Set si_signo to 0 when the
   signal has been delivered.

   Must be called with all signals blocked, to protect against async
   deliveries.
*/
static vki_siginfo_t *next_queued(ThreadId tid, const vki_sigset_t *set)
{
   ThreadState *tst = VG_(get_ThreadState)(tid);
   SigQueue *sq;
   Int idx;
   vki_siginfo_t *ret = NULL;

   sq = tst->sig_queue;
   if (sq == NULL)
      goto out;
   
   idx = sq->next;
   do {
      if (0)
	 VG_(printf)("idx=%d si_signo=%d inset=%d\n", idx,
		     sq->sigs[idx].si_signo, VG_(sigismember)(set, sq->sigs[idx].si_signo));

      if (sq->sigs[idx].si_signo != 0 && VG_(sigismember)(set, sq->sigs[idx].si_signo)) {
	 if (VG_(clo_trace_signals))
	    VG_(message)(Vg_DebugMsg, "Returning queued signal %d (idx %d) for thread %d",
			 sq->sigs[idx].si_signo, idx, tid);
	 ret = &sq->sigs[idx];
	 goto out;
      }

      idx = (idx + 1) % N_QUEUED_SIGNALS;
   } while(idx != sq->next);
  out:   
   return ret;
}

/* 
   Receive an async signal from the kernel.

   This should only happen when the thread is blocked in a syscall,
   since that's the only time this set of signals is unblocked.
*/
static 
void async_signalhandler ( Int sigNo, vki_siginfo_t *info, struct vki_ucontext *uc )
{
   ThreadId tid = VG_(lwpid_to_vgtid)(VG_(gettid)());
   ThreadState *tst = VG_(get_ThreadState)(tid);

#ifdef VGO_linux
   /* The linux kernel uses the top 16 bits of si_code for it's own
      use and only exports the bottom 16 bits to user space - at least
      that is the theory, but it turns out that there are some kernels
      around that forget to mask out the top 16 bits so we do it here.

      The kernel treats the bottom 16 bits as signed and (when it does
      mask them off) sign extends them when exporting to user space so
      we do the same thing here. */
   info->si_code = (Short)info->si_code;
#endif

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugMsg, "Async handler got signal %d for tid %d info %d",
		   sigNo, tid, info->si_code);

   vg_assert(tst->status == VgTs_WaitSys);

   /* The thread isn't currently running, make it so before going on */
   VG_(acquire_BigLock)(tid, "async_signalhandler");

   /* Update thread state properly */
   VG_(fixup_guest_state_after_syscall_interrupted)(
      tid, 
      VG_UCONTEXT_INSTR_PTR(uc), 
      VG_UCONTEXT_SYSCALL_NUM(uc), 
      VG_UCONTEXT_SYSCALL_SYSRES(uc),  
      !!(scss.scss_per_sig[sigNo].scss_flags & VKI_SA_RESTART)
   );

   /* Set up the thread's state to deliver a signal */
   if (!is_sig_ign(info->si_signo))
      deliver_signal(tid, info, uc);

   /* longjmp back to the thread's main loop to start executing the
      handler. */
   resume_scheduler(tid);

   VG_(core_panic)("async_signalhandler: got unexpected signal while outside of scheduler");
}

/* Extend the stack to cover addr.  maxsize is the limit the stack can grow to.

   Returns True on success, False on failure.

   Succeeds without doing anything if addr is already within a segment.

   Failure could be caused by:
   - addr not below a growable segment
   - new stack size would exceed maxsize
   - mmap failed for some other reason
 */
Bool VG_(extend_stack)(Addr addr, UInt maxsize)
{
   SizeT udelta;

   /* Find the next Segment above addr */
   NSegment const* seg
      = VG_(am_find_nsegment)(addr);
   NSegment const* seg_next 
      = seg ? VG_(am_next_nsegment)( (NSegment*)seg, True/*fwds*/ )
            : NULL;

   if (seg && seg->kind == SkAnonC)
      /* addr is already mapped.  Nothing to do. */
      return True;

   /* Check that the requested new base is in a shrink-down
      reservation section which abuts an anonymous mapping that
      belongs to the client. */
   if ( ! (seg
           && seg->kind == SkResvn
           && seg->smode == SmUpper
           && seg_next
           && seg_next->kind == SkAnonC
           && seg->end+1 == seg_next->start))
      return False;

   udelta = VG_PGROUNDUP(seg_next->start - addr);
   VG_(debugLog)(1, "signals", 
                    "extending a stack base 0x%llx down by %lld\n",
                    (ULong)seg_next->start, (ULong)udelta);
   if (! VG_(am_extend_into_adjacent_reservation_client)
            ( (NSegment*)seg_next, -(SSizeT)udelta )) {
      VG_(debugLog)(1, "signals", "extending a stack base: FAILED\n");
      return False;
   }

   /* When we change the main stack, we have to let the stack handling
      code know about it. */
   VG_(change_stack)(VG_(clstk_id), addr, VG_(clstk_end));

   if (VG_(clo_sanity_level) > 2)
      VG_(sanity_check_general)(False);

   return True;
}

static void (*fault_catcher)(Int sig, Addr addr) = NULL;

void VG_(set_fault_catcher)(void (*catcher)(Int, Addr))
{
   if (0)
      VG_(debugLog)(0, "signals", "set fault catcher to %p\n", catcher);
   vg_assert2(NULL == catcher || NULL == fault_catcher,
              "Fault catcher is already registered");

   fault_catcher = catcher;
}


/* 
   Receive a sync signal from the host. 
*/
static
void sync_signalhandler ( Int sigNo, vki_siginfo_t *info, struct vki_ucontext *uc )
{
   ThreadId tid = VG_(lwpid_to_vgtid)(VG_(gettid)());

   vg_assert(info != NULL);
   vg_assert(info->si_signo == sigNo);
   vg_assert(sigNo == VKI_SIGSEGV ||
	     sigNo == VKI_SIGBUS  ||
	     sigNo == VKI_SIGFPE  ||
	     sigNo == VKI_SIGILL  ||
	     sigNo == VKI_SIGTRAP);

#ifdef VGO_linux
   /* The linux kernel uses the top 16 bits of si_code for it's own
      use and only exports the bottom 16 bits to user space - at least
      that is the theory, but it turns out that there are some kernels
      around that forget to mask out the top 16 bits so we do it here.

      The kernel treats the bottom 16 bits as signed and (when it does
      mask them off) sign extends them when exporting to user space so
      we do the same thing here. */
   info->si_code = (Short)info->si_code;
#endif

   if (info->si_code <= VKI_SI_USER) {
      /* If some user-process sent us one of these signals (ie,
	 they're not the result of a faulting instruction), then treat
	 it as an async signal.  This is tricky because we could get
	 this almost anywhere:
	  - while generated client code
	    Action: queue signal and return
	  - while running Valgrind code
	    Action: queue signal and return
	  - while blocked in a syscall
	    Action: make thread runnable, queue signal, resume scheduler
      */
      if (VG_(threads)[tid].status == VgTs_WaitSys) {
	 /* Since this signal interrupted a syscall, it means the
	    client's signal mask was applied, so we can't get here
	    unless the client wants this signal right now.  This means
	    we can simply use the async_signalhandler. */
	 async_signalhandler(sigNo, info, uc);
	 VG_(core_panic)("async_signalhandler returned!?\n");
      }

      if (info->VKI_SIGINFO_si_pid == 0) {
	 /* There's a per-user limit of pending siginfo signals.  If
	    you exceed this, by having more than that number of
	    pending signals with siginfo, then new signals are
	    delivered without siginfo.  This condition can be caused
	    by any unrelated program you're running at the same time
	    as Valgrind, if it has a large number of pending siginfo
	    signals which it isn't taking delivery of.

	    Since we depend on siginfo to work out why we were sent a
	    signal and what we should do about it, we really can't
	    continue unless we get it. */
	 VG_(message)(Vg_UserMsg, "Signal %d (%s) appears to have lost its siginfo; I can't go on.",
		      sigNo, signame(sigNo));
	 VG_(message)(Vg_UserMsg, "  This may be because one of your programs has consumed your");
	 VG_(message)(Vg_UserMsg, "  ration of siginfo structures.");
         VG_(printf)(
"  For more information, see:\n"
"    http://kerneltrap.org/mailarchive/1/message/25599/thread\n"
"  Basically, some program on your system is building up a large queue of\n"
"  pending signals, and this causes the siginfo data for other signals to\n"
"  be dropped because it's exceeding a system limit.  However, Valgrind\n"
"  absolutely needs siginfo for SIGSEGV.  A workaround is to track down the\n"
"  offending program and avoid running it while using Valgrind, but there\n"
"  is no easy way to do this.  Apparently the problem was fixed in kernel\n"
"  2.6.12.\n");

	 /* It's a fatal signal, so we force the default handler. */
	 VG_(set_default_handler)(sigNo);
	 deliver_signal(tid, info, uc);
	 resume_scheduler(tid);
	 VG_(exit)(99);		/* If we can't resume, then just exit */
      }

      if (VG_(clo_trace_signals))
	 VG_(message)(Vg_DebugMsg, "Routing user-sent sync signal %d via queue",
		      sigNo);

      /* Since every thread has these signals unblocked, we can't rely
	 on the kernel to route them properly, so we need to queue
	 them manually. */
      if (info->si_code == VKI_SI_TKILL)
	 queue_signal(tid, info); /* directed to us specifically */
      else
	 queue_signal(0, info);	/* shared pending */

      return;
   } 

   if (VG_(clo_trace_signals)) {
      VG_(message)(Vg_DebugMsg, "signal %d arrived ... si_code=%d, "
                                "EIP=%#lx, eip=%#lx",
                   sigNo, info->si_code, VG_(get_IP)(tid), 
		   VG_UCONTEXT_INSTR_PTR(uc) );
   }
   vg_assert(sigNo >= 1 && sigNo <= VG_(max_signal));

   /* Check to see if someone is interested in faults.  The fault
      catcher should never be set whilst we're in generated code, so
      check for that.  AFAIK the only use of the catcher right now is
      memcheck's leak detector.
   */
   if (fault_catcher) {
      vg_assert(VG_(in_generated_code) == False);

      (*fault_catcher)(sigNo, (Addr)info->VKI_SIGINFO_si_addr);
      /* If the catcher returns, then it didn't handle the fault,
         so carry on panicing. */
   }

   /* Special fault-handling case. We can now get signals which can
      act upon and immediately restart the faulting instruction.
    */
   if (info->si_signo == VKI_SIGSEGV) {
      Addr fault = (Addr)info->VKI_SIGINFO_si_addr;
      Addr esp   =  VG_(get_SP)(tid);
      NSegment const* seg
         = VG_(am_find_nsegment)(fault);
      NSegment const* seg_next 
         = seg ? VG_(am_next_nsegment)( (NSegment*)seg, True/*fwds*/ )
               : NULL;

      if (VG_(clo_trace_signals)) {
	 if (seg == NULL)
	    VG_(message)(Vg_DebugMsg,
			 "SIGSEGV: si_code=%d faultaddr=%#lx tid=%d ESP=%#lx "
                         "seg=NULL",
			 info->si_code, fault, tid, esp);
	 else
	    VG_(message)(Vg_DebugMsg,
			 "SIGSEGV: si_code=%d faultaddr=%#lx tid=%d ESP=%#lx "
                          "seg=%#lx-%#lx",
			 info->si_code, fault, tid, esp, seg->start, seg->end);
      }
      if (info->si_code == VKI_SEGV_MAPERR
          && seg
          && seg->kind == SkResvn
          && seg->smode == SmUpper
          && seg_next
          && seg_next->kind == SkAnonC
          && seg->end+1 == seg_next->start
	  && fault >= (esp - VG_STACK_REDZONE_SZB)) {
	 /* If the fault address is above esp but below the current known
	    stack segment base, and it was a fault because there was
	    nothing mapped there (as opposed to a permissions fault),
	    then extend the stack segment. 
	 */
         Addr base = VG_PGROUNDDN(esp - VG_STACK_REDZONE_SZB);
	 if (VG_(extend_stack)(base, VG_(threads)[tid].client_stack_szB)) {
	    if (VG_(clo_trace_signals))
	       VG_(message)(Vg_DebugMsg, 
			    "       -> extended stack base to %#lx",
                            VG_PGROUNDDN(fault));
            return; // extension succeeded, restart host (hence guest)
                    // instruction
	 } else
	    VG_(message)(Vg_UserMsg, 
                         "Stack overflow in thread %d: can't grow stack to %#lx",
			 tid, fault);
      }
      /* Fall into normal signal handling for all other cases */
   }

   /* OK, this is a signal we really have to deal with.  If it came
      from the client's code, then we can jump back into the scheduler
      and have it delivered.  Otherwise it's a Valgrind bug. */
   {   
      ThreadState *tst 
         = VG_(get_ThreadState)(VG_(lwpid_to_vgtid)(VG_(gettid)()));

      if (VG_(sigismember)(&tst->sig_mask, sigNo)) {
	 /* signal is blocked, but they're not allowed to block faults */
	 VG_(set_default_handler)(sigNo);
      }

      if (VG_(in_generated_code)) {
	 /* Can't continue; must longjmp back to the scheduler and thus
	    enter the sighandler immediately. */
	 deliver_signal(tid, info, uc);
	 resume_scheduler(tid);
      }

      /* If resume_scheduler returns or its our fault, it means we
	 don't have longjmp set up, implying that we weren't running
	 client code, and therefore it was actually generated by
	 Valgrind internally.
       */
      VG_(message)(Vg_DebugMsg, 
		   "VALGRIND INTERNAL ERROR: Valgrind received a signal %d (%s) - exiting",
		   sigNo, signame(sigNo));

      VG_(message)(Vg_DebugMsg, 
		   "si_code=%x;  Faulting address: %p;  sp: %#lx",
		   info->si_code, info->VKI_SIGINFO_si_addr,
                   VG_UCONTEXT_STACK_PTR(uc));

      if (0)
	 VG_(kill_self)(sigNo);		/* generate a core dump */

      //if (tid == 0)            /* could happen after everyone has exited */
      //  tid = VG_(master_tid);
      vg_assert(tid != 0);

      VG_(core_panic_at)("Killed by fatal signal",
                         VG_UCONTEXT_INSTR_PTR(uc),
                         VG_UCONTEXT_STACK_PTR(uc),
                         VG_UCONTEXT_FRAME_PTR(uc),
                         VG_UCONTEXT_LINK_REG(uc));
   }
}


/* 
   Kill this thread.  Makes it leave any syscall it might be currently
   blocked in, and return to the scheduler.  This doesn't mark the thread
   as exiting; that's the caller's job.
 */
static void sigvgkill_handler(int signo, vki_siginfo_t *si, struct vki_ucontext *uc)
{
   ThreadId     tid = VG_(lwpid_to_vgtid)(VG_(gettid)());
   ThreadStatus at_signal = VG_(threads)[tid].status;

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugMsg, 
                   "sigvgkill for lwp %d tid %d", VG_(gettid)(), tid);

   VG_(acquire_BigLock)(tid, "sigvgkill_handler");

   vg_assert(signo == VG_SIGVGKILL);
   vg_assert(si->si_signo == signo);

   /* jrs 2006 August 3: the following assertion seems incorrect to
      me, and fails on AIX.  sigvgkill could be sent to a thread which
      is runnable - see VG_(nuke_all_threads_except) in the scheduler.
      Hence comment these out ..  

      vg_assert(VG_(threads)[tid].status == VgTs_WaitSys);
      VG_(post_syscall)(tid);

      and instead do:
   */
   if (at_signal == VgTs_WaitSys)
      VG_(post_syscall)(tid);
   /* jrs 2006 August 3 ends */

   resume_scheduler(tid);

   VG_(core_panic)("sigvgkill_handler couldn't return to the scheduler\n");
}

static __attribute((unused))
void pp_ksigaction ( struct vki_sigaction* sa )
{
   Int i;
   VG_(printf)("pp_ksigaction: handler %p, flags 0x%x, restorer %p\n", 
               sa->ksa_handler, 
               (UInt)sa->sa_flags, 
#              if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
                  sa->sa_restorer
#              else
                  (void*)0
#              endif
              );
   VG_(printf)("pp_ksigaction: { ");
   for (i = 1; i <= VG_(max_signal); i++)
      if (VG_(sigismember(&(sa->sa_mask),i)))
         VG_(printf)("%d ", i);
   VG_(printf)("}\n");
}

/* 
   Force signal handler to default
 */
void VG_(set_default_handler)(Int signo)
{
   struct vki_sigaction sa;   

   sa.ksa_handler = VKI_SIG_DFL;
   sa.sa_flags = 0;
#  if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
   sa.sa_restorer = 0;
#  endif
   VG_(sigemptyset)(&sa.sa_mask);
      
   VG_(do_sys_sigaction)(signo, &sa, NULL);
}

/* 
   Poll for pending signals, and set the next one up for delivery.
 */
void VG_(poll_signals)(ThreadId tid)
{
   vki_siginfo_t si, *sip;
   vki_sigset_t pollset;
   ThreadState *tst = VG_(get_ThreadState)(tid);
   Int i;
   vki_sigset_t saved_mask;

   /* look for all the signals this thread isn't blocking */
   for(i = 0; i < _VKI_NSIG_WORDS; i++)
      pollset.sig[i] = ~tst->sig_mask.sig[i];

   //VG_(printf)("tid %d pollset=%08x%08x\n", tid, pollset.sig[1], pollset.sig[0]);

   block_all_host_signals(&saved_mask); // protect signal queue

   /* First look for any queued pending signals */
   sip = next_queued(tid, &pollset); /* this thread */

   if (sip == NULL)
      sip = next_queued(0, &pollset); /* process-wide */

   /* If there was nothing queued, ask the kernel for a pending signal */
   if (sip == NULL && VG_(sigtimedwait_zero)(&pollset, &si) > 0) {
      if (VG_(clo_trace_signals))
	 VG_(message)(Vg_DebugMsg, "poll_signals: got signal %d "
                                   "for thread %d", si.si_signo, tid);
      sip = &si;
   }

   if (sip != NULL) {
      /* OK, something to do; deliver it */
      if (VG_(clo_trace_signals))
	 VG_(message)(Vg_DebugMsg, "Polling found signal %d for tid %d", 
		      sip->si_signo, tid);
      if (!is_sig_ign(sip->si_signo))
	 deliver_signal(tid, sip, NULL);
      else if (VG_(clo_trace_signals))
	 VG_(message)(Vg_DebugMsg, "   signal %d ignored", sip->si_signo);
	 
      sip->si_signo = 0;	/* remove from signal queue, if that's
				   where it came from */
   }

   restore_all_host_signals(&saved_mask);
}

/* At startup, copy the process' real signal state to the SCSS.
   Whilst doing this, block all real signals.  Then calculate SKSS and
   set the kernel to that.  Also initialise DCSS. 
*/
void VG_(sigstartup_actions) ( void )
{
   Int i, ret;
   vki_sigset_t saved_procmask;
   struct vki_sigaction sa;

   /* VG_(printf)("SIGSTARTUP\n"); */
   /* Block all signals.  saved_procmask remembers the previous mask,
      which the first thread inherits.
   */
   block_all_host_signals( &saved_procmask );

   /* Copy per-signal settings to SCSS. */
   for (i = 1; i <= _VKI_NSIG; i++) {
      /* Get the old host action */
      ret = VG_(sigaction)(i, NULL, &sa);

      if (ret != 0)
	 break;

      /* Try setting it back to see if this signal is really
	 available */
      if (i >= VKI_SIGRTMIN) {
	 struct vki_sigaction tsa;

	 tsa.ksa_handler = (void *)sync_signalhandler;
	 tsa.sa_flags = VKI_SA_SIGINFO;
#        if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
	 tsa.sa_restorer = 0;
#        endif
	 VG_(sigfillset)(&tsa.sa_mask);

	 /* try setting it to some arbitrary handler */
	 if (VG_(sigaction)(i, &tsa, NULL) != 0) {
	    /* failed - not really usable */
	    break;
	 }

	 ret = VG_(sigaction)(i, &sa, NULL);
	 vg_assert(ret == 0);
      }

      VG_(max_signal) = i;

      if (VG_(clo_trace_signals) && VG_(clo_verbosity) > 2)
         VG_(printf)("snaffling handler 0x%lx for signal %d\n", 
                     (Addr)(sa.ksa_handler), i );

      scss.scss_per_sig[i].scss_handler  = sa.ksa_handler;
      scss.scss_per_sig[i].scss_flags    = sa.sa_flags;
      scss.scss_per_sig[i].scss_mask     = sa.sa_mask;
      scss.scss_per_sig[i].scss_restorer = 0;
#     if !defined(VGP_ppc32_aix5) && !defined(VGP_ppc64_aix5)
      scss.scss_per_sig[i].scss_restorer = sa.sa_restorer;
#     endif
   }

   if (VG_(clo_trace_signals))
      VG_(message)(Vg_DebugMsg, "Max kernel-supported signal is %d", VG_(max_signal));

   /* Our private internal signals are treated as ignored */
   scss.scss_per_sig[VG_SIGVGKILL].scss_handler = VKI_SIG_IGN;
   scss.scss_per_sig[VG_SIGVGKILL].scss_flags   = VKI_SA_SIGINFO;
   VG_(sigfillset)(&scss.scss_per_sig[VG_SIGVGKILL].scss_mask);

   /* Copy the process' signal mask into the root thread. */
   vg_assert(VG_(threads)[1].status == VgTs_Init);
   for (i = 2; i < VG_N_THREADS; i++)
      vg_assert(VG_(threads)[i].status == VgTs_Empty);

   VG_(threads)[1].sig_mask = saved_procmask;
   VG_(threads)[1].tmp_sig_mask = saved_procmask;

   /* Calculate SKSS and apply it.  This also sets the initial kernel
      mask we need to run with. */
   handle_SCSS_change( True /* forced update */ );

   /* Leave with all signals still blocked; the thread scheduler loop
      will set the appropriate mask at the appropriate time. */
}

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
