
/*--------------------------------------------------------------------*/
/*--- Machine-related stuff.                           m_machine.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

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

#include "pub_core_basics.h"
#include "pub_core_vki.h"
#include "pub_core_threadstate.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcbase.h"
#include "pub_core_machine.h"
#include "pub_core_cpuid.h"
#include "pub_core_libcsignal.h"   // for ppc32 messing with SIGILL and SIGFPE
#include "pub_core_debuglog.h"


#define INSTR_PTR(regs)    ((regs).vex.VG_INSTR_PTR)
#define STACK_PTR(regs)    ((regs).vex.VG_STACK_PTR)
#define FRAME_PTR(regs)    ((regs).vex.VG_FRAME_PTR)
#define INT_RET_REG(regs)  ((regs).vex.VG_INT_RET_REG)
#define INT_RET2_REG(regs) ((regs).vex.VG_INT_RET2_REG)
#define INT_XCX(regs)      ((regs).vex.VG_XCX)
#define INT_XBX(regs)      ((regs).vex.VG_XBX)
#define INT_XSI(regs)      ((regs).vex.VG_XSI)
#define INT_XDI(regs)      ((regs).vex.VG_XDI)
#define CASE_XMM(regs, N)       case N: return (regs).vex.guest_XMM##N; break;
#define CASE_SHADOW_XMM(regs, N)       case N: return (regs).vex_shadow1.guest_XMM##N; break;

Addr VG_(get_SP) ( ThreadId tid )
{
   return STACK_PTR( VG_(threads)[tid].arch );
}

Addr VG_(get_IP) ( ThreadId tid )
{
   return INSTR_PTR( VG_(threads)[tid].arch );
}

Addr VG_(get_FP) ( ThreadId tid )
{
   return FRAME_PTR( VG_(threads)[tid].arch );
}

Addr VG_(get_xCX) ( ThreadId tid )
{
  return INT_XCX( VG_(threads)[tid].arch );
}

Addr VG_(get_xBX) ( ThreadId tid )
{
  return INT_XBX( VG_(threads)[tid].arch );
}

Addr VG_(get_xSI) ( ThreadId tid )
{
  return INT_XSI( VG_(threads)[tid].arch );
}

Addr VG_(get_xDI) ( ThreadId tid )
{
  return INT_XDI( VG_(threads)[tid].arch );
}


UInt* VG_(get_XMM_N)( ThreadId tid, UInt num )  
{
  switch(num) {
    CASE_XMM(VG_(threads)[tid].arch, 0);
    CASE_XMM(VG_(threads)[tid].arch, 1);
  default:
    tl_assert(0 && "xmm2-15 not yet implemented");   
  }
}

#if defined(VGA_amd64)
Addr VG_(get_R8) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R8;}
Addr VG_(get_R9) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R9;}
Addr VG_(get_R10) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R10;}
Addr VG_(get_R11) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R11;}
Addr VG_(get_R12) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R12;}
Addr VG_(get_R13) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R13;}
Addr VG_(get_R14) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R14;}
Addr VG_(get_R15) ( ThreadId tid ){ return VG_(threads)[tid].arch.vex.guest_R15;}
#endif

Addr VG_(get_LR) ( ThreadId tid )
{
#  if defined(VGA_ppc32) || defined(VGA_ppc64)
   return VG_(threads)[tid].arch.vex.guest_LR;
#  elif defined(VGA_x86) || defined(VGA_amd64)
   return 0;
#  else
#    error "Unknown arch"
#  endif
}

Addr VG_(get_xAX) ( ThreadId tid )
{
   return INT_RET_REG( VG_(threads)[tid].arch );
}

Addr VG_(get_xDX) ( ThreadId tid )
{
   return INT_RET2_REG( VG_(threads)[tid].arch );
}

void VG_(set_SP) ( ThreadId tid, Addr sp )
{
   STACK_PTR( VG_(threads)[tid].arch ) = sp;
}

void VG_(set_IP) ( ThreadId tid, Addr ip )
{
   INSTR_PTR( VG_(threads)[tid].arch ) = ip;
}

// BEGIN - pgbovine

// PG begin - Hacked to provide useful return value information for
// Kvasir (we really need a more elegant solution)
double VG_(get_FPU_stack_top) ( ThreadId tid ) // 64-bit read
{
   // Remember to re-interpret cast this as a double instead of a ULong
   return *((double*)(&(VG_(threads)[tid].arch.vex.guest_FPREG
                        [VG_(threads)[tid].arch.vex.guest_FTOP & 7])));
}

UWord VG_(get_shadow_xAX) ( ThreadId tid )
{
   return VG_(threads)[tid].arch.vex_shadow1.VG_INT_RET_REG;
}

UWord VG_(get_shadow_xDX) ( ThreadId tid )
{
   return VG_(threads)[tid].arch.vex_shadow1.VG_INT_RET2_REG;
}

ULong VG_(get_shadow_FPU_stack_top) ( ThreadId tid ) // 64-bit read
{
   return VG_(threads)[tid].arch.
      vex_shadow1.guest_FPREG[VG_(threads)[tid].arch.vex.guest_FTOP & 7];
}

UInt* VG_(get_shadow_XMM_N)( ThreadId tid, UInt num )  
{
  
  /* VG_(printf)("Location of xmm0 %x - index %x\n", VG_(threads)[tid].arch.vex_shadow1.guest_XMM0, (UWord)(VG_(threads)[tid].arch.vex_shadow1.guest_XMM0) - (UWord)(&VG_(threads)[tid].arch.vex.guest_RAX)); */

  /* VG_(printf)("Shadow? %x\n", VG_(threads)[tid].arch.vex_shadow1.guest_XMM0[0]); */
  /* VG_(printf)("Shadow? %x\n", VG_(threads)[tid].arch.vex_shadow1.guest_XMM0[1]); */
  switch(num) {
    CASE_SHADOW_XMM(VG_(threads)[tid].arch, 0);
    CASE_SHADOW_XMM(VG_(threads)[tid].arch, 1);
  default:
    tl_assert(0 && "xmm2-15 not yet implemented");   
  }
}

// Ok, if the stuff before were hacks, then these are SUPER HACKS
// because it relies on our ad-hoc (4 * offset) reference into
// VexGuestX86State vex_extra_shadow[4] within TheadArchState:
UWord VG_(get_xAX_tag) ( ThreadId tid )
{
   return *(VG_(get_tag_ptr_for_guest_offset)(tid, offsetof(VexGuestArchState,
							    VG_INT_RET_REG)));
}

UWord VG_(get_xDX_tag) ( ThreadId tid )
{
   return *(VG_(get_tag_ptr_for_guest_offset)(tid, offsetof(VexGuestArchState,
							    VG_INT_RET2_REG)));
}

UWord VG_(get_XMM_N_tag)( ThreadId tid, UInt num )  
{

   return *(VG_(get_tag_ptr_for_guest_offset)(tid, offsetof(VexGuestArchState,
							    guest_XMM0)));
}

UWord VG_(get_FPU_stack_top_tag) ( ThreadId tid )
{
   int FPUoffset = VG_(threads)[tid].arch.vex.guest_FTOP & 7;

   // The start of the FPU stack is at offset 64 so an added offset
   // from that tells us where the top of the FPU stack is
   int offset = FPUoffset + 64;

   return *(VG_(get_tag_ptr_for_guest_offset)(tid, offset));
}

// This is a generalization of all the other tag getter functions,
// which takes in an offset from the guest state (as denoted by
// the member variable locations in vex/pub/libvex_guest_x86.h)
// and performs the (4 * offset) hack and returns the address of
// the associated tag
UInt* VG_(get_tag_ptr_for_guest_offset) ( ThreadId tid, UInt offset )
{
   return ((UInt*)((char*)(VG_(threads)[tid].arch.vex_extra_shadow) +
		    (4 * offset)));
}

// END - pgbovine

void VG_(set_syscall_return_shadows) ( ThreadId tid,
                                       /* shadow vals for the result */
                                       UWord s1res, UWord s2res,
                                       /* shadow vals for the error val */
                                       UWord s1err, UWord s2err )
{
#  if defined(VGP_x86_linux)
   VG_(threads)[tid].arch.vex_shadow1.guest_EAX = s1res;
   VG_(threads)[tid].arch.vex_shadow2.guest_EAX = s2res;
#  elif defined(VGP_amd64_linux)
   VG_(threads)[tid].arch.vex_shadow1.guest_RAX = s1res;
   VG_(threads)[tid].arch.vex_shadow2.guest_RAX = s2res;
#  elif defined(VGP_ppc32_linux) || defined(VGP_ppc64_linux)
   VG_(threads)[tid].arch.vex_shadow1.guest_GPR3 = s1res;
   VG_(threads)[tid].arch.vex_shadow2.guest_GPR3 = s2res;
#  elif defined(VGP_ppc32_aix5) || defined(VGP_ppc64_aix5)
   VG_(threads)[tid].arch.vex_shadow1.guest_GPR3 = s1res;
   VG_(threads)[tid].arch.vex_shadow2.guest_GPR3 = s2res;
   VG_(threads)[tid].arch.vex_shadow1.guest_GPR4 = s1err;
   VG_(threads)[tid].arch.vex_shadow2.guest_GPR4 = s2err;
#  elif defined(VGO_darwin)
   // GrP fixme darwin syscalls may return more values (2 registers plus error)
#  else
#    error "Unknown plat"
#  endif
}

void
VG_(get_shadow_regs_area) ( ThreadId tid,
                            /*DST*/UChar* dst,
                            /*SRC*/Int shadowNo, PtrdiffT offset, SizeT size )
{
   void*        src;
   ThreadState* tst;
   vg_assert(shadowNo == 0 || shadowNo == 1 || shadowNo == 2);
   vg_assert(VG_(is_valid_tid)(tid));
   // Bounds check
   vg_assert(0 <= offset && offset < sizeof(VexGuestArchState));
   vg_assert(offset + size <= sizeof(VexGuestArchState));
   // Copy
   tst = & VG_(threads)[tid];
   src = NULL;
   switch (shadowNo) {
      case 0: src = (void*)(((Addr)&(tst->arch.vex)) + offset); break;
      case 1: src = (void*)(((Addr)&(tst->arch.vex_shadow1)) + offset); break;
      case 2: src = (void*)(((Addr)&(tst->arch.vex_shadow2)) + offset); break;
   }
   tl_assert(src != NULL);
   VG_(memcpy)( dst, src, size);
}

void
VG_(set_shadow_regs_area) ( ThreadId tid,
                            /*DST*/Int shadowNo, PtrdiffT offset, SizeT size,
                            /*SRC*/const UChar* src )
{
   void*        dst;
   ThreadState* tst;
   vg_assert(shadowNo == 0 || shadowNo == 1 || shadowNo == 2);
   vg_assert(VG_(is_valid_tid)(tid));
   // Bounds check
   vg_assert(0 <= offset && offset < sizeof(VexGuestArchState));
   vg_assert(offset + size <= sizeof(VexGuestArchState));
   // Copy
   tst = & VG_(threads)[tid];
   dst = NULL;
   switch (shadowNo) {
      case 0: dst = (void*)(((Addr)&(tst->arch.vex)) + offset); break;
      case 1: dst = (void*)(((Addr)&(tst->arch.vex_shadow1)) + offset); break;
      case 2: dst = (void*)(((Addr)&(tst->arch.vex_shadow2)) + offset); break;
   }
   tl_assert(dst != NULL);
   VG_(memcpy)( dst, src, size);
}


static void apply_to_GPs_of_tid(VexGuestArchState* vex, void (*f)(Addr))
{
#if defined(VGA_x86)
   (*f)(vex->guest_EAX);
   (*f)(vex->guest_ECX);
   (*f)(vex->guest_EDX);
   (*f)(vex->guest_EBX);
   (*f)(vex->guest_ESI);
   (*f)(vex->guest_EDI);
   (*f)(vex->guest_ESP);
   (*f)(vex->guest_EBP);
#elif defined(VGA_amd64)
   (*f)(vex->guest_RAX);
   (*f)(vex->guest_RCX);
   (*f)(vex->guest_RDX);
   (*f)(vex->guest_RBX);
   (*f)(vex->guest_RSI);
   (*f)(vex->guest_RDI);
   (*f)(vex->guest_RSP);
   (*f)(vex->guest_RBP);
   (*f)(vex->guest_R8);
   (*f)(vex->guest_R9);
   (*f)(vex->guest_R10);
   (*f)(vex->guest_R11);
   (*f)(vex->guest_R12);
   (*f)(vex->guest_R13);
   (*f)(vex->guest_R14);
   (*f)(vex->guest_R15);
#elif defined(VGA_ppc32) || defined(VGA_ppc64)
   /* XXX ask tool about validity? */
   (*f)(vex->guest_GPR0);
   (*f)(vex->guest_GPR1);
   (*f)(vex->guest_GPR2);
   (*f)(vex->guest_GPR3);
   (*f)(vex->guest_GPR4);
   (*f)(vex->guest_GPR5);
   (*f)(vex->guest_GPR6);
   (*f)(vex->guest_GPR7);
   (*f)(vex->guest_GPR8);
   (*f)(vex->guest_GPR9);
   (*f)(vex->guest_GPR10);
   (*f)(vex->guest_GPR11);
   (*f)(vex->guest_GPR12);
   (*f)(vex->guest_GPR13);
   (*f)(vex->guest_GPR14);
   (*f)(vex->guest_GPR15);
   (*f)(vex->guest_GPR16);
   (*f)(vex->guest_GPR17);
   (*f)(vex->guest_GPR18);
   (*f)(vex->guest_GPR19);
   (*f)(vex->guest_GPR20);
   (*f)(vex->guest_GPR21);
   (*f)(vex->guest_GPR22);
   (*f)(vex->guest_GPR23);
   (*f)(vex->guest_GPR24);
   (*f)(vex->guest_GPR25);
   (*f)(vex->guest_GPR26);
   (*f)(vex->guest_GPR27);
   (*f)(vex->guest_GPR28);
   (*f)(vex->guest_GPR29);
   (*f)(vex->guest_GPR30);
   (*f)(vex->guest_GPR31);
   (*f)(vex->guest_CTR);
   (*f)(vex->guest_LR);

#else
#  error Unknown arch
#endif
}


void VG_(apply_to_GP_regs)(void (*f)(UWord))
{
   ThreadId tid;

   for (tid = 1; tid < VG_N_THREADS; tid++) {
      if (VG_(is_valid_tid)(tid)) {
         ThreadState* tst = VG_(get_ThreadState)(tid);
         apply_to_GPs_of_tid(&(tst->arch.vex), f);
      }
   }
}

void VG_(thread_stack_reset_iter)(/*OUT*/ThreadId* tid)
{
   *tid = (ThreadId)(-1);
}

Bool VG_(thread_stack_next)(/*MOD*/ThreadId* tid,
                            /*OUT*/Addr* stack_min,
                            /*OUT*/Addr* stack_max)
{
   ThreadId i;
   for (i = (*tid)+1; i < VG_N_THREADS; i++) {
      if (i == VG_INVALID_THREADID)
         continue;
      if (VG_(threads)[i].status != VgTs_Empty) {
         *tid       = i;
         *stack_min = VG_(get_SP)(i);
         *stack_max = VG_(threads)[i].client_stack_highest_word;
         return True;
      }
   }
   return False;
}

Addr VG_(thread_get_stack_max)(ThreadId tid)
{
   vg_assert(0 <= tid && tid < VG_N_THREADS && tid != VG_INVALID_THREADID);
   vg_assert(VG_(threads)[tid].status != VgTs_Empty);
   return VG_(threads)[tid].client_stack_highest_word;
}

SizeT VG_(thread_get_stack_size)(ThreadId tid)
{
   vg_assert(0 <= tid && tid < VG_N_THREADS && tid != VG_INVALID_THREADID);
   vg_assert(VG_(threads)[tid].status != VgTs_Empty);
   return VG_(threads)[tid].client_stack_szB;
}

//-------------------------------------------------------------
/* Details about the capabilities of the underlying (host) CPU.  These
   details are acquired by (1) enquiring with the CPU at startup, or
   (2) from the AT_SYSINFO entries the kernel gave us (ppc32 cache
   line size).  It's a bit nasty in the sense that there's no obvious
   way to stop uses of some of this info before it's ready to go.

   Current dependencies are:

   x86:   initially:  call VG_(machine_get_hwcaps)

          then safe to use VG_(machine_get_VexArchInfo)
                       and VG_(machine_x86_have_mxcsr)
   -------------
   amd64: initially:  call VG_(machine_get_hwcaps)

          then safe to use VG_(machine_get_VexArchInfo)
   -------------
   ppc32: initially:  call VG_(machine_get_hwcaps)
                      call VG_(machine_ppc32_set_clszB)

          then safe to use VG_(machine_get_VexArchInfo)
                       and VG_(machine_ppc32_has_FP)
                       and VG_(machine_ppc32_has_VMX)
   -------------
   ppc64: initially:  call VG_(machine_get_hwcaps)
                      call VG_(machine_ppc64_set_clszB)

          then safe to use VG_(machine_get_VexArchInfo)
                       and VG_(machine_ppc64_has_VMX)

   VG_(machine_get_hwcaps) may use signals (although it attempts to
   leave signal state unchanged) and therefore should only be
   called before m_main sets up the client's signal state.
*/

/* --------- State --------- */
static Bool        hwcaps_done = False;

/* --- all archs --- */
static VexArch     va;
static VexArchInfo vai;

#if defined(VGA_x86)
UInt VG_(machine_x86_have_mxcsr) = 0;
#endif
#if defined(VGA_ppc32)
UInt VG_(machine_ppc32_has_FP)  = 0;
UInt VG_(machine_ppc32_has_VMX) = 0;
#endif
#if defined(VGA_ppc64)
ULong VG_(machine_ppc64_has_VMX) = 0;
#endif


/* Determine what insn set and insn set variant the host has, and
   record it.  To be called once at system startup.  Returns False if
   this a CPU incapable of running Valgrind. */

#if defined(VGA_ppc32) || defined(VGA_ppc64)
#include <setjmp.h> // For jmp_buf
static jmp_buf env_unsup_insn;
static void handler_unsup_insn ( Int x ) { __builtin_longjmp(env_unsup_insn,1); }
#endif

Bool VG_(machine_get_hwcaps)( void )
{
   vg_assert(hwcaps_done == False);
   hwcaps_done = True;

   // Whack default settings into vai, so that we only need to fill in
   // any interesting bits.
   LibVEX_default_VexArchInfo(&vai);

#if defined(VGA_x86)
   { Bool have_sse1, have_sse2, have_cx8;
     UInt eax, ebx, ecx, edx;

     if (!VG_(has_cpuid)())
        /* we can't do cpuid at all.  Give up. */
        return False;

     VG_(cpuid)(0, &eax, &ebx, &ecx, &edx);
     if (eax < 1)
        /* we can't ask for cpuid(x) for x > 0.  Give up. */
        return False;

     /* get capabilities bits into edx */
     VG_(cpuid)(1, &eax, &ebx, &ecx, &edx);

     have_sse1 = (edx & (1<<25)) != 0; /* True => have sse insns */
     have_sse2 = (edx & (1<<26)) != 0; /* True => have sse2 insns */

     /* cmpxchg8b is a minimum requirement now; if we don't have it we
        must simply give up.  But all CPUs since Pentium-I have it, so
        that doesn't seem like much of a restriction. */
     have_cx8 = (edx & (1<<8)) != 0; /* True => have cmpxchg8b */
     if (!have_cx8)
        return False;

     if (have_sse2 && have_sse1) {
        va          = VexArchX86;
        vai.hwcaps  = VEX_HWCAPS_X86_SSE1;
        vai.hwcaps |= VEX_HWCAPS_X86_SSE2;
        VG_(machine_x86_have_mxcsr) = 1;
        return True;
     }

     if (have_sse1) {
        va          = VexArchX86;
        vai.hwcaps  = VEX_HWCAPS_X86_SSE1;
        VG_(machine_x86_have_mxcsr) = 1;
        return True;
     }

     va         = VexArchX86;
     vai.hwcaps = 0; /*baseline - no sse at all*/
     VG_(machine_x86_have_mxcsr) = 0;
     return True;
   }

#elif defined(VGA_amd64)
   { Bool have_sse1, have_sse2, have_sse3, have_cx8, have_cx16;
     UInt eax, ebx, ecx, edx;

     if (!VG_(has_cpuid)())
        /* we can't do cpuid at all.  Give up. */
        return False;

     VG_(cpuid)(0, &eax, &ebx, &ecx, &edx);
     if (eax < 1)
        /* we can't ask for cpuid(x) for x > 0.  Give up. */
        return False;

     /* get capabilities bits into edx */
     VG_(cpuid)(1, &eax, &ebx, &ecx, &edx);

     have_sse1 = (edx & (1<<25)) != 0; /* True => have sse insns */
     have_sse2 = (edx & (1<<26)) != 0; /* True => have sse2 insns */
     have_sse3 = (ecx & (1<<0)) != 0;  /* True => have sse3 insns */

     /* cmpxchg8b is a minimum requirement now; if we don't have it we
        must simply give up.  But all CPUs since Pentium-I have it, so
        that doesn't seem like much of a restriction. */
     have_cx8 = (edx & (1<<8)) != 0; /* True => have cmpxchg8b */
     if (!have_cx8)
        return False;

     /* on amd64 we tolerate older cpus, which don't have cmpxchg16b */
     have_cx16 = (ecx & (1<<13)) != 0; /* True => have cmpxchg16b */

     va         = VexArchAMD64;
     vai.hwcaps = (have_sse3 ? VEX_HWCAPS_AMD64_SSE3 : 0)
                  | (have_cx16 ? VEX_HWCAPS_AMD64_CX16 : 0);
     return True;
   }

#elif defined(VGA_ppc32)
   {
     /* Find out which subset of the ppc32 instruction set is supported by
        verifying whether various ppc32 instructions generate a SIGILL
        or a SIGFPE. An alternative approach is to check the AT_HWCAP and
        AT_PLATFORM entries in the ELF auxiliary table -- see also
        the_iifii.client_auxv in m_main.c.
      */
     vki_sigset_t          saved_set, tmp_set;
     vki_sigaction_fromK_t saved_sigill_act, saved_sigfpe_act;
     vki_sigaction_toK_t     tmp_sigill_act,   tmp_sigfpe_act;

     volatile Bool have_F, have_V, have_FX, have_GX;
     Int r;

     /* This is a kludge.  Really we ought to back-convert saved_act
        into a toK_t using VG_(convert_sigaction_fromK_to_toK), but
        since that's a no-op on all ppc32 platforms so far supported,
        it's not worth the typing effort.  At least include most basic
        sanity check: */
     vg_assert(sizeof(vki_sigaction_fromK_t) == sizeof(vki_sigaction_toK_t));

     VG_(sigemptyset)(&tmp_set);
     VG_(sigaddset)(&tmp_set, VKI_SIGILL);
     VG_(sigaddset)(&tmp_set, VKI_SIGFPE);

     r = VG_(sigprocmask)(VKI_SIG_UNBLOCK, &tmp_set, &saved_set);
     vg_assert(r == 0);

     r = VG_(sigaction)(VKI_SIGILL, NULL, &saved_sigill_act);
     vg_assert(r == 0);
     tmp_sigill_act = saved_sigill_act;

     r = VG_(sigaction)(VKI_SIGFPE, NULL, &saved_sigfpe_act);
     vg_assert(r == 0);
     tmp_sigfpe_act = saved_sigfpe_act;

     /* NODEFER: signal handler does not return (from the kernel's point of
        view), hence if it is to successfully catch a signal more than once,
        we need the NODEFER flag. */
     tmp_sigill_act.sa_flags &= ~VKI_SA_RESETHAND;
     tmp_sigill_act.sa_flags &= ~VKI_SA_SIGINFO;
     tmp_sigill_act.sa_flags |=  VKI_SA_NODEFER;
     tmp_sigill_act.ksa_handler = handler_unsup_insn;
     r = VG_(sigaction)(VKI_SIGILL, &tmp_sigill_act, NULL);
     vg_assert(r == 0);

     tmp_sigfpe_act.sa_flags &= ~VKI_SA_RESETHAND;
     tmp_sigfpe_act.sa_flags &= ~VKI_SA_SIGINFO;
     tmp_sigfpe_act.sa_flags |=  VKI_SA_NODEFER;
     tmp_sigfpe_act.ksa_handler = handler_unsup_insn;
     r = VG_(sigaction)(VKI_SIGFPE, &tmp_sigfpe_act, NULL);
     vg_assert(r == 0);

     /* standard FP insns */
     have_F = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_F = False;
     } else {
        __asm__ __volatile__(".long 0xFC000090"); /*fmr 0,0 */
     }

     /* Altivec insns */
     have_V = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_V = False;
     } else {
        /* Unfortunately some older assemblers don't speak Altivec (or
           choose not to), so to be safe we directly emit the 32-bit
           word corresponding to "vor 0,0,0".  This fixes a build
           problem that happens on Debian 3.1 (ppc32), and probably
           various other places. */
        __asm__ __volatile__(".long 0x10000484"); /*vor 0,0,0*/
     }

     /* General-Purpose optional (fsqrt, fsqrts) */
     have_FX = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_FX = False;
     } else {
        __asm__ __volatile__(".long 0xFC00002C"); /*fsqrt 0,0 */
     }

     /* Graphics optional (stfiwx, fres, frsqrte, fsel) */
     have_GX = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_GX = False;
     } else {
        __asm__ __volatile__(".long 0xFC000034"); /* frsqrte 0,0 */
     }

     r = VG_(sigaction)(VKI_SIGILL, &saved_sigill_act, NULL);
     vg_assert(r == 0);
     r = VG_(sigaction)(VKI_SIGFPE, &saved_sigfpe_act, NULL);
     vg_assert(r == 0);
     r = VG_(sigprocmask)(VKI_SIG_SETMASK, &saved_set, NULL);
     vg_assert(r == 0);
     VG_(debugLog)(1, "machine", "F %d V %d FX %d GX %d\n",
                    (Int)have_F, (Int)have_V, (Int)have_FX, (Int)have_GX);
     /* Make FP a prerequisite for VMX (bogusly so), and for FX and GX. */
     if (have_V && !have_F)
        have_V = False;
     if (have_FX && !have_F)
        have_FX = False;
     if (have_GX && !have_F)
        have_GX = False;

     VG_(machine_ppc32_has_FP)  = have_F ? 1 : 0;
     VG_(machine_ppc32_has_VMX) = have_V ? 1 : 0;

     va = VexArchPPC32;

     vai.hwcaps = 0;
     if (have_F)  vai.hwcaps |= VEX_HWCAPS_PPC32_F;
     if (have_V)  vai.hwcaps |= VEX_HWCAPS_PPC32_V;
     if (have_FX) vai.hwcaps |= VEX_HWCAPS_PPC32_FX;
     if (have_GX) vai.hwcaps |= VEX_HWCAPS_PPC32_GX;

     /* But we're not done yet: VG_(machine_ppc32_set_clszB) must be
        called before we're ready to go. */
     return True;
   }

#elif defined(VGA_ppc64)
   {
     /* Same instruction set detection algorithm as for ppc32. */
     vki_sigset_t          saved_set, tmp_set;
     vki_sigaction_fromK_t saved_sigill_act, saved_sigfpe_act;
     vki_sigaction_toK_t     tmp_sigill_act,   tmp_sigfpe_act;

     volatile Bool have_F, have_V, have_FX, have_GX;
     Int r;

     /* This is a kludge.  Really we ought to back-convert saved_act
        into a toK_t using VG_(convert_sigaction_fromK_to_toK), but
        since that's a no-op on all ppc64 platforms so far supported,
        it's not worth the typing effort.  At least include most basic
        sanity check: */
     vg_assert(sizeof(vki_sigaction_fromK_t) == sizeof(vki_sigaction_toK_t));

     VG_(sigemptyset)(&tmp_set);
     VG_(sigaddset)(&tmp_set, VKI_SIGILL);
     VG_(sigaddset)(&tmp_set, VKI_SIGFPE);

     r = VG_(sigprocmask)(VKI_SIG_UNBLOCK, &tmp_set, &saved_set);
     vg_assert(r == 0);

     r = VG_(sigaction)(VKI_SIGILL, NULL, &saved_sigill_act);
     vg_assert(r == 0);
     tmp_sigill_act = saved_sigill_act;

     VG_(sigaction)(VKI_SIGFPE, NULL, &saved_sigfpe_act);
     tmp_sigfpe_act = saved_sigfpe_act;

     /* NODEFER: signal handler does not return (from the kernel's point of
        view), hence if it is to successfully catch a signal more than once,
        we need the NODEFER flag. */
     tmp_sigill_act.sa_flags &= ~VKI_SA_RESETHAND;
     tmp_sigill_act.sa_flags &= ~VKI_SA_SIGINFO;
     tmp_sigill_act.sa_flags |=  VKI_SA_NODEFER;
     tmp_sigill_act.ksa_handler = handler_unsup_insn;
     VG_(sigaction)(VKI_SIGILL, &tmp_sigill_act, NULL);

     tmp_sigfpe_act.sa_flags &= ~VKI_SA_RESETHAND;
     tmp_sigfpe_act.sa_flags &= ~VKI_SA_SIGINFO;
     tmp_sigfpe_act.sa_flags |=  VKI_SA_NODEFER;
     tmp_sigfpe_act.ksa_handler = handler_unsup_insn;
     VG_(sigaction)(VKI_SIGFPE, &tmp_sigfpe_act, NULL);

     /* standard FP insns */
     have_F = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_F = False;
     } else {
        __asm__ __volatile__("fmr 0,0");
     }

     /* Altivec insns */
     have_V = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_V = False;
     } else {
        __asm__ __volatile__(".long 0x10000484"); /*vor 0,0,0*/
     }

     /* General-Purpose optional (fsqrt, fsqrts) */
     have_FX = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_FX = False;
     } else {
        __asm__ __volatile__(".long 0xFC00002C"); /*fsqrt 0,0*/
     }

     /* Graphics optional (stfiwx, fres, frsqrte, fsel) */
     have_GX = True;
     if (__builtin_setjmp(env_unsup_insn)) {
        have_GX = False;
     } else {
        __asm__ __volatile__(".long 0xFC000034"); /*frsqrte 0,0*/
     }

     VG_(sigaction)(VKI_SIGILL, &saved_sigill_act, NULL);
     VG_(sigaction)(VKI_SIGFPE, &saved_sigfpe_act, NULL);
     VG_(sigprocmask)(VKI_SIG_SETMASK, &saved_set, NULL);
     VG_(debugLog)(1, "machine", "F %d V %d FX %d GX %d\n",
                    (Int)have_F, (Int)have_V, (Int)have_FX, (Int)have_GX);
     /* on ppc64, if we don't even have FP, just give up. */
     if (!have_F)
        return False;

     VG_(machine_ppc64_has_VMX) = have_V ? 1 : 0;

     va = VexArchPPC64;

     vai.hwcaps = 0;
     if (have_V)  vai.hwcaps |= VEX_HWCAPS_PPC64_V;
     if (have_FX) vai.hwcaps |= VEX_HWCAPS_PPC64_FX;
     if (have_GX) vai.hwcaps |= VEX_HWCAPS_PPC64_GX;

     /* But we're not done yet: VG_(machine_ppc64_set_clszB) must be
        called before we're ready to go. */
     return True;
   }

#else
#  error "Unknown arch"
#endif
}

/* Notify host cpu cache line size. */
#if defined(VGA_ppc32)
void VG_(machine_ppc32_set_clszB)( Int szB )
{
   vg_assert(hwcaps_done);

   /* Either the value must not have been set yet (zero) or we can
      tolerate it being set to the same value multiple times, as the
      stack scanning logic in m_main is a bit stupid. */
   vg_assert(vai.ppc_cache_line_szB == 0
             || vai.ppc_cache_line_szB == szB);

   vg_assert(szB == 32 || szB == 64 || szB == 128);
   vai.ppc_cache_line_szB = szB;
}
#endif


/* Notify host cpu cache line size. */
#if defined(VGA_ppc64)
void VG_(machine_ppc64_set_clszB)( Int szB )
{
   vg_assert(hwcaps_done);

   /* Either the value must not have been set yet (zero) or we can
      tolerate it being set to the same value multiple times, as the
      stack scanning logic in m_main is a bit stupid. */
   vg_assert(vai.ppc_cache_line_szB == 0
             || vai.ppc_cache_line_szB == szB);

   vg_assert(szB == 32 || szB == 64 || szB == 128);
   vai.ppc_cache_line_szB = szB;
}
#endif


/* Fetch host cpu info, once established. */
void VG_(machine_get_VexArchInfo)( /*OUT*/VexArch* pVa,
                                   /*OUT*/VexArchInfo* pVai )
{
   vg_assert(hwcaps_done);
   if (pVa)  *pVa  = va;
   if (pVai) *pVai = vai;
}


// Given a pointer to a function as obtained by "& functionname" in C,
// produce a pointer to the actual entry point for the function.
void* VG_(fnptr_to_fnentry)( void* f )
{
#if defined(VGP_x86_linux)   || defined(VGP_amd64_linux) || \
    defined(VGP_ppc32_linux) || defined(VGO_darwin)
   return f;
#elif defined(VGP_ppc64_linux) || defined(VGP_ppc32_aix5) \
                               || defined(VGP_ppc64_aix5)
   /* All other ppc variants use the AIX scheme, in which f is a
      pointer to a 3-word function descriptor, of which the first word
      is the entry address. */
   UWord* descr = (UWord*)f;
   return (void*)(descr[0]);
#else
#  error "Unknown platform"
#endif
}

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
