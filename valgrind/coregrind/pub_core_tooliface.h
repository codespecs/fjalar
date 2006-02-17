
/*--------------------------------------------------------------------*/
/*--- The core/tool interface.                pub_core_tooliface.h ---*/
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

#ifndef __PUB_CORE_TOOLIFACE_H
#define __PUB_CORE_TOOLIFACE_H

#include "pub_tool_tooliface.h"

//--------------------------------------------------------------------
// PURPOSE: This module encapsulates the key parts of the core/tool
// interface: 'details', 'needs' and 'trackable events'.
//--------------------------------------------------------------------

// Note the use of C's comma operator here -- it means that we execute both
// statements, and the rvalue of the whole thing is the rvalue of the last
// statement.  This lets us say "x = VG_TDICT_CALL(...)" in the required
// places, while still checking the assertion.
#define VG_TDICT_CALL(fn, args...) \
   ( tl_assert2(VG_(tdict).fn, \
                "you forgot to set VgToolInterface function '" #fn "'"), \
     VG_(tdict).fn(args) )

#define VG_TRACK(fn, args...) 			\
   do {						\
      if (VG_(tdict).track_##fn)		\
	 VG_(tdict).track_##fn(args);           \
   } while(0)

/* These structs are not exposed to tools to mitigate possibility of
   binary-incompatibilities when the core/tool interface changes.  Instead,
   set functions are provided (see include/pub_tool_tooliface.h). */

/* ---------------------------------------------------------------------
   'Details'
   ------------------------------------------------------------------ */

typedef
   struct {
      Char* name;
      Char* version;
      Char* description;
      Char* copyright_author;
      Char* bug_reports_to;
      UInt  avg_translation_sizeB;
   }
   VgDetails;

extern VgDetails VG_(details);

/* ---------------------------------------------------------------------
   'Needs'
   ------------------------------------------------------------------ */

typedef
   struct {
      Bool libc_freeres;
      Bool core_errors;
      Bool tool_errors;
      Bool basic_block_discards;
      Bool command_line_options;
      Bool client_requests;
      Bool syscall_wrapper;
      Bool sanity_checks;
      Bool data_syms;
      Bool malloc_replacement;
   } 
   VgNeeds;

extern VgNeeds VG_(needs);

/* ---------------------------------------------------------------------
   The dictionary of callable tool functions
   ------------------------------------------------------------------ */

typedef struct {
   // -- 'Needs'-related functions ----------------------------------
   // Basic functions
   void  (*tool_pre_clo_init) (void);
   void  (*tool_post_clo_init)(void);
   IRBB* (*tool_instrument)   (VgCallbackClosure*,
                               IRBB*, 
                               VexGuestLayout*, VexGuestExtents*, 
                               IRType, IRType);
   void  (*tool_fini)         (Int);

   // VG_(needs).core_errors
   // (none)
   
   // VG_(needs).tool_errors
   Bool  (*tool_eq_Error)                    (VgRes, Error*, Error*);
   void  (*tool_pp_Error)                    (Error*);
   UInt  (*tool_update_extra)                (Error*);
   Bool  (*tool_recognised_suppression)      (Char*, Supp*);
   Bool  (*tool_read_extra_suppression_info) (Int, Char*, Int, Supp*);
   Bool  (*tool_error_matches_suppression)   (Error*, Supp*);
   Char* (*tool_get_error_name)              (Error*);
   void  (*tool_print_extra_suppression_info)(Error*);

   // VG_(needs).basic_block_discards
   void (*tool_discard_basic_block_info)(Addr64, VexGuestExtents);

   // VG_(needs).command_line_options
   Bool (*tool_process_cmd_line_option)(Char*);
   void (*tool_print_usage)            (void);
   void (*tool_print_debug_usage)      (void);

   // VG_(needs).client_requests
   Bool (*tool_handle_client_request)(ThreadId, UWord*, UWord*);

   // VG_(needs).syscall_wrapper
   void (*tool_pre_syscall) (ThreadId, UInt);
   void (*tool_post_syscall)(ThreadId, UInt, SysRes);

   // VG_(needs).sanity_checks
   Bool (*tool_cheap_sanity_check)(void);
   Bool (*tool_expensive_sanity_check)(void);

   // VG_(needs).malloc_replacement
   void* (*tool_malloc)              (ThreadId, SizeT);
   void* (*tool___builtin_new)       (ThreadId, SizeT);
   void* (*tool___builtin_vec_new)   (ThreadId, SizeT);
   void* (*tool_memalign)            (ThreadId, SizeT, SizeT);
   void* (*tool_calloc)              (ThreadId, SizeT, SizeT);
   void  (*tool_free)                (ThreadId, void*);
   void  (*tool___builtin_delete)    (ThreadId, void*);
   void  (*tool___builtin_vec_delete)(ThreadId, void*);
   void* (*tool_realloc)             (ThreadId, void*, SizeT);
   SizeT tool_client_redzone_szB;

   // -- Event tracking functions ------------------------------------
   void (*track_new_mem_startup)     (Addr, SizeT, Bool, Bool, Bool);
   void (*track_new_mem_stack_signal)(Addr, SizeT);
   void (*track_new_mem_brk)         (Addr, SizeT);
   void (*track_new_mem_mmap)        (Addr, SizeT, Bool, Bool, Bool);

   void (*track_copy_mem_remap)      (Addr src, Addr dst, SizeT);
   void (*track_change_mem_mprotect) (Addr, SizeT, Bool, Bool, Bool);
   void (*track_die_mem_stack_signal)(Addr, SizeT);
   void (*track_die_mem_brk)         (Addr, SizeT);
   void (*track_die_mem_munmap)      (Addr, SizeT);

   void VG_REGPARM(1) (*track_new_mem_stack_4) (Addr);
   void VG_REGPARM(1) (*track_new_mem_stack_8) (Addr);
   void VG_REGPARM(1) (*track_new_mem_stack_12)(Addr);
   void VG_REGPARM(1) (*track_new_mem_stack_16)(Addr);
   void VG_REGPARM(1) (*track_new_mem_stack_32)(Addr);
   void (*track_new_mem_stack)(Addr, SizeT);

   void VG_REGPARM(1) (*track_die_mem_stack_4) (Addr);
   void VG_REGPARM(1) (*track_die_mem_stack_8) (Addr);
   void VG_REGPARM(1) (*track_die_mem_stack_12)(Addr);
   void VG_REGPARM(1) (*track_die_mem_stack_16)(Addr);
   void VG_REGPARM(1) (*track_die_mem_stack_32)(Addr);
   void (*track_die_mem_stack)(Addr, SizeT);

   void (*track_ban_mem_stack)(Addr, SizeT);

   void (*track_pre_mem_read)       (CorePart, ThreadId, Char*, Addr, SizeT);
   void (*track_pre_mem_read_asciiz)(CorePart, ThreadId, Char*, Addr);
   void (*track_pre_mem_write)      (CorePart, ThreadId, Char*, Addr, SizeT);
   void (*track_post_mem_write)     (CorePart, ThreadId, Addr, SizeT);

   void (*track_pre_reg_read)  (CorePart, ThreadId, Char*, OffT, SizeT);
   void (*track_post_reg_write)(CorePart, ThreadId,        OffT, SizeT);
   void (*track_post_reg_write_clientcall_return)(ThreadId, OffT, SizeT, Addr);

   void (*track_thread_run)(ThreadId);

   void (*track_post_thread_create)(ThreadId, ThreadId);
   void (*track_post_thread_join)  (ThreadId, ThreadId);

   void (*track_pre_mutex_lock)   (ThreadId, void*);
   void (*track_post_mutex_lock)  (ThreadId, void*);
   void (*track_post_mutex_unlock)(ThreadId, void*);

   void (*track_pre_deliver_signal) (ThreadId, Int sigNo, Bool);
   void (*track_post_deliver_signal)(ThreadId, Int sigNo);

} VgToolInterface;

extern VgToolInterface VG_(tdict);

/* ---------------------------------------------------------------------
   Miscellaneous functions
   ------------------------------------------------------------------ */

Bool VG_(sanity_check_needs) ( Char** failmsg );

#endif   // __PUB_CORE_TOOLIFACE_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
