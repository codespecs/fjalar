
/*--------------------------------------------------------------------*/
/*--- Helgrind: a Valgrind tool for detecting errors               ---*/
/*--- in threaded programs.                              hg_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Helgrind, a Valgrind tool for detecting errors
   in threaded programs.

   Copyright (C) 2007-2009 OpenWorks LLP
      info@open-works.co.uk

   Copyright (C) 2007-2009 Apple, Inc.

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

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.
*/

#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_machine.h"
#include "pub_tool_options.h"
#include "pub_tool_xarray.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_debuginfo.h"  /* VG_(get_data_description) */
#include "pub_tool_wordfm.h"

#include "hg_basics.h"
#include "hg_wordset.h"
#include "hg_lock_n_thread.h"
#include "hg_errors.h"

#include "libhb.h"

#include "helgrind.h"


// FIXME: new_mem_w_tid ignores the supplied tid. (wtf?!)

// FIXME: when client destroys a lock or a CV, remove these
// from our mappings, so that the associated SO can be freed up

/*----------------------------------------------------------------*/
/*---                                                          ---*/
/*----------------------------------------------------------------*/

/* Note this needs to be compiled with -fno-strict-aliasing, since it
   contains a whole bunch of calls to lookupFM etc which cast between
   Word and pointer types.  gcc rightly complains this breaks ANSI C
   strict aliasing rules, at -O2.  No complaints at -O, but -O2 gives
   worthwhile performance benefits over -O.
*/

// FIXME catch sync signals (SEGV, basically) and unlock BHL,
// if held.  Otherwise a LOCK-prefixed insn which segfaults 
// gets Helgrind into a total muddle as the BHL will not be
// released after the insn.

// FIXME what is supposed to happen to locks in memory which
// is relocated as a result of client realloc?

// FIXME put referencing ThreadId into Thread and get
// rid of the slow reverse mapping function.

// FIXME accesses to NoAccess areas: change state to Excl?

// FIXME report errors for accesses of NoAccess memory?

// FIXME pth_cond_wait/timedwait wrappers.  Even if these fail,
// the thread still holds the lock.

/* ------------ Debug/trace options ------------ */

// this is:
// shadow_mem_make_NoAccess: 29156 SMs, 1728 scanned
// happens_before_wrk: 1000
// ev__post_thread_join: 3360 SMs, 29 scanned, 252 re-Excls
#define SHOW_EXPENSIVE_STUFF 0

// 0 for silent, 1 for some stuff, 2 for lots of stuff
#define SHOW_EVENTS 0


static void all__sanity_check ( Char* who ); /* fwds */

#define HG_CLI__MALLOC_REDZONE_SZB 16 /* let's say */

// 0 for none, 1 for dump at end of run
#define SHOW_DATA_STRUCTURES 0


/* ------------ Misc comments ------------ */

// FIXME: don't hardwire initial entries for root thread.
// Instead, let the pre_thread_ll_create handler do this.


/*----------------------------------------------------------------*/
/*--- Primary data structures                                  ---*/
/*----------------------------------------------------------------*/

/* Admin linked list of Threads */
static Thread* admin_threads = NULL;

/* Admin linked list of Locks */
static Lock* admin_locks = NULL;

/* Mapping table for core ThreadIds to Thread* */
static Thread** map_threads = NULL; /* Array[VG_N_THREADS] of Thread* */

/* Mapping table for lock guest addresses to Lock* */
static WordFM* map_locks = NULL; /* WordFM LockAddr Lock* */

/* The word-set universes for thread sets and lock sets. */
static WordSetU* univ_tsets = NULL; /* sets of Thread* */
static WordSetU* univ_lsets = NULL; /* sets of Lock* */
static WordSetU* univ_laog  = NULL; /* sets of Lock*, for LAOG */

/* never changed; we only care about its address.  Is treated as if it
   was a standard userspace lock.  Also we have a Lock* describing it
   so it can participate in lock sets in the usual way. */
static Int   __bus_lock = 0;
static Lock* __bus_lock_Lock = NULL;


/*----------------------------------------------------------------*/
/*--- Simple helpers for the data structures                   ---*/
/*----------------------------------------------------------------*/

static UWord stats__lockN_acquires = 0;
static UWord stats__lockN_releases = 0;

static
ThreadId map_threads_maybe_reverse_lookup_SLOW ( Thread* thr ); /*fwds*/

/* --------- Constructors --------- */

static Thread* mk_Thread ( Thr* hbthr ) {
   static Int indx      = 1;
   Thread* thread       = HG_(zalloc)( "hg.mk_Thread.1", sizeof(Thread) );
   thread->locksetA     = HG_(emptyWS)( univ_lsets );
   thread->locksetW     = HG_(emptyWS)( univ_lsets );
   thread->magic        = Thread_MAGIC;
   thread->hbthr        = hbthr;
   thread->coretid      = VG_INVALID_THREADID;
   thread->created_at   = NULL;
   thread->announced    = False;
   thread->errmsg_index = indx++;
   thread->admin        = admin_threads;
   admin_threads        = thread;
   return thread;
}

// Make a new lock which is unlocked (hence ownerless)
static Lock* mk_LockN ( LockKind kind, Addr guestaddr ) {
   static ULong unique = 0;
   Lock* lock             = HG_(zalloc)( "hg.mk_Lock.1", sizeof(Lock) );
   lock->admin            = admin_locks;
   lock->unique           = unique++;
   lock->magic            = LockN_MAGIC;
   lock->appeared_at      = NULL;
   lock->acquired_at      = NULL;
   lock->hbso             = libhb_so_alloc();
   lock->guestaddr        = guestaddr;
   lock->kind             = kind;
   lock->heldW            = False;
   lock->heldBy           = NULL;
   tl_assert(HG_(is_sane_LockN)(lock));
   admin_locks            = lock;
   return lock;
}

/* Release storage for a Lock.  Also release storage in .heldBy, if
   any. */
static void del_LockN ( Lock* lk ) 
{
   tl_assert(HG_(is_sane_LockN)(lk));
   tl_assert(lk->hbso);
   libhb_so_dealloc(lk->hbso);
   if (lk->heldBy)
      VG_(deleteBag)( lk->heldBy );
   VG_(memset)(lk, 0xAA, sizeof(*lk));
   HG_(free)(lk);
}

/* Update 'lk' to reflect that 'thr' now has a write-acquisition of
   it.  This is done strictly: only combinations resulting from
   correct program and libpthread behaviour are allowed. */
static void lockN_acquire_writer ( Lock* lk, Thread* thr ) 
{
   tl_assert(HG_(is_sane_LockN)(lk));
   tl_assert(HG_(is_sane_Thread)(thr));

   stats__lockN_acquires++;

   /* EXPOSITION only */
   /* We need to keep recording snapshots of where the lock was
      acquired, so as to produce better lock-order error messages. */
   if (lk->acquired_at == NULL) {
      ThreadId tid;
      tl_assert(lk->heldBy == NULL);
      tid = map_threads_maybe_reverse_lookup_SLOW(thr);
      lk->acquired_at
         = VG_(record_ExeContext)(tid, 0/*first_ip_delta*/);
   } else {
      tl_assert(lk->heldBy != NULL);
   }
   /* end EXPOSITION only */

   switch (lk->kind) {
      case LK_nonRec:
      case_LK_nonRec:
         tl_assert(lk->heldBy == NULL); /* can't w-lock recursively */
         tl_assert(!lk->heldW);
         lk->heldW  = True;
         lk->heldBy = VG_(newBag)( HG_(zalloc), "hg.lNaw.1", HG_(free) );
         VG_(addToBag)( lk->heldBy, (Word)thr );
         break;
      case LK_mbRec:
         if (lk->heldBy == NULL)
            goto case_LK_nonRec;
         /* 2nd and subsequent locking of a lock by its owner */
         tl_assert(lk->heldW);
         /* assert: lk is only held by one thread .. */
         tl_assert(VG_(sizeUniqueBag(lk->heldBy)) == 1);
         /* assert: .. and that thread is 'thr'. */
         tl_assert(VG_(elemBag)(lk->heldBy, (Word)thr)
                   == VG_(sizeTotalBag)(lk->heldBy));
         VG_(addToBag)(lk->heldBy, (Word)thr);
         break;
      case LK_rdwr:
         tl_assert(lk->heldBy == NULL && !lk->heldW); /* must be unheld */
         goto case_LK_nonRec;
      default: 
         tl_assert(0);
  }
  tl_assert(HG_(is_sane_LockN)(lk));
}

static void lockN_acquire_reader ( Lock* lk, Thread* thr )
{
   tl_assert(HG_(is_sane_LockN)(lk));
   tl_assert(HG_(is_sane_Thread)(thr));
   /* can only add reader to a reader-writer lock. */
   tl_assert(lk->kind == LK_rdwr);
   /* lk must be free or already r-held. */
   tl_assert(lk->heldBy == NULL 
             || (lk->heldBy != NULL && !lk->heldW));

   stats__lockN_acquires++;

   /* EXPOSITION only */
   /* We need to keep recording snapshots of where the lock was
      acquired, so as to produce better lock-order error messages. */
   if (lk->acquired_at == NULL) {
      ThreadId tid;
      tl_assert(lk->heldBy == NULL);
      tid = map_threads_maybe_reverse_lookup_SLOW(thr);
      lk->acquired_at
         = VG_(record_ExeContext)(tid, 0/*first_ip_delta*/);
   } else {
      tl_assert(lk->heldBy != NULL);
   }
   /* end EXPOSITION only */

   if (lk->heldBy) {
      VG_(addToBag)(lk->heldBy, (Word)thr);
   } else {
      lk->heldW  = False;
      lk->heldBy = VG_(newBag)( HG_(zalloc), "hg.lNar.1", HG_(free) );
      VG_(addToBag)( lk->heldBy, (Word)thr );
   }
   tl_assert(!lk->heldW);
   tl_assert(HG_(is_sane_LockN)(lk));
}

/* Update 'lk' to reflect a release of it by 'thr'.  This is done
   strictly: only combinations resulting from correct program and
   libpthread behaviour are allowed. */

static void lockN_release ( Lock* lk, Thread* thr )
{
   Bool b;
   tl_assert(HG_(is_sane_LockN)(lk));
   tl_assert(HG_(is_sane_Thread)(thr));
   /* lock must be held by someone */
   tl_assert(lk->heldBy);
   stats__lockN_releases++;
   /* Remove it from the holder set */
   b = VG_(delFromBag)(lk->heldBy, (Word)thr);
   /* thr must actually have been a holder of lk */
   tl_assert(b);
   /* normalise */
   tl_assert(lk->acquired_at);
   if (VG_(isEmptyBag)(lk->heldBy)) {
      VG_(deleteBag)(lk->heldBy);
      lk->heldBy      = NULL;
      lk->heldW       = False;
      lk->acquired_at = NULL;
   }
   tl_assert(HG_(is_sane_LockN)(lk));
}

static void remove_Lock_from_locksets_of_all_owning_Threads( Lock* lk )
{
   Thread* thr;
   if (!lk->heldBy) {
      tl_assert(!lk->heldW);
      return;
   }
   /* for each thread that holds this lock do ... */
   VG_(initIterBag)( lk->heldBy );
   while (VG_(nextIterBag)( lk->heldBy, (Word*)&thr, NULL )) {
      tl_assert(HG_(is_sane_Thread)(thr));
      tl_assert(HG_(elemWS)( univ_lsets,
                             thr->locksetA, (Word)lk ));
      thr->locksetA
         = HG_(delFromWS)( univ_lsets, thr->locksetA, (Word)lk );

      if (lk->heldW) {
         tl_assert(HG_(elemWS)( univ_lsets,
                                thr->locksetW, (Word)lk ));
         thr->locksetW
            = HG_(delFromWS)( univ_lsets, thr->locksetW, (Word)lk );
      }
   }
   VG_(doneIterBag)( lk->heldBy );
}


/*----------------------------------------------------------------*/
/*--- Print out the primary data structures                    ---*/
/*----------------------------------------------------------------*/

//static WordSetID del_BHL ( WordSetID lockset ); /* fwds */

#define PP_THREADS      (1<<1)
#define PP_LOCKS        (1<<2)
#define PP_ALL (PP_THREADS | PP_LOCKS)


static const Int sHOW_ADMIN = 0;

static void space ( Int n )
{
   Int  i;
   Char spaces[128+1];
   tl_assert(n >= 0 && n < 128);
   if (n == 0)
      return;
   for (i = 0; i < n; i++)
      spaces[i] = ' ';
   spaces[i] = 0;
   tl_assert(i < 128+1);
   VG_(printf)("%s", spaces);
}

static void pp_Thread ( Int d, Thread* t )
{
   space(d+0); VG_(printf)("Thread %p {\n", t);
   if (sHOW_ADMIN) {
   space(d+3); VG_(printf)("admin    %p\n",   t->admin);
   space(d+3); VG_(printf)("magic    0x%x\n", (UInt)t->magic);
   }
   space(d+3); VG_(printf)("locksetA %d\n",   (Int)t->locksetA);
   space(d+3); VG_(printf)("locksetW %d\n",   (Int)t->locksetW);
   space(d+0); VG_(printf)("}\n");
}

static void pp_admin_threads ( Int d )
{
   Int     i, n;
   Thread* t;
   for (n = 0, t = admin_threads;  t;  n++, t = t->admin) {
      /* nothing */
   }
   space(d); VG_(printf)("admin_threads (%d records) {\n", n);
   for (i = 0, t = admin_threads;  t;  i++, t = t->admin) {
      if (0) {
         space(n); 
         VG_(printf)("admin_threads record %d of %d:\n", i, n);
      }
      pp_Thread(d+3, t);
   }
   space(d); VG_(printf)("}\n");
}

static void pp_map_threads ( Int d )
{
   Int i, n = 0;
   space(d); VG_(printf)("map_threads ");
   for (i = 0; i < VG_N_THREADS; i++) {
      if (map_threads[i] != NULL)
         n++;
   }
   VG_(printf)("(%d entries) {\n", n);
   for (i = 0; i < VG_N_THREADS; i++) {
      if (map_threads[i] == NULL)
         continue;
      space(d+3);
      VG_(printf)("coretid %d -> Thread %p\n", i, map_threads[i]);
   }
   space(d); VG_(printf)("}\n");
}

static const HChar* show_LockKind ( LockKind lkk ) {
   switch (lkk) {
      case LK_mbRec:  return "mbRec";
      case LK_nonRec: return "nonRec";
      case LK_rdwr:   return "rdwr";
      default:        tl_assert(0);
   }
}

static void pp_Lock ( Int d, Lock* lk )
{
   space(d+0); VG_(printf)("Lock %p (ga %#lx) {\n", lk, lk->guestaddr);
   if (sHOW_ADMIN) {
      space(d+3); VG_(printf)("admin  %p\n",   lk->admin);
      space(d+3); VG_(printf)("magic  0x%x\n", (UInt)lk->magic);
   }
   space(d+3); VG_(printf)("unique %llu\n", lk->unique);
   space(d+3); VG_(printf)("kind   %s\n", show_LockKind(lk->kind));
   space(d+3); VG_(printf)("heldW  %s\n", lk->heldW ? "yes" : "no");
   space(d+3); VG_(printf)("heldBy %p", lk->heldBy);
   if (lk->heldBy) {
      Thread* thr;
      Word    count;
      VG_(printf)(" { ");
      VG_(initIterBag)( lk->heldBy );
      while (VG_(nextIterBag)( lk->heldBy, (Word*)&thr, &count ))
         VG_(printf)("%lu:%p ", count, thr);
      VG_(doneIterBag)( lk->heldBy );
      VG_(printf)("}");
   }
   VG_(printf)("\n");
   space(d+0); VG_(printf)("}\n");
}

static void pp_admin_locks ( Int d )
{
   Int   i, n;
   Lock* lk;
   for (n = 0, lk = admin_locks;  lk;  n++, lk = lk->admin) {
      /* nothing */
   }
   space(d); VG_(printf)("admin_locks (%d records) {\n", n);
   for (i = 0, lk = admin_locks;  lk;  i++, lk = lk->admin) {
      if (0) {
         space(n); 
         VG_(printf)("admin_locks record %d of %d:\n", i, n);
      }
      pp_Lock(d+3, lk);
   }
   space(d); VG_(printf)("}\n");
}

static void pp_map_locks ( Int d )
{
   void* gla;
   Lock* lk;
   space(d); VG_(printf)("map_locks (%d entries) {\n",
                         (Int)VG_(sizeFM)( map_locks ));
   VG_(initIterFM)( map_locks );
   while (VG_(nextIterFM)( map_locks, (Word*)&gla,
                                      (Word*)&lk )) {
      space(d+3);
      VG_(printf)("guest %p -> Lock %p\n", gla, lk);
   }
   VG_(doneIterFM)( map_locks );
   space(d); VG_(printf)("}\n");
}

static void pp_everything ( Int flags, Char* caller )
{
   Int d = 0;
   VG_(printf)("\n");
   VG_(printf)("All_Data_Structures (caller = \"%s\") {\n", caller);
   if (flags & PP_THREADS) {
      VG_(printf)("\n");
      pp_admin_threads(d+3);
      VG_(printf)("\n");
      pp_map_threads(d+3);
   }
   if (flags & PP_LOCKS) {
      VG_(printf)("\n");
      pp_admin_locks(d+3);
      VG_(printf)("\n");
      pp_map_locks(d+3);
   }

   VG_(printf)("\n");
   VG_(printf)("}\n");
   VG_(printf)("\n");
}

#undef SHOW_ADMIN


/*----------------------------------------------------------------*/
/*--- Initialise the primary data structures                   ---*/
/*----------------------------------------------------------------*/

static void initialise_data_structures ( Thr* hbthr_root )
{
   Thread*   thr;

   /* Get everything initialised and zeroed. */
   tl_assert(admin_threads == NULL);
   tl_assert(admin_locks == NULL);

   tl_assert(sizeof(Addr) == sizeof(Word));

   tl_assert(map_threads == NULL);
   map_threads = HG_(zalloc)( "hg.ids.1", VG_N_THREADS * sizeof(Thread*) );
   tl_assert(map_threads != NULL);

   tl_assert(sizeof(Addr) == sizeof(Word));
   tl_assert(map_locks == NULL);
   map_locks = VG_(newFM)( HG_(zalloc), "hg.ids.2", HG_(free), 
                           NULL/*unboxed Word cmp*/);
   tl_assert(map_locks != NULL);

   __bus_lock_Lock = mk_LockN( LK_nonRec, (Addr)&__bus_lock );
   tl_assert(HG_(is_sane_LockN)(__bus_lock_Lock));
   VG_(addToFM)( map_locks, (Word)&__bus_lock, (Word)__bus_lock_Lock );

   tl_assert(univ_tsets == NULL);
   univ_tsets = HG_(newWordSetU)( HG_(zalloc), "hg.ids.3", HG_(free),
                                  8/*cacheSize*/ );
   tl_assert(univ_tsets != NULL);

   tl_assert(univ_lsets == NULL);
   univ_lsets = HG_(newWordSetU)( HG_(zalloc), "hg.ids.4", HG_(free),
                                  8/*cacheSize*/ );
   tl_assert(univ_lsets != NULL);

   tl_assert(univ_laog == NULL);
   univ_laog = HG_(newWordSetU)( HG_(zalloc), "hg.ids.5 (univ_laog)",
                                 HG_(free), 24/*cacheSize*/ );
   tl_assert(univ_laog != NULL);

   /* Set up entries for the root thread */
   // FIXME: this assumes that the first real ThreadId is 1

   /* a Thread for the new thread ... */
   thr = mk_Thread(hbthr_root);
   thr->coretid = 1; /* FIXME: hardwires an assumption about the
                        identity of the root thread. */
   tl_assert( libhb_get_Thr_opaque(hbthr_root) == NULL );
   libhb_set_Thr_opaque(hbthr_root, thr);

   /* and bind it in the thread-map table. */
   tl_assert(HG_(is_sane_ThreadId)(thr->coretid));
   tl_assert(thr->coretid != VG_INVALID_THREADID);

   map_threads[thr->coretid] = thr;

   tl_assert(VG_INVALID_THREADID == 0);

   /* Mark the new bus lock correctly (to stop the sanity checks
      complaining) */
   tl_assert( sizeof(__bus_lock) == 4 );

   all__sanity_check("initialise_data_structures");
}


/*----------------------------------------------------------------*/
/*--- map_threads :: array[core-ThreadId] of Thread*           ---*/
/*----------------------------------------------------------------*/

/* Doesn't assert if the relevant map_threads entry is NULL. */
static Thread* map_threads_maybe_lookup ( ThreadId coretid )
{
   Thread* thr;
   tl_assert( HG_(is_sane_ThreadId)(coretid) );
   thr = map_threads[coretid];
   return thr;
}

/* Asserts if the relevant map_threads entry is NULL. */
static inline Thread* map_threads_lookup ( ThreadId coretid )
{
   Thread* thr;
   tl_assert( HG_(is_sane_ThreadId)(coretid) );
   thr = map_threads[coretid];
   tl_assert(thr);
   return thr;
}

/* Do a reverse lookup.  Does not assert if 'thr' is not found in
   map_threads. */
static ThreadId map_threads_maybe_reverse_lookup_SLOW ( Thread* thr )
{
   ThreadId tid;
   tl_assert(HG_(is_sane_Thread)(thr));
   /* Check nobody used the invalid-threadid slot */
   tl_assert(VG_INVALID_THREADID >= 0 && VG_INVALID_THREADID < VG_N_THREADS);
   tl_assert(map_threads[VG_INVALID_THREADID] == NULL);
   tid = thr->coretid;
   tl_assert(HG_(is_sane_ThreadId)(tid));
   return tid;
}

/* Do a reverse lookup.  Warning: POTENTIALLY SLOW.  Asserts if 'thr'
   is not found in map_threads. */
static ThreadId map_threads_reverse_lookup_SLOW ( Thread* thr )
{
   ThreadId tid = map_threads_maybe_reverse_lookup_SLOW( thr );
   tl_assert(tid != VG_INVALID_THREADID);
   tl_assert(map_threads[tid]);
   tl_assert(map_threads[tid]->coretid == tid);
   return tid;
}

static void map_threads_delete ( ThreadId coretid )
{
   Thread* thr;
   tl_assert(coretid != 0);
   tl_assert( HG_(is_sane_ThreadId)(coretid) );
   thr = map_threads[coretid];
   tl_assert(thr);
   map_threads[coretid] = NULL;
}


/*----------------------------------------------------------------*/
/*--- map_locks :: WordFM guest-Addr-of-lock Lock*             ---*/
/*----------------------------------------------------------------*/

/* Make sure there is a lock table entry for the given (lock) guest
   address.  If not, create one of the stated 'kind' in unheld state.
   In any case, return the address of the existing or new Lock. */
static 
Lock* map_locks_lookup_or_create ( LockKind lkk, Addr ga, ThreadId tid )
{
   Bool  found;
   Lock* oldlock = NULL;
   tl_assert(HG_(is_sane_ThreadId)(tid));
   found = VG_(lookupFM)( map_locks, 
                          NULL, (Word*)&oldlock, (Word)ga );
   if (!found) {
      Lock* lock = mk_LockN(lkk, ga);
      lock->appeared_at = VG_(record_ExeContext)( tid, 0 );
      tl_assert(HG_(is_sane_LockN)(lock));
      VG_(addToFM)( map_locks, (Word)ga, (Word)lock );
      tl_assert(oldlock == NULL);
      return lock;
   } else {
      tl_assert(oldlock != NULL);
      tl_assert(HG_(is_sane_LockN)(oldlock));
      tl_assert(oldlock->guestaddr == ga);
      return oldlock;
   }
}

static Lock* map_locks_maybe_lookup ( Addr ga )
{
   Bool  found;
   Lock* lk = NULL;
   found = VG_(lookupFM)( map_locks, NULL, (Word*)&lk, (Word)ga );
   tl_assert(found  ?  lk != NULL  :  lk == NULL);
   return lk;
}

static void map_locks_delete ( Addr ga )
{
   Addr  ga2 = 0;
   Lock* lk  = NULL;
   VG_(delFromFM)( map_locks,
                   (Word*)&ga2, (Word*)&lk, (Word)ga );
   /* delFromFM produces the val which is being deleted, if it is
      found.  So assert it is non-null; that in effect asserts that we
      are deleting a (ga, Lock) pair which actually exists. */
   tl_assert(lk != NULL);
   tl_assert(ga2 == ga);
}



/*----------------------------------------------------------------*/
/*--- Sanity checking the data structures                      ---*/
/*----------------------------------------------------------------*/

static UWord stats__sanity_checks = 0;

static void laog__sanity_check ( Char* who ); /* fwds */

/* REQUIRED INVARIANTS:

   Thread vs Segment/Lock/SecMaps

      for each t in Threads {

         // Thread.lockset: each element is really a valid Lock

         // Thread.lockset: each Lock in set is actually held by that thread
         for lk in Thread.lockset 
            lk == LockedBy(t)

         // Thread.csegid is a valid SegmentID
         // and the associated Segment has .thr == t

      }

      all thread Locksets are pairwise empty under intersection
      (that is, no lock is claimed to be held by more than one thread)
      -- this is guaranteed if all locks in locksets point back to their
      owner threads

   Lock vs Thread/Segment/SecMaps

      for each entry (gla, la) in map_locks
         gla == la->guest_addr

      for each lk in Locks {

         lk->tag is valid
         lk->guest_addr does not have shadow state NoAccess
         if lk == LockedBy(t), then t->lockset contains lk
         if lk == UnlockedBy(segid) then segid is valid SegmentID
             and can be mapped to a valid Segment(seg)
             and seg->thr->lockset does not contain lk
         if lk == UnlockedNew then (no lockset contains lk)

         secmaps for lk has .mbHasLocks == True

      }

   Segment vs Thread/Lock/SecMaps

      the Segment graph is a dag (no cycles)
      all of the Segment graph must be reachable from the segids
         mentioned in the Threads

      for seg in Segments {

         seg->thr is a sane Thread

      }

   SecMaps vs Segment/Thread/Lock

      for sm in SecMaps {

         sm properly aligned
         if any shadow word is ShR or ShM then .mbHasShared == True

         for each Excl(segid) state
            map_segments_lookup maps to a sane Segment(seg)
         for each ShM/ShR(tsetid,lsetid) state
            each lk in lset is a valid Lock
            each thr in tset is a valid thread, which is non-dead

      }
*/


/* Return True iff 'thr' holds 'lk' in some mode. */
static Bool thread_is_a_holder_of_Lock ( Thread* thr, Lock* lk )
{
   if (lk->heldBy)
      return VG_(elemBag)( lk->heldBy, (Word)thr ) > 0;
   else
      return False;
}

/* Sanity check Threads, as far as possible */
__attribute__((noinline))
static void threads__sanity_check ( Char* who )
{
#define BAD(_str) do { how = (_str); goto bad; } while (0)
   Char*     how = "no error";
   Thread*   thr;
   WordSetID wsA, wsW;
   UWord*    ls_words;
   Word      ls_size, i;
   Lock*     lk;
   for (thr = admin_threads; thr; thr = thr->admin) {
      if (!HG_(is_sane_Thread)(thr)) BAD("1");
      wsA = thr->locksetA;
      wsW = thr->locksetW;
      // locks held in W mode are a subset of all locks held
      if (!HG_(isSubsetOf)( univ_lsets, wsW, wsA )) BAD("7");
      HG_(getPayloadWS)( &ls_words, &ls_size, univ_lsets, wsA );
      for (i = 0; i < ls_size; i++) {
         lk = (Lock*)ls_words[i];
         // Thread.lockset: each element is really a valid Lock
         if (!HG_(is_sane_LockN)(lk)) BAD("2");
         // Thread.lockset: each Lock in set is actually held by that
         // thread
         if (!thread_is_a_holder_of_Lock(thr,lk)) BAD("3");
      }
   }
   return;
  bad:
   VG_(printf)("threads__sanity_check: who=\"%s\", bad=\"%s\"\n", who, how);
   tl_assert(0);
#undef BAD
}


/* Sanity check Locks, as far as possible */
__attribute__((noinline))
static void locks__sanity_check ( Char* who )
{
#define BAD(_str) do { how = (_str); goto bad; } while (0)
   Char*     how = "no error";
   Addr      gla;
   Lock*     lk;
   Int       i;
   // # entries in admin_locks == # entries in map_locks
   for (i = 0, lk = admin_locks;  lk;  i++, lk = lk->admin)
      ;
   if (i != VG_(sizeFM)(map_locks)) BAD("1");
   // for each entry (gla, lk) in map_locks
   //      gla == lk->guest_addr
   VG_(initIterFM)( map_locks );
   while (VG_(nextIterFM)( map_locks,
                           (Word*)&gla, (Word*)&lk )) {
      if (lk->guestaddr != gla) BAD("2");
   }
   VG_(doneIterFM)( map_locks );
   // scan through admin_locks ...
   for (lk = admin_locks; lk; lk = lk->admin) {
      // lock is sane.  Quite comprehensive, also checks that
      // referenced (holder) threads are sane.
      if (!HG_(is_sane_LockN)(lk)) BAD("3");
      // map_locks binds guest address back to this lock
      if (lk != map_locks_maybe_lookup(lk->guestaddr)) BAD("4");
      // look at all threads mentioned as holders of this lock.  Ensure
      // this lock is mentioned in their locksets.
      if (lk->heldBy) {
         Thread* thr;
         Word    count;
         VG_(initIterBag)( lk->heldBy );
         while (VG_(nextIterBag)( lk->heldBy, 
                                  (Word*)&thr, &count )) {
            // HG_(is_sane_LockN) above ensures these
            tl_assert(count >= 1);
            tl_assert(HG_(is_sane_Thread)(thr));
            if (!HG_(elemWS)(univ_lsets, thr->locksetA, (Word)lk)) 
               BAD("6");
            // also check the w-only lockset
            if (lk->heldW 
                && !HG_(elemWS)(univ_lsets, thr->locksetW, (Word)lk)) 
               BAD("7");
            if ((!lk->heldW)
                && HG_(elemWS)(univ_lsets, thr->locksetW, (Word)lk)) 
               BAD("8");
         }
         VG_(doneIterBag)( lk->heldBy );
      } else {
         /* lock not held by anybody */
         if (lk->heldW) BAD("9"); /* should be False if !heldBy */
         // since lk is unheld, then (no lockset contains lk)
         // hmm, this is really too expensive to check.  Hmm.
      }
   }

   return;
  bad:
   VG_(printf)("locks__sanity_check: who=\"%s\", bad=\"%s\"\n", who, how);
   tl_assert(0);
#undef BAD
}


static void all_except_Locks__sanity_check ( Char* who ) {
   stats__sanity_checks++;
   if (0) VG_(printf)("all_except_Locks__sanity_check(%s)\n", who);
   threads__sanity_check(who);
   laog__sanity_check(who);
}
static void all__sanity_check ( Char* who ) {
   all_except_Locks__sanity_check(who);
   locks__sanity_check(who);
}


/*----------------------------------------------------------------*/
/*--- the core memory state machine (msm__* functions)         ---*/
/*----------------------------------------------------------------*/

//static WordSetID add_BHL ( WordSetID lockset ) {
//   return HG_(addToWS)( univ_lsets, lockset, (Word)__bus_lock_Lock );
//}
//static WordSetID del_BHL ( WordSetID lockset ) {
//   return HG_(delFromWS)( univ_lsets, lockset, (Word)__bus_lock_Lock );
//}


///* Last-lock-lossage records.  This mechanism exists to help explain
//   to programmers why we are complaining about a race.  The idea is to
//   monitor all lockset transitions.  When a previously nonempty
//   lockset becomes empty, the lock(s) that just disappeared (the
//   "lossage") are the locks that have consistently protected the
//   location (ga_of_access) in question for the longest time.  Most of
//   the time the lossage-set is a single lock.  Because the
//   lossage-lock is the one that has survived longest, there is there
//   is a good chance that it is indeed the lock that the programmer
//   intended to use to protect the location.
//
//   Note that we cannot in general just look at the lossage set when we
//   see a transition to ShM(...,empty-set), because a transition to an
//   empty lockset can happen arbitrarily far before the point where we
//   want to report an error.  This is in the case where there are many
//   transitions ShR -> ShR, all with an empty lockset, and only later
//   is there a transition to ShM.  So what we want to do is note the
//   lossage lock at the point where a ShR -> ShR transition empties out
//   the lockset, so we can present it later if there should be a
//   transition to ShM.
//
//   So this function finds such transitions.  For each, it associates
//   in ga_to_lastlock, the guest address and the lossage lock.  In fact
//   we do not record the Lock* directly as that may disappear later,
//   but instead the ExeContext inside the Lock which says where it was
//   initialised or first locked.  ExeContexts are permanent so keeping
//   them indefinitely is safe.
//
//   A boring detail: the hardware bus lock is not interesting in this
//   respect, so we first remove that from the pre/post locksets.
//*/
//
//static UWord stats__ga_LL_adds = 0;
//
//static WordFM* ga_to_lastlock = NULL; /* GuestAddr -> ExeContext* */
//
//static 
//void record_last_lock_lossage ( Addr ga_of_access,
//                                WordSetID lset_old, WordSetID lset_new )
//{
//   Lock* lk;
//   Int   card_old, card_new;
//
//   tl_assert(lset_old != lset_new);
//
//   if (0) VG_(printf)("XX1: %d (card %ld) -> %d (card %ld) %#lx\n",
//                      (Int)lset_old, 
//                      HG_(cardinalityWS)(univ_lsets,lset_old),
//                      (Int)lset_new, 
//                      HG_(cardinalityWS)(univ_lsets,lset_new),
//                      ga_of_access );
//
//   /* This is slow, but at least it's simple.  The bus hardware lock
//      just confuses the logic, so remove it from the locksets we're
//      considering before doing anything else. */
//   lset_new = del_BHL( lset_new );
//
//   if (!HG_(isEmptyWS)( univ_lsets, lset_new )) {
//      /* The post-transition lock set is not empty.  So we are not
//         interested.  We're only interested in spotting transitions
//         that make locksets become empty. */
//      return;
//   }
//
//   /* lset_new is now empty */
//   card_new = HG_(cardinalityWS)( univ_lsets, lset_new );
//   tl_assert(card_new == 0);
//
//   lset_old = del_BHL( lset_old );
//   card_old = HG_(cardinalityWS)( univ_lsets, lset_old );
//
//   if (0) VG_(printf)(" X2: %d (card %d) -> %d (card %d)\n",
//                      (Int)lset_old, card_old, (Int)lset_new, card_new );
//
//   if (card_old == 0) {
//      /* The old lockset was also empty.  Not interesting. */
//      return;
//   }
//
//   tl_assert(card_old > 0);
//   tl_assert(!HG_(isEmptyWS)( univ_lsets, lset_old ));
//
//   /* Now we know we've got a transition from a nonempty lockset to an
//      empty one.  So lset_old must be the set of locks lost.  Record
//      some details.  If there is more than one element in the lossage
//      set, just choose one arbitrarily -- not the best, but at least
//      it's simple. */
//
//   lk = (Lock*)HG_(anyElementOfWS)( univ_lsets, lset_old );
//   if (0) VG_(printf)("lossage %ld %p\n",
//                      HG_(cardinalityWS)( univ_lsets, lset_old), lk );
//   if (lk->appeared_at) {
//      if (ga_to_lastlock == NULL)
//         ga_to_lastlock = VG_(newFM)( HG_(zalloc), "hg.rlll.1", HG_(free), NULL );
//      VG_(addToFM)( ga_to_lastlock, ga_of_access, (Word)lk->appeared_at );
//      stats__ga_LL_adds++;
//   }
//}
//
///* This queries the table (ga_to_lastlock) made by
//   record_last_lock_lossage, when constructing error messages.  It
//   attempts to find the ExeContext of the allocation or initialisation
//   point for the lossage lock associated with 'ga'. */
//
//static ExeContext* maybe_get_lastlock_initpoint ( Addr ga ) 
//{
//   ExeContext* ec_hint = NULL;
//   if (ga_to_lastlock != NULL 
//       && VG_(lookupFM)(ga_to_lastlock, 
//                        NULL, (Word*)&ec_hint, ga)) {
//      tl_assert(ec_hint != NULL);
//      return ec_hint;
//   } else {
//      return NULL;
//   }
//}


/*----------------------------------------------------------------*/
/*--- Shadow value and address range handlers                  ---*/
/*----------------------------------------------------------------*/

static void laog__pre_thread_acquires_lock ( Thread*, Lock* ); /* fwds */
//static void laog__handle_lock_deletions    ( WordSetID ); /* fwds */
static inline Thread* get_current_Thread ( void ); /* fwds */
__attribute__((noinline))
static void laog__handle_one_lock_deletion ( Lock* lk ); /* fwds */


/* Block-copy states (needed for implementing realloc()). */
static void shadow_mem_copy_range ( Addr src, Addr dst, SizeT len )
{
   libhb_copy_shadow_state( src, dst, len );
}

static void shadow_mem_read_range ( Thread* thr, Addr a, SizeT len )
{
   Thr*     hbthr = thr->hbthr;
   tl_assert(hbthr);
   LIBHB_READ_N(hbthr, a, len);
}

static void shadow_mem_write_range ( Thread* thr, Addr a, SizeT len ) {
   Thr*     hbthr = thr->hbthr;
   tl_assert(hbthr);
   LIBHB_WRITE_N(hbthr, a, len);
}

static void shadow_mem_make_New ( Thread* thr, Addr a, SizeT len )
{
   libhb_range_new( thr->hbthr, a, len );
}

static void shadow_mem_make_NoAccess ( Thread* thr, Addr aIN, SizeT len )
{
   if (0 && len > 500)
      VG_(printf)("make NoAccess ( %#lx, %ld )\n", aIN, len );
   libhb_range_noaccess( thr->hbthr, aIN, len );
}


/*----------------------------------------------------------------*/
/*--- Event handlers (evh__* functions)                        ---*/
/*--- plus helpers (evhH__* functions)                         ---*/
/*----------------------------------------------------------------*/

/*--------- Event handler helpers (evhH__* functions) ---------*/

/* Create a new segment for 'thr', making it depend (.prev) on its
   existing segment, bind together the SegmentID and Segment, and
   return both of them.  Also update 'thr' so it references the new
   Segment. */
//zz static 
//zz void evhH__start_new_segment_for_thread ( /*OUT*/SegmentID* new_segidP,
//zz                                           /*OUT*/Segment** new_segP,
//zz                                           Thread* thr )
//zz {
//zz    Segment* cur_seg;
//zz    tl_assert(new_segP);
//zz    tl_assert(new_segidP);
//zz    tl_assert(HG_(is_sane_Thread)(thr));
//zz    cur_seg = map_segments_lookup( thr->csegid );
//zz    tl_assert(cur_seg);
//zz    tl_assert(cur_seg->thr == thr); /* all sane segs should point back
//zz                                       at their owner thread. */
//zz    *new_segP = mk_Segment( thr, cur_seg, NULL/*other*/ );
//zz    *new_segidP = alloc_SegmentID();
//zz    map_segments_add( *new_segidP, *new_segP );
//zz    thr->csegid = *new_segidP;
//zz }


/* The lock at 'lock_ga' has acquired a writer.  Make all necessary
   updates, and also do all possible error checks. */
static 
void evhH__post_thread_w_acquires_lock ( Thread* thr, 
                                         LockKind lkk, Addr lock_ga )
{
   Lock* lk; 

   /* Basically what we need to do is call lockN_acquire_writer.
      However, that will barf if any 'invalid' lock states would
      result.  Therefore check before calling.  Side effect is that
      'HG_(is_sane_LockN)(lk)' is both a pre- and post-condition of this
      routine. 

      Because this routine is only called after successful lock
      acquisition, we should not be asked to move the lock into any
      invalid states.  Requests to do so are bugs in libpthread, since
      that should have rejected any such requests. */

   tl_assert(HG_(is_sane_Thread)(thr));
   /* Try to find the lock.  If we can't, then create a new one with
      kind 'lkk'. */
   lk = map_locks_lookup_or_create( 
           lkk, lock_ga, map_threads_reverse_lookup_SLOW(thr) );
   tl_assert( HG_(is_sane_LockN)(lk) );

   /* check libhb level entities exist */
   tl_assert(thr->hbthr);
   tl_assert(lk->hbso);

   if (lk->heldBy == NULL) {
      /* the lock isn't held.  Simple. */
      tl_assert(!lk->heldW);
      lockN_acquire_writer( lk, thr );
      /* acquire a dependency from the lock's VCs */
      libhb_so_recv( thr->hbthr, lk->hbso, True/*strong_recv*/ );
      goto noerror;
   }

   /* So the lock is already held.  If held as a r-lock then
      libpthread must be buggy. */
   tl_assert(lk->heldBy);
   if (!lk->heldW) {
      HG_(record_error_Misc)(
         thr, "Bug in libpthread: write lock "
              "granted on rwlock which is currently rd-held");
      goto error;
   }

   /* So the lock is held in w-mode.  If it's held by some other
      thread, then libpthread must be buggy. */
   tl_assert(VG_(sizeUniqueBag)(lk->heldBy) == 1); /* from precondition */

   if (thr != (Thread*)VG_(anyElementOfBag)(lk->heldBy)) {
      HG_(record_error_Misc)(
         thr, "Bug in libpthread: write lock "
              "granted on mutex/rwlock which is currently "
              "wr-held by a different thread");
      goto error;
   }

   /* So the lock is already held in w-mode by 'thr'.  That means this
      is an attempt to lock it recursively, which is only allowable
      for LK_mbRec kinded locks.  Since this routine is called only
      once the lock has been acquired, this must also be a libpthread
      bug. */
   if (lk->kind != LK_mbRec) {
      HG_(record_error_Misc)(
         thr, "Bug in libpthread: recursive write lock "
              "granted on mutex/wrlock which does not "
              "support recursion");
      goto error;
   }

   /* So we are recursively re-locking a lock we already w-hold. */
   lockN_acquire_writer( lk, thr );
   /* acquire a dependency from the lock's VC.  Probably pointless,
      but also harmless. */
   libhb_so_recv( thr->hbthr, lk->hbso, True/*strong_recv*/ );
   goto noerror;

  noerror:
   /* check lock order acquisition graph, and update.  This has to
      happen before the lock is added to the thread's locksetA/W. */
   laog__pre_thread_acquires_lock( thr, lk );
   /* update the thread's held-locks set */
   thr->locksetA = HG_(addToWS)( univ_lsets, thr->locksetA, (Word)lk );
   thr->locksetW = HG_(addToWS)( univ_lsets, thr->locksetW, (Word)lk );
   /* fall through */

  error:
   tl_assert(HG_(is_sane_LockN)(lk));
}


/* The lock at 'lock_ga' has acquired a reader.  Make all necessary
   updates, and also do all possible error checks. */
static 
void evhH__post_thread_r_acquires_lock ( Thread* thr, 
                                         LockKind lkk, Addr lock_ga )
{
   Lock* lk; 

   /* Basically what we need to do is call lockN_acquire_reader.
      However, that will barf if any 'invalid' lock states would
      result.  Therefore check before calling.  Side effect is that
      'HG_(is_sane_LockN)(lk)' is both a pre- and post-condition of this
      routine. 

      Because this routine is only called after successful lock
      acquisition, we should not be asked to move the lock into any
      invalid states.  Requests to do so are bugs in libpthread, since
      that should have rejected any such requests. */

   tl_assert(HG_(is_sane_Thread)(thr));
   /* Try to find the lock.  If we can't, then create a new one with
      kind 'lkk'.  Only a reader-writer lock can be read-locked,
      hence the first assertion. */
   tl_assert(lkk == LK_rdwr);
   lk = map_locks_lookup_or_create( 
           lkk, lock_ga, map_threads_reverse_lookup_SLOW(thr) );
   tl_assert( HG_(is_sane_LockN)(lk) );

   /* check libhb level entities exist */
   tl_assert(thr->hbthr);
   tl_assert(lk->hbso);

   if (lk->heldBy == NULL) {
      /* the lock isn't held.  Simple. */
      tl_assert(!lk->heldW);
      lockN_acquire_reader( lk, thr );
      /* acquire a dependency from the lock's VC */
      libhb_so_recv( thr->hbthr, lk->hbso, False/*!strong_recv*/ );
      goto noerror;
   }

   /* So the lock is already held.  If held as a w-lock then
      libpthread must be buggy. */
   tl_assert(lk->heldBy);
   if (lk->heldW) {
      HG_(record_error_Misc)( thr, "Bug in libpthread: read lock "
                                   "granted on rwlock which is "
                                   "currently wr-held");
      goto error;
   }

   /* Easy enough.  In short anybody can get a read-lock on a rwlock
      provided it is either unlocked or already in rd-held. */
   lockN_acquire_reader( lk, thr );
   /* acquire a dependency from the lock's VC.  Probably pointless,
      but also harmless. */
   libhb_so_recv( thr->hbthr, lk->hbso, False/*!strong_recv*/ );
   goto noerror;

  noerror:
   /* check lock order acquisition graph, and update.  This has to
      happen before the lock is added to the thread's locksetA/W. */
   laog__pre_thread_acquires_lock( thr, lk );
   /* update the thread's held-locks set */
   thr->locksetA = HG_(addToWS)( univ_lsets, thr->locksetA, (Word)lk );
   /* but don't update thr->locksetW, since lk is only rd-held */
   /* fall through */

  error:
   tl_assert(HG_(is_sane_LockN)(lk));
}


/* The lock at 'lock_ga' is just about to be unlocked.  Make all
   necessary updates, and also do all possible error checks. */
static 
void evhH__pre_thread_releases_lock ( Thread* thr,
                                      Addr lock_ga, Bool isRDWR )
{
   Lock* lock;
   Word  n;
   Bool  was_heldW;

   /* This routine is called prior to a lock release, before
      libpthread has had a chance to validate the call.  Hence we need
      to detect and reject any attempts to move the lock into an
      invalid state.  Such attempts are bugs in the client.

      isRDWR is True if we know from the wrapper context that lock_ga
      should refer to a reader-writer lock, and is False if [ditto]
      lock_ga should refer to a standard mutex. */

   tl_assert(HG_(is_sane_Thread)(thr));
   lock = map_locks_maybe_lookup( lock_ga );

   if (!lock) {
      /* We know nothing about a lock at 'lock_ga'.  Nevertheless
         the client is trying to unlock it.  So complain, then ignore
         the attempt. */
      HG_(record_error_UnlockBogus)( thr, lock_ga );
      return;
   }

   tl_assert(lock->guestaddr == lock_ga);
   tl_assert(HG_(is_sane_LockN)(lock));

   if (isRDWR && lock->kind != LK_rdwr) {
      HG_(record_error_Misc)( thr, "pthread_rwlock_unlock with a "
                                   "pthread_mutex_t* argument " );
   }
   if ((!isRDWR) && lock->kind == LK_rdwr) {
      HG_(record_error_Misc)( thr, "pthread_mutex_unlock with a "
                                   "pthread_rwlock_t* argument " );
   }

   if (!lock->heldBy) {
      /* The lock is not held.  This indicates a serious bug in the
         client. */
      tl_assert(!lock->heldW);
      HG_(record_error_UnlockUnlocked)( thr, lock );
      tl_assert(!HG_(elemWS)( univ_lsets, thr->locksetA, (Word)lock ));
      tl_assert(!HG_(elemWS)( univ_lsets, thr->locksetW, (Word)lock ));
      goto error;
   }

   /* test just above dominates */
   tl_assert(lock->heldBy);
   was_heldW = lock->heldW;

   /* The lock is held.  Is this thread one of the holders?  If not,
      report a bug in the client. */
   n = VG_(elemBag)( lock->heldBy, (Word)thr );
   tl_assert(n >= 0);
   if (n == 0) {
      /* We are not a current holder of the lock.  This is a bug in
         the guest, and (per POSIX pthread rules) the unlock
         attempt will fail.  So just complain and do nothing
         else. */
      Thread* realOwner = (Thread*)VG_(anyElementOfBag)( lock->heldBy );
      tl_assert(HG_(is_sane_Thread)(realOwner));
      tl_assert(realOwner != thr);
      tl_assert(!HG_(elemWS)( univ_lsets, thr->locksetA, (Word)lock ));
      tl_assert(!HG_(elemWS)( univ_lsets, thr->locksetW, (Word)lock ));
      HG_(record_error_UnlockForeign)( thr, realOwner, lock );
      goto error;
   }

   /* Ok, we hold the lock 'n' times. */
   tl_assert(n >= 1);

   lockN_release( lock, thr );

   n--;
   tl_assert(n >= 0);

   if (n > 0) {
      tl_assert(lock->heldBy);
      tl_assert(n == VG_(elemBag)( lock->heldBy, (Word)thr )); 
      /* We still hold the lock.  So either it's a recursive lock 
         or a rwlock which is currently r-held. */
      tl_assert(lock->kind == LK_mbRec
                || (lock->kind == LK_rdwr && !lock->heldW));
      tl_assert(HG_(elemWS)( univ_lsets, thr->locksetA, (Word)lock ));
      if (lock->heldW)
         tl_assert(HG_(elemWS)( univ_lsets, thr->locksetW, (Word)lock ));
      else
         tl_assert(!HG_(elemWS)( univ_lsets, thr->locksetW, (Word)lock ));
   } else {
      /* n is zero.  This means we don't hold the lock any more.  But
         if it's a rwlock held in r-mode, someone else could still
         hold it.  Just do whatever sanity checks we can. */
      if (lock->kind == LK_rdwr && lock->heldBy) {
         /* It's a rwlock.  We no longer hold it but we used to;
            nevertheless it still appears to be held by someone else.
            The implication is that, prior to this release, it must
            have been shared by us and and whoever else is holding it;
            which in turn implies it must be r-held, since a lock
            can't be w-held by more than one thread. */
         /* The lock is now R-held by somebody else: */
         tl_assert(lock->heldW == False);
      } else {
         /* Normal case.  It's either not a rwlock, or it's a rwlock
            that we used to hold in w-mode (which is pretty much the
            same thing as a non-rwlock.)  Since this transaction is
            atomic (V does not allow multiple threads to run
            simultaneously), it must mean the lock is now not held by
            anybody.  Hence assert for it. */
         /* The lock is now not held by anybody: */
         tl_assert(!lock->heldBy);
         tl_assert(lock->heldW == False);
      }
      //if (lock->heldBy) {
      //   tl_assert(0 == VG_(elemBag)( lock->heldBy, (Word)thr ));
      //}
      /* update this thread's lockset accordingly. */
      thr->locksetA
         = HG_(delFromWS)( univ_lsets, thr->locksetA, (Word)lock );
      thr->locksetW
         = HG_(delFromWS)( univ_lsets, thr->locksetW, (Word)lock );
      /* push our VC into the lock */
      tl_assert(thr->hbthr);
      tl_assert(lock->hbso);
      /* If the lock was previously W-held, then we want to do a
         strong send, and if previously R-held, then a weak send. */
      libhb_so_send( thr->hbthr, lock->hbso, was_heldW );
   }
   /* fall through */

  error:
   tl_assert(HG_(is_sane_LockN)(lock));
}


/* ---------------------------------------------------------- */
/* -------- Event handlers proper (evh__* functions) -------- */
/* ---------------------------------------------------------- */

/* What is the Thread* for the currently running thread?  This is
   absolutely performance critical.  We receive notifications from the
   core for client code starts/stops, and cache the looked-up result
   in 'current_Thread'.  Hence, for the vast majority of requests,
   finding the current thread reduces to a read of a global variable,
   provided get_current_Thread_in_C_C is inlined.

   Outside of client code, current_Thread is NULL, and presumably
   any uses of it will cause a segfault.  Hence:

   - for uses definitely within client code, use
     get_current_Thread_in_C_C.

   - for all other uses, use get_current_Thread.
*/

static Thread* current_Thread = NULL;

static void evh__start_client_code ( ThreadId tid, ULong nDisp ) {
   if (0) VG_(printf)("start %d %llu\n", (Int)tid, nDisp);
   tl_assert(current_Thread == NULL);
   current_Thread = map_threads_lookup( tid );
   tl_assert(current_Thread != NULL);
}
static void evh__stop_client_code ( ThreadId tid, ULong nDisp ) {
   if (0) VG_(printf)(" stop %d %llu\n", (Int)tid, nDisp);
   tl_assert(current_Thread != NULL);
   current_Thread = NULL;
   libhb_maybe_GC();
}
static inline Thread* get_current_Thread_in_C_C ( void ) {
   return current_Thread;
}
static inline Thread* get_current_Thread ( void ) {
   ThreadId coretid;
   Thread*  thr;
   thr = get_current_Thread_in_C_C();
   if (LIKELY(thr))
      return thr;
   /* evidently not in client code.  Do it the slow way. */
   coretid = VG_(get_running_tid)();
   /* FIXME: get rid of the following kludge.  It exists because
      evh__new_mem is called during initialisation (as notification
      of initial memory layout) and VG_(get_running_tid)() returns
      VG_INVALID_THREADID at that point. */
   if (coretid == VG_INVALID_THREADID)
      coretid = 1; /* KLUDGE */
   thr = map_threads_lookup( coretid );
   return thr;
}

static
void evh__new_mem ( Addr a, SizeT len ) {
   if (SHOW_EVENTS >= 2)
      VG_(printf)("evh__new_mem(%p, %lu)\n", (void*)a, len );
   shadow_mem_make_New( get_current_Thread(), a, len );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__new_mem-post");
}

static
void evh__new_mem_w_tid ( Addr a, SizeT len, ThreadId tid ) {
   if (SHOW_EVENTS >= 2)
      VG_(printf)("evh__new_mem_w_tid(%p, %lu)\n", (void*)a, len );
   shadow_mem_make_New( get_current_Thread(), a, len );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__new_mem_w_tid-post");
}

static
void evh__new_mem_w_perms ( Addr a, SizeT len, 
                            Bool rr, Bool ww, Bool xx, ULong di_handle ) {
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__new_mem_w_perms(%p, %lu, %d,%d,%d)\n",
                  (void*)a, len, (Int)rr, (Int)ww, (Int)xx );
   if (rr || ww || xx)
      shadow_mem_make_New( get_current_Thread(), a, len );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__new_mem_w_perms-post");
}

static
void evh__set_perms ( Addr a, SizeT len,
                      Bool rr, Bool ww, Bool xx ) {
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__set_perms(%p, %lu, %d,%d,%d)\n",
                  (void*)a, len, (Int)rr, (Int)ww, (Int)xx );
   /* Hmm.  What should we do here, that actually makes any sense?
      Let's say: if neither readable nor writable, then declare it
      NoAccess, else leave it alone. */
   if (!(rr || ww))
      shadow_mem_make_NoAccess( get_current_Thread(), a, len );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__set_perms-post");
}

static
void evh__die_mem ( Addr a, SizeT len ) {
   if (SHOW_EVENTS >= 2)
      VG_(printf)("evh__die_mem(%p, %lu)\n", (void*)a, len );
   shadow_mem_make_NoAccess( get_current_Thread(), a, len );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__die_mem-post");
}

static
void evh__pre_thread_ll_create ( ThreadId parent, ThreadId child )
{
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__pre_thread_ll_create(p=%d, c=%d)\n",
                  (Int)parent, (Int)child );

   if (parent != VG_INVALID_THREADID) {
      Thread* thr_p;
      Thread* thr_c;
      Thr*    hbthr_p;
      Thr*    hbthr_c;

      tl_assert(HG_(is_sane_ThreadId)(parent));
      tl_assert(HG_(is_sane_ThreadId)(child));
      tl_assert(parent != child);

      thr_p = map_threads_maybe_lookup( parent );
      thr_c = map_threads_maybe_lookup( child );

      tl_assert(thr_p != NULL);
      tl_assert(thr_c == NULL);

      hbthr_p = thr_p->hbthr;
      tl_assert(hbthr_p != NULL);
      tl_assert( libhb_get_Thr_opaque(hbthr_p) == thr_p );

      hbthr_c = libhb_create ( hbthr_p );

      /* Create a new thread record for the child. */
      /* a Thread for the new thread ... */
      thr_c = mk_Thread( hbthr_c );
      tl_assert( libhb_get_Thr_opaque(hbthr_c) == NULL );
      libhb_set_Thr_opaque(hbthr_c, thr_c);

      /* and bind it in the thread-map table */
      map_threads[child] = thr_c;
      tl_assert(thr_c->coretid == VG_INVALID_THREADID);
      thr_c->coretid = child;

      /* Record where the parent is so we can later refer to this in
         error messages.

         On amd64-linux, this entails a nasty glibc-2.5 specific hack.
         The stack snapshot is taken immediately after the parent has
         returned from its sys_clone call.  Unfortunately there is no
         unwind info for the insn following "syscall" - reading the
         glibc sources confirms this.  So we ask for a snapshot to be
         taken as if RIP was 3 bytes earlier, in a place where there
         is unwind info.  Sigh.
      */
      { Word first_ip_delta = 0;
#       if defined(VGP_amd64_linux)
        first_ip_delta = -3;
#       endif
        thr_c->created_at = VG_(record_ExeContext)(parent, first_ip_delta);
      }
   }

   if (HG_(clo_sanity_flags) & SCE_THREADS)
      all__sanity_check("evh__pre_thread_create-post");
}

static
void evh__pre_thread_ll_exit ( ThreadId quit_tid )
{
   Int     nHeld;
   Thread* thr_q;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__pre_thread_ll_exit(thr=%d)\n",
                  (Int)quit_tid );

   /* quit_tid has disappeared without joining to any other thread.
      Therefore there is no synchronisation event associated with its
      exit and so we have to pretty much treat it as if it was still
      alive but mysteriously making no progress.  That is because, if
      we don't know when it really exited, then we can never say there
      is a point in time when we're sure the thread really has
      finished, and so we need to consider the possibility that it
      lingers indefinitely and continues to interact with other
      threads. */
   /* However, it might have rendezvous'd with a thread that called
      pthread_join with this one as arg, prior to this point (that's
      how NPTL works).  In which case there has already been a prior
      sync event.  So in any case, just let the thread exit.  On NPTL,
      all thread exits go through here. */
   tl_assert(HG_(is_sane_ThreadId)(quit_tid));
   thr_q = map_threads_maybe_lookup( quit_tid );
   tl_assert(thr_q != NULL);

   /* Complain if this thread holds any locks. */
   nHeld = HG_(cardinalityWS)( univ_lsets, thr_q->locksetA );
   tl_assert(nHeld >= 0);
   if (nHeld > 0) {
      HChar buf[80];
      VG_(sprintf)(buf, "Exiting thread still holds %d lock%s",
                        nHeld, nHeld > 1 ? "s" : "");
      HG_(record_error_Misc)( thr_q, buf );
   }

   /* About the only thing we do need to do is clear the map_threads
      entry, in order that the Valgrind core can re-use it. */
   tl_assert(thr_q->coretid == quit_tid);
   thr_q->coretid = VG_INVALID_THREADID;
   map_threads_delete( quit_tid );

   if (HG_(clo_sanity_flags) & SCE_THREADS)
      all__sanity_check("evh__pre_thread_ll_exit-post");
}


static
void evh__HG_PTHREAD_JOIN_POST ( ThreadId stay_tid, Thread* quit_thr )
{
   Thread*  thr_s;
   Thread*  thr_q;
   Thr*     hbthr_s;
   Thr*     hbthr_q;
   SO*      so;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__post_thread_join(stayer=%d, quitter=%p)\n",
                  (Int)stay_tid, quit_thr );

   tl_assert(HG_(is_sane_ThreadId)(stay_tid));

   thr_s = map_threads_maybe_lookup( stay_tid );
   thr_q = quit_thr;
   tl_assert(thr_s != NULL);
   tl_assert(thr_q != NULL);
   tl_assert(thr_s != thr_q);

   hbthr_s = thr_s->hbthr;
   hbthr_q = thr_q->hbthr;
   tl_assert(hbthr_s != hbthr_q);
   tl_assert( libhb_get_Thr_opaque(hbthr_s) == thr_s );
   tl_assert( libhb_get_Thr_opaque(hbthr_q) == thr_q );

   /* Allocate a temporary synchronisation object and use it to send
      an imaginary message from the quitter to the stayer, the purpose
      being to generate a dependence from the quitter to the
      stayer. */
   so = libhb_so_alloc();
   tl_assert(so);
   libhb_so_send(hbthr_q, so, True/*strong_send*/);
   libhb_so_recv(hbthr_s, so, True/*strong_recv*/);
   libhb_so_dealloc(so);

   /* evh__pre_thread_ll_exit issues an error message if the exiting
      thread holds any locks.  No need to check here. */

   /* This holds because, at least when using NPTL as the thread
      library, we should be notified the low level thread exit before
      we hear of any join event on it.  The low level exit
      notification feeds through into evh__pre_thread_ll_exit,
      which should clear the map_threads entry for it.  Hence we
      expect there to be no map_threads entry at this point. */
   tl_assert( map_threads_maybe_reverse_lookup_SLOW(thr_q)
              == VG_INVALID_THREADID);

   if (HG_(clo_sanity_flags) & SCE_THREADS)
      all__sanity_check("evh__post_thread_join-post");
}

static
void evh__pre_mem_read ( CorePart part, ThreadId tid, Char* s, 
                         Addr a, SizeT size) {
   if (SHOW_EVENTS >= 2
       || (SHOW_EVENTS >= 1 && size != 1))
      VG_(printf)("evh__pre_mem_read(ctid=%d, \"%s\", %p, %lu)\n", 
                  (Int)tid, s, (void*)a, size );
   shadow_mem_read_range( map_threads_lookup(tid), a, size);
   if (size >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__pre_mem_read-post");
}

static
void evh__pre_mem_read_asciiz ( CorePart part, ThreadId tid,
                                Char* s, Addr a ) {
   Int len;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__pre_mem_asciiz(ctid=%d, \"%s\", %p)\n", 
                  (Int)tid, s, (void*)a );
   // FIXME: think of a less ugly hack
   len = VG_(strlen)( (Char*) a );
   shadow_mem_read_range( map_threads_lookup(tid), a, len+1 );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__pre_mem_read_asciiz-post");
}

static
void evh__pre_mem_write ( CorePart part, ThreadId tid, Char* s,
                          Addr a, SizeT size ) {
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__pre_mem_write(ctid=%d, \"%s\", %p, %lu)\n", 
                  (Int)tid, s, (void*)a, size );
   shadow_mem_write_range( map_threads_lookup(tid), a, size);
   if (size >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__pre_mem_write-post");
}

static
void evh__new_mem_heap ( Addr a, SizeT len, Bool is_inited ) {
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__new_mem_heap(%p, %lu, inited=%d)\n", 
                  (void*)a, len, (Int)is_inited );
   // FIXME: this is kinda stupid
   if (is_inited) {
      shadow_mem_make_New(get_current_Thread(), a, len);
   } else {
      shadow_mem_make_New(get_current_Thread(), a, len);
   }
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__pre_mem_read-post");
}

static
void evh__die_mem_heap ( Addr a, SizeT len ) {
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__die_mem_heap(%p, %lu)\n", (void*)a, len );
   shadow_mem_make_NoAccess( get_current_Thread(), a, len );
   if (len >= SCE_BIGRANGE_T && (HG_(clo_sanity_flags) & SCE_BIGRANGE))
      all__sanity_check("evh__pre_mem_read-post");
}

static VG_REGPARM(1)
void evh__mem_help_read_1(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_READ_1(hbthr, a);
}

static VG_REGPARM(1)
void evh__mem_help_read_2(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_READ_2(hbthr, a);
}

static VG_REGPARM(1)
void evh__mem_help_read_4(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_READ_4(hbthr, a);
}

static VG_REGPARM(1)
void evh__mem_help_read_8(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_READ_8(hbthr, a);
}

static VG_REGPARM(2)
void evh__mem_help_read_N(Addr a, SizeT size) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_READ_N(hbthr, a, size);
}

static VG_REGPARM(1)
void evh__mem_help_write_1(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_WRITE_1(hbthr, a);
}

static VG_REGPARM(1)
void evh__mem_help_write_2(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_WRITE_2(hbthr, a);
}

static VG_REGPARM(1)
void evh__mem_help_write_4(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_WRITE_4(hbthr, a);
}

static VG_REGPARM(1)
void evh__mem_help_write_8(Addr a) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_WRITE_8(hbthr, a);
}

static VG_REGPARM(2)
void evh__mem_help_write_N(Addr a, SizeT size) {
   Thread*  thr = get_current_Thread_in_C_C();
   Thr*     hbthr = thr->hbthr;
   LIBHB_WRITE_N(hbthr, a, size);
}

//static void evh__bus_lock(void) {
//   Thread* thr;
//   if (0) VG_(printf)("evh__bus_lock()\n");
//   thr = get_current_Thread();
//   tl_assert(thr); /* cannot fail - Thread* must already exist */
//   evhH__post_thread_w_acquires_lock( thr, LK_nonRec, (Addr)&__bus_lock );
//}
//static void evh__bus_unlock(void) {
//   Thread* thr;
//   if (0) VG_(printf)("evh__bus_unlock()\n");
//   thr = get_current_Thread();
//   tl_assert(thr); /* cannot fail - Thread* must already exist */
//   evhH__pre_thread_releases_lock( thr, (Addr)&__bus_lock, False/*!isRDWR*/ );
//}

/* ------------------------------------------------------- */
/* -------------- events to do with mutexes -------------- */
/* ------------------------------------------------------- */

/* EXPOSITION only: by intercepting lock init events we can show the
   user where the lock was initialised, rather than only being able to
   show where it was first locked.  Intercepting lock initialisations
   is not necessary for the basic operation of the race checker. */
static
void evh__HG_PTHREAD_MUTEX_INIT_POST( ThreadId tid, 
                                      void* mutex, Word mbRec )
{
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_MUTEX_INIT_POST(ctid=%d, mbRec=%ld, %p)\n", 
                  (Int)tid, mbRec, (void*)mutex );
   tl_assert(mbRec == 0 || mbRec == 1);
   map_locks_lookup_or_create( mbRec ? LK_mbRec : LK_nonRec,
                               (Addr)mutex, tid );
   if (HG_(clo_sanity_flags) & SCE_LOCKS)
      all__sanity_check("evh__hg_PTHREAD_MUTEX_INIT_POST");
}

static
void evh__HG_PTHREAD_MUTEX_DESTROY_PRE( ThreadId tid, void* mutex )
{
   Thread* thr;
   Lock*   lk;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_MUTEX_DESTROY_PRE(ctid=%d, %p)\n", 
                  (Int)tid, (void*)mutex );

   thr = map_threads_maybe_lookup( tid );
   /* cannot fail - Thread* must already exist */
   tl_assert( HG_(is_sane_Thread)(thr) );

   lk = map_locks_maybe_lookup( (Addr)mutex );

   if (lk == NULL || (lk->kind != LK_nonRec && lk->kind != LK_mbRec)) {
      HG_(record_error_Misc)(
         thr, "pthread_mutex_destroy with invalid argument" );
   }

   if (lk) {
      tl_assert( HG_(is_sane_LockN)(lk) );
      tl_assert( lk->guestaddr == (Addr)mutex );
      if (lk->heldBy) {
         /* Basically act like we unlocked the lock */
         HG_(record_error_Misc)(
            thr, "pthread_mutex_destroy of a locked mutex" );
         /* remove lock from locksets of all owning threads */
         remove_Lock_from_locksets_of_all_owning_Threads( lk );
         VG_(deleteBag)( lk->heldBy );
         lk->heldBy = NULL;
         lk->heldW = False;
         lk->acquired_at = NULL;
      }
      tl_assert( !lk->heldBy );
      tl_assert( HG_(is_sane_LockN)(lk) );

      laog__handle_one_lock_deletion(lk);
      map_locks_delete( lk->guestaddr );
      del_LockN( lk );
   }

   if (HG_(clo_sanity_flags) & SCE_LOCKS)
      all__sanity_check("evh__hg_PTHREAD_MUTEX_DESTROY_PRE");
}

static void evh__HG_PTHREAD_MUTEX_LOCK_PRE ( ThreadId tid,
                                             void* mutex, Word isTryLock )
{
   /* Just check the mutex is sane; nothing else to do. */
   // 'mutex' may be invalid - not checked by wrapper
   Thread* thr;
   Lock*   lk;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_MUTEX_LOCK_PRE(ctid=%d, mutex=%p)\n", 
                  (Int)tid, (void*)mutex );

   tl_assert(isTryLock == 0 || isTryLock == 1);
   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   lk = map_locks_maybe_lookup( (Addr)mutex );

   if (lk && (lk->kind == LK_rdwr)) {
      HG_(record_error_Misc)( thr, "pthread_mutex_lock with a "
                                   "pthread_rwlock_t* argument " );
   }

   if ( lk 
        && isTryLock == 0
        && (lk->kind == LK_nonRec || lk->kind == LK_rdwr)
        && lk->heldBy
        && lk->heldW
        && VG_(elemBag)( lk->heldBy, (Word)thr ) > 0 ) {
      /* uh, it's a non-recursive lock and we already w-hold it, and
         this is a real lock operation (not a speculative "tryLock"
         kind of thing).  Duh.  Deadlock coming up; but at least
         produce an error message. */
      HG_(record_error_Misc)( thr, "Attempt to re-lock a "
                                   "non-recursive lock I already hold" );
   }
}

static void evh__HG_PTHREAD_MUTEX_LOCK_POST ( ThreadId tid, void* mutex )
{
   // only called if the real library call succeeded - so mutex is sane
   Thread* thr;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_MUTEX_LOCK_POST(ctid=%d, mutex=%p)\n", 
                  (Int)tid, (void*)mutex );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   evhH__post_thread_w_acquires_lock( 
      thr, 
      LK_mbRec, /* if not known, create new lock with this LockKind */
      (Addr)mutex
   );
}

static void evh__HG_PTHREAD_MUTEX_UNLOCK_PRE ( ThreadId tid, void* mutex )
{
   // 'mutex' may be invalid - not checked by wrapper
   Thread* thr;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_MUTEX_UNLOCK_PRE(ctid=%d, mutex=%p)\n", 
                  (Int)tid, (void*)mutex );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   evhH__pre_thread_releases_lock( thr, (Addr)mutex, False/*!isRDWR*/ );
}

static void evh__HG_PTHREAD_MUTEX_UNLOCK_POST ( ThreadId tid, void* mutex )
{
   // only called if the real library call succeeded - so mutex is sane
   Thread* thr;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_MUTEX_UNLOCK_POST(ctid=%d, mutex=%p)\n", 
                  (Int)tid, (void*)mutex );
   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   // anything we should do here?
}


/* ----------------------------------------------------- */
/* --------------- events to do with CVs --------------- */
/* ----------------------------------------------------- */

/* A mapping from CV to the SO associated with it.  When the CV is
   signalled/broadcasted upon, we do a 'send' into the SO, and when a
   wait on it completes, we do a 'recv' from the SO.  This is believed
   to give the correct happens-before events arising from CV
   signallings/broadcasts.
*/

/* pthread_mutex_cond* -> SO* */
static WordFM* map_cond_to_SO = NULL;

static void map_cond_to_SO_INIT ( void ) {
   if (UNLIKELY(map_cond_to_SO == NULL)) {
      map_cond_to_SO = VG_(newFM)( HG_(zalloc),
                                   "hg.mctSI.1", HG_(free), NULL );
      tl_assert(map_cond_to_SO != NULL);
   }
}

static SO* map_cond_to_SO_lookup_or_alloc ( void* cond ) {
   UWord key, val;
   map_cond_to_SO_INIT();
   if (VG_(lookupFM)( map_cond_to_SO, &key, &val, (UWord)cond )) {
      tl_assert(key == (UWord)cond);
      return (SO*)val;
   } else {
      SO* so = libhb_so_alloc();
      VG_(addToFM)( map_cond_to_SO, (UWord)cond, (UWord)so );
      return so;
   }
}

static void map_cond_to_SO_delete ( void* cond ) {
   UWord keyW, valW;
   map_cond_to_SO_INIT();
   if (VG_(delFromFM)( map_cond_to_SO, &keyW, &valW, (UWord)cond )) {
      SO* so = (SO*)valW;
      tl_assert(keyW == (UWord)cond);
      libhb_so_dealloc(so);
   }
}

static void evh__HG_PTHREAD_COND_SIGNAL_PRE ( ThreadId tid, void* cond )
{
   /* 'tid' has signalled on 'cond'.  As per the comment above, bind
      cond to a SO if it is not already so bound, and 'send' on the
      SO.  This is later used by other thread(s) which successfully
      exit from a pthread_cond_wait on the same cv; then they 'recv'
      from the SO, thereby acquiring a dependency on this signalling
      event. */
   Thread*   thr;
   SO*       so;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_COND_SIGNAL_PRE(ctid=%d, cond=%p)\n", 
                  (Int)tid, (void*)cond );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   // error-if: mutex is bogus
   // error-if: mutex is not locked

   so = map_cond_to_SO_lookup_or_alloc( cond );
   tl_assert(so);

   libhb_so_send( thr->hbthr, so, True/*strong_send*/ );
}

/* returns True if it reckons 'mutex' is valid and held by this
   thread, else False */
static Bool evh__HG_PTHREAD_COND_WAIT_PRE ( ThreadId tid,
                                            void* cond, void* mutex )
{
   Thread* thr;
   Lock*   lk;
   Bool    lk_valid = True;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_COND_WAIT_PRE"
                  "(ctid=%d, cond=%p, mutex=%p)\n", 
                  (Int)tid, (void*)cond, (void*)mutex );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   lk = map_locks_maybe_lookup( (Addr)mutex );

   /* Check for stupid mutex arguments.  There are various ways to be
      a bozo.  Only complain once, though, even if more than one thing
      is wrong. */
   if (lk == NULL) {
      lk_valid = False;
      HG_(record_error_Misc)( 
         thr, 
         "pthread_cond_{timed}wait called with invalid mutex" );
   } else {
      tl_assert( HG_(is_sane_LockN)(lk) );
      if (lk->kind == LK_rdwr) {
         lk_valid = False;
         HG_(record_error_Misc)(
            thr, "pthread_cond_{timed}wait called with mutex "
                 "of type pthread_rwlock_t*" );
      } else
         if (lk->heldBy == NULL) {
         lk_valid = False;
         HG_(record_error_Misc)( 
            thr, "pthread_cond_{timed}wait called with un-held mutex");
      } else
      if (lk->heldBy != NULL
          && VG_(elemBag)( lk->heldBy, (Word)thr ) == 0) {
         lk_valid = False;
         HG_(record_error_Misc)(
            thr, "pthread_cond_{timed}wait called with mutex "
                 "held by a different thread" );
      }
   }

   // error-if: cond is also associated with a different mutex

   return lk_valid;
}

static void evh__HG_PTHREAD_COND_WAIT_POST ( ThreadId tid,
                                             void* cond, void* mutex )
{
   /* A pthread_cond_wait(cond, mutex) completed successfully.  Find
      the SO for this cond, and 'recv' from it so as to acquire a
      dependency edge back to the signaller/broadcaster. */
   Thread* thr;
   SO*     so;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_COND_WAIT_POST"
                  "(ctid=%d, cond=%p, mutex=%p)\n", 
                  (Int)tid, (void*)cond, (void*)mutex );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   // error-if: cond is also associated with a different mutex

   so = map_cond_to_SO_lookup_or_alloc( cond );
   tl_assert(so);

   if (!libhb_so_everSent(so)) {
      /* Hmm.  How can a wait on 'cond' succeed if nobody signalled
         it?  If this happened it would surely be a bug in the threads
         library.  Or one of those fabled "spurious wakeups". */
      HG_(record_error_Misc)( thr, "Bug in libpthread: pthread_cond_wait "
                                   "succeeded on"
                                   " without prior pthread_cond_post");
   }

   /* anyway, acquire a dependency on it. */
   libhb_so_recv( thr->hbthr, so, True/*strong_recv*/ );
}

static void evh__HG_PTHREAD_COND_DESTROY_PRE ( ThreadId tid,
                                               void* cond )
{
   /* Deal with destroy events.  The only purpose is to free storage
      associated with the CV, so as to avoid any possible resource
      leaks. */
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_COND_DESTROY_PRE"
                  "(ctid=%d, cond=%p)\n", 
                  (Int)tid, (void*)cond );

   map_cond_to_SO_delete( cond );
}


/* ------------------------------------------------------- */
/* -------------- events to do with rwlocks -------------- */
/* ------------------------------------------------------- */

/* EXPOSITION only */
static
void evh__HG_PTHREAD_RWLOCK_INIT_POST( ThreadId tid, void* rwl )
{
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_RWLOCK_INIT_POST(ctid=%d, %p)\n", 
                  (Int)tid, (void*)rwl );
   map_locks_lookup_or_create( LK_rdwr, (Addr)rwl, tid );
   if (HG_(clo_sanity_flags) & SCE_LOCKS)
      all__sanity_check("evh__hg_PTHREAD_RWLOCK_INIT_POST");
}

static
void evh__HG_PTHREAD_RWLOCK_DESTROY_PRE( ThreadId tid, void* rwl )
{
   Thread* thr;
   Lock*   lk;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_RWLOCK_DESTROY_PRE(ctid=%d, %p)\n", 
                  (Int)tid, (void*)rwl );

   thr = map_threads_maybe_lookup( tid );
   /* cannot fail - Thread* must already exist */
   tl_assert( HG_(is_sane_Thread)(thr) );

   lk = map_locks_maybe_lookup( (Addr)rwl );

   if (lk == NULL || lk->kind != LK_rdwr) {
      HG_(record_error_Misc)(
         thr, "pthread_rwlock_destroy with invalid argument" );
   }

   if (lk) {
      tl_assert( HG_(is_sane_LockN)(lk) );
      tl_assert( lk->guestaddr == (Addr)rwl );
      if (lk->heldBy) {
         /* Basically act like we unlocked the lock */
         HG_(record_error_Misc)(
            thr, "pthread_rwlock_destroy of a locked mutex" );
         /* remove lock from locksets of all owning threads */
         remove_Lock_from_locksets_of_all_owning_Threads( lk );
         VG_(deleteBag)( lk->heldBy );
         lk->heldBy = NULL;
         lk->heldW = False;
         lk->acquired_at = NULL;
      }
      tl_assert( !lk->heldBy );
      tl_assert( HG_(is_sane_LockN)(lk) );

      laog__handle_one_lock_deletion(lk);
      map_locks_delete( lk->guestaddr );
      del_LockN( lk );
   }

   if (HG_(clo_sanity_flags) & SCE_LOCKS)
      all__sanity_check("evh__hg_PTHREAD_RWLOCK_DESTROY_PRE");
}

static 
void evh__HG_PTHREAD_RWLOCK_LOCK_PRE ( ThreadId tid,
                                       void* rwl,
                                       Word isW, Word isTryLock )
{
   /* Just check the rwl is sane; nothing else to do. */
   // 'rwl' may be invalid - not checked by wrapper
   Thread* thr;
   Lock*   lk;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_RWLOCK_LOCK_PRE(ctid=%d, isW=%d, %p)\n", 
                  (Int)tid, (Int)isW, (void*)rwl );

   tl_assert(isW == 0 || isW == 1); /* assured us by wrapper */
   tl_assert(isTryLock == 0 || isTryLock == 1); /* assured us by wrapper */
   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   lk = map_locks_maybe_lookup( (Addr)rwl );
   if ( lk 
        && (lk->kind == LK_nonRec || lk->kind == LK_mbRec) ) {
      /* Wrong kind of lock.  Duh.  */
      HG_(record_error_Misc)( 
         thr, "pthread_rwlock_{rd,rw}lock with a "
              "pthread_mutex_t* argument " );
   }
}

static 
void evh__HG_PTHREAD_RWLOCK_LOCK_POST ( ThreadId tid, void* rwl, Word isW )
{
   // only called if the real library call succeeded - so mutex is sane
   Thread* thr;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_RWLOCK_LOCK_POST(ctid=%d, isW=%d, %p)\n", 
                  (Int)tid, (Int)isW, (void*)rwl );

   tl_assert(isW == 0 || isW == 1); /* assured us by wrapper */
   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   (isW ? evhH__post_thread_w_acquires_lock 
        : evhH__post_thread_r_acquires_lock)( 
      thr, 
      LK_rdwr, /* if not known, create new lock with this LockKind */
      (Addr)rwl
   );
}

static void evh__HG_PTHREAD_RWLOCK_UNLOCK_PRE ( ThreadId tid, void* rwl )
{
   // 'rwl' may be invalid - not checked by wrapper
   Thread* thr;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_RWLOCK_UNLOCK_PRE(ctid=%d, rwl=%p)\n", 
                  (Int)tid, (void*)rwl );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   evhH__pre_thread_releases_lock( thr, (Addr)rwl, True/*isRDWR*/ );
}

static void evh__HG_PTHREAD_RWLOCK_UNLOCK_POST ( ThreadId tid, void* rwl )
{
   // only called if the real library call succeeded - so mutex is sane
   Thread* thr;
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__hg_PTHREAD_RWLOCK_UNLOCK_POST(ctid=%d, rwl=%p)\n", 
                  (Int)tid, (void*)rwl );
   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   // anything we should do here?
}


/* ---------------------------------------------------------- */
/* -------------- events to do with semaphores -------------- */
/* ---------------------------------------------------------- */

/* This is similar to but not identical to the handling for condition
   variables. */

/* For each semaphore, we maintain a stack of SOs.  When a 'post'
   operation is done on a semaphore (unlocking, essentially), a new SO
   is created for the posting thread, the posting thread does a strong
   send to it (which merely installs the posting thread's VC in the
   SO), and the SO is pushed on the semaphore's stack.

   Later, when a (probably different) thread completes 'wait' on the
   semaphore, we pop a SO off the semaphore's stack (which should be
   nonempty), and do a strong recv from it.  This mechanism creates
   dependencies between posters and waiters of the semaphore.

   It may not be necessary to use a stack - perhaps a bag of SOs would
   do.  But we do need to keep track of how many unused-up posts have
   happened for the semaphore.

   Imagine T1 and T2 both post once on a semaphore S, and T3 waits
   twice on S.  T3 cannot complete its waits without both T1 and T2
   posting.  The above mechanism will ensure that T3 acquires
   dependencies on both T1 and T2.

   When a semaphore is initialised with value N, we do as if we'd
   posted N times on the semaphore: basically create N SOs and do a
   strong send to all of then.  This allows up to N waits on the
   semaphore to acquire a dependency on the initialisation point,
   which AFAICS is the correct behaviour.

   We don't emit an error for DESTROY_PRE on a semaphore we don't know
   about.  We should.
*/

/* sem_t* -> XArray* SO* */
static WordFM* map_sem_to_SO_stack = NULL;

static void map_sem_to_SO_stack_INIT ( void ) {
   if (map_sem_to_SO_stack == NULL) {
      map_sem_to_SO_stack = VG_(newFM)( HG_(zalloc), "hg.mstSs.1",
                                        HG_(free), NULL );
      tl_assert(map_sem_to_SO_stack != NULL);
   }
}

static void push_SO_for_sem ( void* sem, SO* so ) {
   UWord   keyW;
   XArray* xa;
   tl_assert(so);
   map_sem_to_SO_stack_INIT();
   if (VG_(lookupFM)( map_sem_to_SO_stack, 
                      &keyW, (UWord*)&xa, (UWord)sem )) {
      tl_assert(keyW == (UWord)sem);
      tl_assert(xa);
      VG_(addToXA)( xa, &so );
   } else {
     xa = VG_(newXA)( HG_(zalloc), "hg.pSfs.1", HG_(free), sizeof(SO*) );
      VG_(addToXA)( xa, &so );
      VG_(addToFM)( map_sem_to_SO_stack, (Word)sem, (Word)xa );
   }
}

static SO* mb_pop_SO_for_sem ( void* sem ) {
   UWord    keyW;
   XArray*  xa;
   SO* so;
   map_sem_to_SO_stack_INIT();
   if (VG_(lookupFM)( map_sem_to_SO_stack, 
                      &keyW, (UWord*)&xa, (UWord)sem )) {
      /* xa is the stack for this semaphore. */
      Word sz; 
      tl_assert(keyW == (UWord)sem);
      sz = VG_(sizeXA)( xa );
      tl_assert(sz >= 0);
      if (sz == 0)
         return NULL; /* odd, the stack is empty */
      so = *(SO**)VG_(indexXA)( xa, sz-1 );
      tl_assert(so);
      VG_(dropTailXA)( xa, 1 );
      return so;
   } else {
      /* hmm, that's odd.  No stack for this semaphore. */
      return NULL;
   }
}

static void evh__HG_POSIX_SEM_DESTROY_PRE ( ThreadId tid, void* sem )
{
   UWord keyW, valW;
   SO*   so;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_POSIX_SEM_DESTROY_PRE(ctid=%d, sem=%p)\n", 
                  (Int)tid, (void*)sem );

   map_sem_to_SO_stack_INIT();

   /* Empty out the semaphore's SO stack.  This way of doing it is
      stupid, but at least it's easy. */
   while (1) {
      so = mb_pop_SO_for_sem( sem );
      if (!so) break;
      libhb_so_dealloc(so);
   }

   if (VG_(delFromFM)( map_sem_to_SO_stack, &keyW, &valW, (UWord)sem )) {
      XArray* xa = (XArray*)valW;
      tl_assert(keyW == (UWord)sem);
      tl_assert(xa);
      tl_assert(VG_(sizeXA)(xa) == 0); /* preceding loop just emptied it */
      VG_(deleteXA)(xa);
   }
}

static 
void evh__HG_POSIX_SEM_INIT_POST ( ThreadId tid, void* sem, UWord value )
{
   SO*     so;
   Thread* thr;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_POSIX_SEM_INIT_POST(ctid=%d, sem=%p, value=%lu)\n", 
                  (Int)tid, (void*)sem, value );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   /* Empty out the semaphore's SO stack.  This way of doing it is
      stupid, but at least it's easy. */
   while (1) {
      so = mb_pop_SO_for_sem( sem );
      if (!so) break;
      libhb_so_dealloc(so);
   }

   /* If we don't do this check, the following while loop runs us out
      of memory for stupid initial values of 'value'. */
   if (value > 10000) {
      HG_(record_error_Misc)(
         thr, "sem_init: initial value exceeds 10000; using 10000" );
      value = 10000;
   }

   /* Now create 'valid' new SOs for the thread, do a strong send to
      each of them, and push them all on the stack. */
   for (; value > 0; value--) {
      Thr* hbthr = thr->hbthr;
      tl_assert(hbthr);

      so = libhb_so_alloc();
      libhb_so_send( hbthr, so, True/*strong send*/ );
      push_SO_for_sem( sem, so );
   }
}

static void evh__HG_POSIX_SEM_POST_PRE ( ThreadId tid, void* sem )
{
   /* 'tid' has posted on 'sem'.  Create a new SO, do a strong send to
      it (iow, write our VC into it, then tick ours), and push the SO
      on on a stack of SOs associated with 'sem'.  This is later used
      by other thread(s) which successfully exit from a sem_wait on
      the same sem; by doing a strong recv from SOs popped of the
      stack, they acquire dependencies on the posting thread
      segment(s). */

   Thread* thr;
   SO*     so;
   Thr*    hbthr;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_POSIX_SEM_POST_PRE(ctid=%d, sem=%p)\n", 
                  (Int)tid, (void*)sem );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   // error-if: sem is bogus

   hbthr = thr->hbthr;
   tl_assert(hbthr);

   so = libhb_so_alloc();
   libhb_so_send( hbthr, so, True/*strong send*/ );
   push_SO_for_sem( sem, so );
}

static void evh__HG_POSIX_SEM_WAIT_POST ( ThreadId tid, void* sem )
{
   /* A sem_wait(sem) completed successfully.  Pop the posting-SO for
      the 'sem' from this semaphore's SO-stack, and do a strong recv
      from it.  This creates a dependency back to one of the post-ers
      for the semaphore. */

   Thread* thr;
   SO*     so;
   Thr*    hbthr;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_POSIX_SEM_WAIT_POST(ctid=%d, sem=%p)\n", 
                  (Int)tid, (void*)sem );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   // error-if: sem is bogus

   so = mb_pop_SO_for_sem( sem );

   if (so) {
      hbthr = thr->hbthr;
      tl_assert(hbthr);

      libhb_so_recv( hbthr, so, True/*strong recv*/ );
      libhb_so_dealloc(so);
   } else {
      /* Hmm.  How can a wait on 'sem' succeed if nobody posted to it?
         If this happened it would surely be a bug in the threads
         library. */
      HG_(record_error_Misc)(
         thr, "Bug in libpthread: sem_wait succeeded on"
              " semaphore without prior sem_post");
   }
}


/* -------------------------------------------------------- */
/* -------------- events to do with barriers -------------- */
/* -------------------------------------------------------- */

typedef
   struct {
      Bool    initted; /* has it yet been initted by guest? */
      UWord   size;    /* declared size */
      XArray* waiting; /* XA of Thread*.  # present is 0 .. .size */
   }
   Bar;

static Bar* new_Bar ( void ) {
   Bar* bar = HG_(zalloc)( "hg.nB.1 (new_Bar)", sizeof(Bar) );
   tl_assert(bar);
   /* all fields are zero */
   tl_assert(bar->initted == False);
   return bar;
}

static void delete_Bar ( Bar* bar ) {
   tl_assert(bar);
   if (bar->waiting)
      VG_(deleteXA)(bar->waiting);
   HG_(free)(bar);
}

/* A mapping which stores auxiliary data for barriers. */

/* pthread_barrier_t* -> Bar* */
static WordFM* map_barrier_to_Bar = NULL;

static void map_barrier_to_Bar_INIT ( void ) {
   if (UNLIKELY(map_barrier_to_Bar == NULL)) {
      map_barrier_to_Bar = VG_(newFM)( HG_(zalloc),
                                       "hg.mbtBI.1", HG_(free), NULL );
      tl_assert(map_barrier_to_Bar != NULL);
   }
}

static Bar* map_barrier_to_Bar_lookup_or_alloc ( void* barrier ) {
   UWord key, val;
   map_barrier_to_Bar_INIT();
   if (VG_(lookupFM)( map_barrier_to_Bar, &key, &val, (UWord)barrier )) {
      tl_assert(key == (UWord)barrier);
      return (Bar*)val;
   } else {
      Bar* bar = new_Bar();
      VG_(addToFM)( map_barrier_to_Bar, (UWord)barrier, (UWord)bar );
      return bar;
   }
}

static void map_barrier_to_Bar_delete ( void* barrier ) {
   UWord keyW, valW;
   map_barrier_to_Bar_INIT();
   if (VG_(delFromFM)( map_barrier_to_Bar, &keyW, &valW, (UWord)barrier )) {
      Bar* bar = (Bar*)valW;
      tl_assert(keyW == (UWord)barrier);
      delete_Bar(bar);
   }
}


static void evh__HG_PTHREAD_BARRIER_INIT_PRE ( ThreadId tid,
                                               void* barrier,
                                               UWord count )
{
   Thread* thr;
   Bar*    bar;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_BARRIER_INIT_PRE"
                  "(tid=%d, barrier=%p, count=%lu)\n", 
                  (Int)tid, (void*)barrier, count );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   if (count == 0) {
      HG_(record_error_Misc)(
         thr, "pthread_barrier_init: 'count' argument is zero"
      );
   }

   bar = map_barrier_to_Bar_lookup_or_alloc(barrier);
   tl_assert(bar);

   if (bar->initted) {
      HG_(record_error_Misc)(
         thr, "pthread_barrier_init: barrier is already initialised"
      );
   }

   if (bar->waiting && VG_(sizeXA)(bar->waiting) > 0) {
      tl_assert(bar->initted);
      HG_(record_error_Misc)(
         thr, "pthread_barrier_init: threads are waiting at barrier"
      );
      VG_(dropTailXA)(bar->waiting, VG_(sizeXA)(bar->waiting));
   }
   if (!bar->waiting) {
      bar->waiting = VG_(newXA)( HG_(zalloc), "hg.eHPBIP.1", HG_(free),
                                 sizeof(Thread*) );
   }

   tl_assert(bar->waiting);
   tl_assert(VG_(sizeXA)(bar->waiting) == 0);
   bar->initted = True;
   bar->size    = count;
}


static void evh__HG_PTHREAD_BARRIER_DESTROY_PRE ( ThreadId tid,
                                                  void* barrier )
{
   Thread* thr;
   Bar*    bar;

   /* Deal with destroy events.  The only purpose is to free storage
      associated with the barrier, so as to avoid any possible
      resource leaks. */
   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_BARRIER_DESTROY_PRE"
                  "(tid=%d, barrier=%p)\n", 
                  (Int)tid, (void*)barrier );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   bar = map_barrier_to_Bar_lookup_or_alloc(barrier);
   tl_assert(bar);

   if (!bar->initted) {
      HG_(record_error_Misc)(
         thr, "pthread_barrier_destroy: barrier was never initialised"
      );
   }

   if (bar->initted && bar->waiting && VG_(sizeXA)(bar->waiting) > 0) {
      HG_(record_error_Misc)(
         thr, "pthread_barrier_destroy: threads are waiting at barrier"
      );
   }

   /* Maybe we shouldn't do this; just let it persist, so that when it
      is reinitialised we don't need to do any dynamic memory
      allocation?  The downside is a potentially unlimited space leak,
      if the client creates (in turn) a large number of barriers all
      at different locations.  Note that if we do later move to the
      don't-delete-it scheme, we need to mark the barrier as
      uninitialised again since otherwise a later _init call will
      elicit a duplicate-init error.  */
   map_barrier_to_Bar_delete( barrier );
}


static void evh__HG_PTHREAD_BARRIER_WAIT_PRE ( ThreadId tid,
                                               void* barrier )
{
  /* This function gets called after a client thread calls
     pthread_barrier_wait but before it arrives at the real
     pthread_barrier_wait.

     Why is the following correct?  It's a bit subtle.

     If this is not the last thread arriving at the barrier, we simply
     note its presence and return.  Because valgrind (at least as of
     Nov 08) is single threaded, we are guaranteed safe from any race
     conditions when in this function -- no other client threads are
     running.

     If this is the last thread, then we are again the only running
     thread.  All the other threads will have either arrived at the
     real pthread_barrier_wait or are on their way to it, but in any
     case are guaranteed not to be able to move past it, because this
     thread is currently in this function and so has not yet arrived
     at the real pthread_barrier_wait.  That means that:

     1. While we are in this function, none of the other threads
        waiting at the barrier can move past it.

     2. When this function returns (and simulated execution resumes),
        this thread and all other waiting threads will be able to move
        past the real barrier.

     Because of this, it is now safe to update the vector clocks of
     all threads, to represent the fact that they all arrived at the
     barrier and have all moved on.  There is no danger of any
     complications to do with some threads leaving the barrier and
     racing back round to the front, whilst others are still leaving
     (which is the primary source of complication in correct handling/
     implementation of barriers).  That can't happen because we update
     here our data structures so as to indicate that the threads have
     passed the barrier, even though, as per (2) above, they are
     guaranteed not to pass the barrier until we return.

     This relies crucially on Valgrind being single threaded.  If that
     changes, this will need to be reconsidered.
   */
   Thread* thr;
   Bar*    bar;
   SO*     so;
   UWord   present, i;

   if (SHOW_EVENTS >= 1)
      VG_(printf)("evh__HG_PTHREAD_BARRIER_WAIT_PRE"
                  "(tid=%d, barrier=%p)\n", 
                  (Int)tid, (void*)barrier );

   thr = map_threads_maybe_lookup( tid );
   tl_assert(thr); /* cannot fail - Thread* must already exist */

   bar = map_barrier_to_Bar_lookup_or_alloc(barrier);
   tl_assert(bar);

   if (!bar->initted) {
      HG_(record_error_Misc)(
         thr, "pthread_barrier_wait: barrier is uninitialised"
      );
      return; /* client is broken .. avoid assertions below */
   }

   /* guaranteed by _INIT_PRE above */
   tl_assert(bar->size > 0);
   tl_assert(bar->waiting);

   VG_(addToXA)( bar->waiting, &thr );

   /* guaranteed by this function */
   present = VG_(sizeXA)(bar->waiting);
   tl_assert(present > 0 && present <= bar->size);

   if (present < bar->size)
      return;

   /* All the threads have arrived.  Now do the Interesting Bit.  Get
      a new synchronisation object and do a weak send to it from all
      the participating threads.  This makes its vector clocks be the
      join of all the individual threads' vector clocks.  Then do a
      strong receive from it back to all threads, so that their VCs
      are a copy of it (hence are all equal to the join of their
      original VCs.) */
   so = libhb_so_alloc();

   /* XXX check ->waiting has no duplicates */

   tl_assert(bar->waiting);
   tl_assert(VG_(sizeXA)(bar->waiting) == bar->size);

   /* compute the join ... */
   for (i = 0; i < bar->size; i++) {
      Thread* t = *(Thread**)VG_(indexXA)(bar->waiting, i);
      Thr* hbthr = t->hbthr;
      libhb_so_send( hbthr, so, False/*weak send*/ );
   }
   /* ... and distribute to all threads */
   for (i = 0; i < bar->size; i++) {
      Thread* t = *(Thread**)VG_(indexXA)(bar->waiting, i);
      Thr* hbthr = t->hbthr;
      libhb_so_recv( hbthr, so, True/*strong recv*/ );
   }

   /* finally, we must empty out the waiting vector */
   VG_(dropTailXA)(bar->waiting, VG_(sizeXA)(bar->waiting));

   /* and we don't need this any more.  Perhaps a stack-allocated
      SO would be better? */
   libhb_so_dealloc(so);
}


/*--------------------------------------------------------------*/
/*--- Lock acquisition order monitoring                      ---*/
/*--------------------------------------------------------------*/

/* FIXME: here are some optimisations still to do in
          laog__pre_thread_acquires_lock.

   The graph is structured so that if L1 --*--> L2 then L1 must be
   acquired before L2.

   The common case is that some thread T holds (eg) L1 L2 and L3 and
   is repeatedly acquiring and releasing Ln, and there is no ordering
   error in what it is doing.  Hence it repeatly:

   (1) searches laog to see if Ln --*--> {L1,L2,L3}, which always 
       produces the answer No (because there is no error).

   (2) adds edges {L1,L2,L3} --> Ln to laog, which are already present
       (because they already got added the first time T acquired Ln).

   Hence cache these two events:

   (1) Cache result of the query from last time.  Invalidate the cache
       any time any edges are added to or deleted from laog.

   (2) Cache these add-edge requests and ignore them if said edges
       have already been added to laog.  Invalidate the cache any time
       any edges are deleted from laog.
*/

typedef
   struct {
      WordSetID inns; /* in univ_laog */
      WordSetID outs; /* in univ_laog */
   }
   LAOGLinks;

/* lock order acquisition graph */
static WordFM* laog = NULL; /* WordFM Lock* LAOGLinks* */

/* EXPOSITION ONLY: for each edge in 'laog', record the two places
   where that edge was created, so that we can show the user later if
   we need to. */
typedef
   struct {
      Addr        src_ga; /* Lock guest addresses for */
      Addr        dst_ga; /* src/dst of the edge */
      ExeContext* src_ec; /* And corresponding places where that */
      ExeContext* dst_ec; /* ordering was established */
   }
   LAOGLinkExposition;

static Word cmp_LAOGLinkExposition ( UWord llx1W, UWord llx2W ) {
   /* Compare LAOGLinkExposition*s by (src_ga,dst_ga) field pair. */
   LAOGLinkExposition* llx1 = (LAOGLinkExposition*)llx1W;
   LAOGLinkExposition* llx2 = (LAOGLinkExposition*)llx2W;
   if (llx1->src_ga < llx2->src_ga) return -1;
   if (llx1->src_ga > llx2->src_ga) return  1;
   if (llx1->dst_ga < llx2->dst_ga) return -1;
   if (llx1->dst_ga > llx2->dst_ga) return  1;
   return 0;
}

static WordFM* laog_exposition = NULL; /* WordFM LAOGLinkExposition* NULL */
/* end EXPOSITION ONLY */


__attribute__((noinline))
static void laog__init ( void )
{
   tl_assert(!laog);
   tl_assert(!laog_exposition);

   laog = VG_(newFM)( HG_(zalloc), "hg.laog__init.1", 
                      HG_(free), NULL/*unboxedcmp*/ );

   laog_exposition = VG_(newFM)( HG_(zalloc), "hg.laog__init.2", HG_(free), 
                                 cmp_LAOGLinkExposition );
   tl_assert(laog);
   tl_assert(laog_exposition);
}

static void laog__show ( Char* who ) {
   Word i, ws_size;
   UWord* ws_words;
   Lock* me;
   LAOGLinks* links;
   VG_(printf)("laog (requested by %s) {\n", who);
   VG_(initIterFM)( laog );
   me = NULL;
   links = NULL;
   while (VG_(nextIterFM)( laog, (Word*)&me,
                                 (Word*)&links )) {
      tl_assert(me);
      tl_assert(links);
      VG_(printf)("   node %p:\n", me);
      HG_(getPayloadWS)( &ws_words, &ws_size, univ_laog, links->inns );
      for (i = 0; i < ws_size; i++)
         VG_(printf)("      inn %#lx\n", ws_words[i] );
      HG_(getPayloadWS)( &ws_words, &ws_size, univ_laog, links->outs );
      for (i = 0; i < ws_size; i++)
         VG_(printf)("      out %#lx\n", ws_words[i] );
      me = NULL;
      links = NULL;
   }
   VG_(doneIterFM)( laog );
   VG_(printf)("}\n");
}

__attribute__((noinline))
static void laog__add_edge ( Lock* src, Lock* dst ) {
   Word       keyW;
   LAOGLinks* links;
   Bool       presentF, presentR;
   if (0) VG_(printf)("laog__add_edge %p %p\n", src, dst);

   /* Take the opportunity to sanity check the graph.  Record in
      presentF if there is already a src->dst mapping in this node's
      forwards links, and presentR if there is already a src->dst
      mapping in this node's backwards links.  They should agree!
      Also, we need to know whether the edge was already present so as
      to decide whether or not to update the link details mapping.  We
      can compute presentF and presentR essentially for free, so may
      as well do this always. */
   presentF = presentR = False;

   /* Update the out edges for src */
   keyW  = 0;
   links = NULL;
   if (VG_(lookupFM)( laog, &keyW, (Word*)&links, (Word)src )) {
      WordSetID outs_new;
      tl_assert(links);
      tl_assert(keyW == (Word)src);
      outs_new = HG_(addToWS)( univ_laog, links->outs, (Word)dst );
      presentF = outs_new == links->outs;
      links->outs = outs_new;
   } else {
      links = HG_(zalloc)("hg.lae.1", sizeof(LAOGLinks));
      links->inns = HG_(emptyWS)( univ_laog );
      links->outs = HG_(singletonWS)( univ_laog, (Word)dst );
      VG_(addToFM)( laog, (Word)src, (Word)links );
   }
   /* Update the in edges for dst */
   keyW  = 0;
   links = NULL;
   if (VG_(lookupFM)( laog, &keyW, (Word*)&links, (Word)dst )) {
      WordSetID inns_new;
      tl_assert(links);
      tl_assert(keyW == (Word)dst);
      inns_new = HG_(addToWS)( univ_laog, links->inns, (Word)src );
      presentR = inns_new == links->inns;
      links->inns = inns_new;
   } else {
      links = HG_(zalloc)("hg.lae.2", sizeof(LAOGLinks));
      links->inns = HG_(singletonWS)( univ_laog, (Word)src );
      links->outs = HG_(emptyWS)( univ_laog );
      VG_(addToFM)( laog, (Word)dst, (Word)links );
   }

   tl_assert( (presentF && presentR) || (!presentF && !presentR) );

   if (!presentF && src->acquired_at && dst->acquired_at) {
      LAOGLinkExposition expo;
      /* If this edge is entering the graph, and we have acquired_at
         information for both src and dst, record those acquisition
         points.  Hence, if there is later a violation of this
         ordering, we can show the user the two places in which the
         required src-dst ordering was previously established. */
      if (0) VG_(printf)("acquire edge %#lx %#lx\n",
                         src->guestaddr, dst->guestaddr);
      expo.src_ga = src->guestaddr;
      expo.dst_ga = dst->guestaddr;
      expo.src_ec = NULL;
      expo.dst_ec = NULL;
      tl_assert(laog_exposition);
      if (VG_(lookupFM)( laog_exposition, NULL, NULL, (Word)&expo )) {
         /* we already have it; do nothing */
      } else {
         LAOGLinkExposition* expo2 = HG_(zalloc)("hg.lae.3", 
                                               sizeof(LAOGLinkExposition));
         expo2->src_ga = src->guestaddr;
         expo2->dst_ga = dst->guestaddr;
         expo2->src_ec = src->acquired_at;
         expo2->dst_ec = dst->acquired_at;
         VG_(addToFM)( laog_exposition, (Word)expo2, (Word)NULL );
      }
   }
}

__attribute__((noinline))
static void laog__del_edge ( Lock* src, Lock* dst ) {
   Word       keyW;
   LAOGLinks* links;
   if (0) VG_(printf)("laog__del_edge %p %p\n", src, dst);
   /* Update the out edges for src */
   keyW  = 0;
   links = NULL;
   if (VG_(lookupFM)( laog, &keyW, (Word*)&links, (Word)src )) {
      tl_assert(links);
      tl_assert(keyW == (Word)src);
      links->outs = HG_(delFromWS)( univ_laog, links->outs, (Word)dst );
   }
   /* Update the in edges for dst */
   keyW  = 0;
   links = NULL;
   if (VG_(lookupFM)( laog, &keyW, (Word*)&links, (Word)dst )) {
      tl_assert(links);
      tl_assert(keyW == (Word)dst);
      links->inns = HG_(delFromWS)( univ_laog, links->inns, (Word)src );
   }
}

__attribute__((noinline))
static WordSetID /* in univ_laog */ laog__succs ( Lock* lk ) {
   Word       keyW;
   LAOGLinks* links;
   keyW  = 0;
   links = NULL;
   if (VG_(lookupFM)( laog, &keyW, (Word*)&links, (Word)lk )) {
      tl_assert(links);
      tl_assert(keyW == (Word)lk);
      return links->outs;
   } else {
      return HG_(emptyWS)( univ_laog );
   }
}

__attribute__((noinline))
static WordSetID /* in univ_laog */ laog__preds ( Lock* lk ) {
   Word       keyW;
   LAOGLinks* links;
   keyW  = 0;
   links = NULL;
   if (VG_(lookupFM)( laog, &keyW, (Word*)&links, (Word)lk )) {
      tl_assert(links);
      tl_assert(keyW == (Word)lk);
      return links->inns;
   } else {
      return HG_(emptyWS)( univ_laog );
   }
}

__attribute__((noinline))
static void laog__sanity_check ( Char* who ) {
   Word i, ws_size;
   UWord* ws_words;
   Lock* me;
   LAOGLinks* links;
   if (UNLIKELY(!laog || !laog_exposition))
      laog__init();
   VG_(initIterFM)( laog );
   me = NULL;
   links = NULL;
   if (0) VG_(printf)("laog sanity check\n");
   while (VG_(nextIterFM)( laog, (Word*)&me,
                                 (Word*)&links )) {
      tl_assert(me);
      tl_assert(links);
      HG_(getPayloadWS)( &ws_words, &ws_size, univ_laog, links->inns );
      for (i = 0; i < ws_size; i++) {
         if ( ! HG_(elemWS)( univ_laog, 
                             laog__succs( (Lock*)ws_words[i] ), 
                             (Word)me ))
            goto bad;
      }
      HG_(getPayloadWS)( &ws_words, &ws_size, univ_laog, links->outs );
      for (i = 0; i < ws_size; i++) {
         if ( ! HG_(elemWS)( univ_laog, 
                             laog__preds( (Lock*)ws_words[i] ), 
                             (Word)me ))
            goto bad;
      }
      me = NULL;
      links = NULL;
   }
   VG_(doneIterFM)( laog );
   return;

  bad:
   VG_(printf)("laog__sanity_check(%s) FAILED\n", who);
   laog__show(who);
   tl_assert(0);
}

/* If there is a path in laog from 'src' to any of the elements in
   'dst', return an arbitrarily chosen element of 'dst' reachable from
   'src'.  If no path exist from 'src' to any element in 'dst', return
   NULL. */
__attribute__((noinline))
static
Lock* laog__do_dfs_from_to ( Lock* src, WordSetID dsts /* univ_lsets */ )
{
   Lock*     ret;
   Word      i, ssz;
   XArray*   stack;   /* of Lock* */
   WordFM*   visited; /* Lock* -> void, iow, Set(Lock*) */
   Lock*     here;
   WordSetID succs;
   Word      succs_size;
   UWord*    succs_words;
   //laog__sanity_check();

   /* If the destination set is empty, we can never get there from
      'src' :-), so don't bother to try */
   if (HG_(isEmptyWS)( univ_lsets, dsts ))
      return NULL;

   ret     = NULL;
   stack   = VG_(newXA)( HG_(zalloc), "hg.lddft.1", HG_(free), sizeof(Lock*) );
   visited = VG_(newFM)( HG_(zalloc), "hg.lddft.2", HG_(free), NULL/*unboxedcmp*/ );

   (void) VG_(addToXA)( stack, &src );

   while (True) {

      ssz = VG_(sizeXA)( stack );

      if (ssz == 0) { ret = NULL; break; }

      here = *(Lock**) VG_(indexXA)( stack, ssz-1 );
      VG_(dropTailXA)( stack, 1 );

      if (HG_(elemWS)( univ_lsets, dsts, (Word)here )) { ret = here; break; }

      if (VG_(lookupFM)( visited, NULL, NULL, (Word)here ))
         continue;

      VG_(addToFM)( visited, (Word)here, 0 );

      succs = laog__succs( here );
      HG_(getPayloadWS)( &succs_words, &succs_size, univ_laog, succs );
      for (i = 0; i < succs_size; i++)
         (void) VG_(addToXA)( stack, &succs_words[i] );
   }

   VG_(deleteFM)( visited, NULL, NULL );
   VG_(deleteXA)( stack );
   return ret;
}


/* Thread 'thr' is acquiring 'lk'.  Check for inconsistent ordering
   between 'lk' and the locks already held by 'thr' and issue a
   complaint if so.  Also, update the ordering graph appropriately.
*/
__attribute__((noinline))
static void laog__pre_thread_acquires_lock ( 
               Thread* thr, /* NB: BEFORE lock is added */
               Lock*   lk
            )
{
   UWord*   ls_words;
   Word     ls_size, i;
   Lock*    other;

   /* It may be that 'thr' already holds 'lk' and is recursively
      relocking in.  In this case we just ignore the call. */
   /* NB: univ_lsets really is correct here */
   if (HG_(elemWS)( univ_lsets, thr->locksetA, (Word)lk ))
      return;

   if (UNLIKELY(!laog || !laog_exposition))
      laog__init();

   /* First, the check.  Complain if there is any path in laog from lk
      to any of the locks already held by thr, since if any such path
      existed, it would mean that previously lk was acquired before
      (rather than after, as we are doing here) at least one of those
      locks.
   */
   other = laog__do_dfs_from_to(lk, thr->locksetA);
   if (other) {
      LAOGLinkExposition key, *found;
      /* So we managed to find a path lk --*--> other in the graph,
         which implies that 'lk' should have been acquired before
         'other' but is in fact being acquired afterwards.  We present
         the lk/other arguments to record_error_LockOrder in the order
         in which they should have been acquired. */
      /* Go look in the laog_exposition mapping, to find the allocation
         points for this edge, so we can show the user. */
      key.src_ga = lk->guestaddr;
      key.dst_ga = other->guestaddr;
      key.src_ec = NULL;
      key.dst_ec = NULL;
      found = NULL;
      if (VG_(lookupFM)( laog_exposition,
                         (Word*)&found, NULL, (Word)&key )) {
         tl_assert(found != &key);
         tl_assert(found->src_ga == key.src_ga);
         tl_assert(found->dst_ga == key.dst_ga);
         tl_assert(found->src_ec);
         tl_assert(found->dst_ec);
         HG_(record_error_LockOrder)( 
            thr, lk->guestaddr, other->guestaddr,
                 found->src_ec, found->dst_ec );
      } else {
         /* Hmm.  This can't happen (can it?) */
         HG_(record_error_LockOrder)(
            thr, lk->guestaddr, other->guestaddr,
                 NULL, NULL );
      }
   }

   /* Second, add to laog the pairs
        (old, lk)  |  old <- locks already held by thr
      Since both old and lk are currently held by thr, their acquired_at
      fields must be non-NULL.
   */
   tl_assert(lk->acquired_at);
   HG_(getPayloadWS)( &ls_words, &ls_size, univ_lsets, thr->locksetA );
   for (i = 0; i < ls_size; i++) {
      Lock* old = (Lock*)ls_words[i];
      tl_assert(old->acquired_at);
      laog__add_edge( old, lk );
   }

   /* Why "except_Locks" ?  We're here because a lock is being
      acquired by a thread, and we're in an inconsistent state here.
      See the call points in evhH__post_thread_{r,w}_acquires_lock.
      When called in this inconsistent state, locks__sanity_check duly
      barfs. */
   if (HG_(clo_sanity_flags) & SCE_LAOG)
      all_except_Locks__sanity_check("laog__pre_thread_acquires_lock-post");
}


/* Delete from 'laog' any pair mentioning a lock in locksToDelete */

__attribute__((noinline))
static void laog__handle_one_lock_deletion ( Lock* lk )
{
   WordSetID preds, succs;
   Word preds_size, succs_size, i, j;
   UWord *preds_words, *succs_words;

   if (UNLIKELY(!laog || !laog_exposition))
      laog__init();

   preds = laog__preds( lk );
   succs = laog__succs( lk );

   HG_(getPayloadWS)( &preds_words, &preds_size, univ_laog, preds );
   for (i = 0; i < preds_size; i++)
      laog__del_edge( (Lock*)preds_words[i], lk );

   HG_(getPayloadWS)( &succs_words, &succs_size, univ_laog, succs );
   for (j = 0; j < succs_size; j++)
      laog__del_edge( lk, (Lock*)succs_words[j] );

   for (i = 0; i < preds_size; i++) {
      for (j = 0; j < succs_size; j++) {
         if (preds_words[i] != succs_words[j]) {
            /* This can pass unlocked locks to laog__add_edge, since
               we're deleting stuff.  So their acquired_at fields may
               be NULL. */
            laog__add_edge( (Lock*)preds_words[i], (Lock*)succs_words[j] );
         }
      }
   }
}

//__attribute__((noinline))
//static void laog__handle_lock_deletions (
//               WordSetID /* in univ_laog */ locksToDelete
//            )
//{
//   Word   i, ws_size;
//   UWord* ws_words;
//
//   if (UNLIKELY(!laog || !laog_exposition))
//      laog__init();
//
//   HG_(getPayloadWS)( &ws_words, &ws_size, univ_lsets, locksToDelete );
//   for (i = 0; i < ws_size; i++)
//      laog__handle_one_lock_deletion( (Lock*)ws_words[i] );
//
//   if (HG_(clo_sanity_flags) & SCE_LAOG)
//      all__sanity_check("laog__handle_lock_deletions-post");
//}


/*--------------------------------------------------------------*/
/*--- Malloc/free replacements                               ---*/
/*--------------------------------------------------------------*/

typedef
   struct {
      void*       next;    /* required by m_hashtable */
      Addr        payload; /* ptr to actual block    */
      SizeT       szB;     /* size requested         */
      ExeContext* where;   /* where it was allocated */
      Thread*     thr;     /* allocating thread      */
   }
   MallocMeta;

/* A hash table of MallocMetas, used to track malloc'd blocks
   (obviously). */
static VgHashTable hg_mallocmeta_table = NULL;


static MallocMeta* new_MallocMeta ( void ) {
   MallocMeta* md = HG_(zalloc)( "hg.new_MallocMeta.1", sizeof(MallocMeta) );
   tl_assert(md);
   return md;
}
static void delete_MallocMeta ( MallocMeta* md ) {
   HG_(free)(md);
}


/* Allocate a client block and set up the metadata for it. */

static
void* handle_alloc ( ThreadId tid, 
                     SizeT szB, SizeT alignB, Bool is_zeroed )
{
   Addr        p;
   MallocMeta* md;

   tl_assert( ((SSizeT)szB) >= 0 );
   p = (Addr)VG_(cli_malloc)(alignB, szB);
   if (!p) {
      return NULL;
   }
   if (is_zeroed)
      VG_(memset)((void*)p, 0, szB);

   /* Note that map_threads_lookup must succeed (cannot assert), since
      memory can only be allocated by currently alive threads, hence
      they must have an entry in map_threads. */
   md = new_MallocMeta();
   md->payload = p;
   md->szB     = szB;
   md->where   = VG_(record_ExeContext)( tid, 0 );
   md->thr     = map_threads_lookup( tid );

   VG_(HT_add_node)( hg_mallocmeta_table, (VgHashNode*)md );

   /* Tell the lower level memory wranglers. */
   evh__new_mem_heap( p, szB, is_zeroed );

   return (void*)p;
}

/* Re the checks for less-than-zero (also in hg_cli__realloc below):
   Cast to a signed type to catch any unexpectedly negative args.
   We're assuming here that the size asked for is not greater than
   2^31 bytes (for 32-bit platforms) or 2^63 bytes (for 64-bit
   platforms). */
static void* hg_cli__malloc ( ThreadId tid, SizeT n ) {
   if (((SSizeT)n) < 0) return NULL;
   return handle_alloc ( tid, n, VG_(clo_alignment),
                         /*is_zeroed*/False );
}
static void* hg_cli____builtin_new ( ThreadId tid, SizeT n ) {
   if (((SSizeT)n) < 0) return NULL;
   return handle_alloc ( tid, n, VG_(clo_alignment),
                         /*is_zeroed*/False );
}
static void* hg_cli____builtin_vec_new ( ThreadId tid, SizeT n ) {
   if (((SSizeT)n) < 0) return NULL;
   return handle_alloc ( tid, n, VG_(clo_alignment), 
                         /*is_zeroed*/False );
}
static void* hg_cli__memalign ( ThreadId tid, SizeT align, SizeT n ) {
   if (((SSizeT)n) < 0) return NULL;
   return handle_alloc ( tid, n, align, 
                         /*is_zeroed*/False );
}
static void* hg_cli__calloc ( ThreadId tid, SizeT nmemb, SizeT size1 ) {
   if ( ((SSizeT)nmemb) < 0 || ((SSizeT)size1) < 0 ) return NULL;
   return handle_alloc ( tid, nmemb*size1, VG_(clo_alignment),
                         /*is_zeroed*/True );
}


/* Free a client block, including getting rid of the relevant
   metadata. */

static void handle_free ( ThreadId tid, void* p )
{
   MallocMeta *md, *old_md;
   SizeT      szB;

   /* First see if we can find the metadata for 'p'. */
   md = (MallocMeta*) VG_(HT_lookup)( hg_mallocmeta_table, (UWord)p );
   if (!md)
      return; /* apparently freeing a bogus address.  Oh well. */

   tl_assert(md->payload == (Addr)p);
   szB = md->szB;

   /* Nuke the metadata block */
   old_md = (MallocMeta*)
            VG_(HT_remove)( hg_mallocmeta_table, (UWord)p );
   tl_assert(old_md); /* it must be present - we just found it */
   tl_assert(old_md == md);
   tl_assert(old_md->payload == (Addr)p);

   VG_(cli_free)((void*)old_md->payload);
   delete_MallocMeta(old_md);

   /* Tell the lower level memory wranglers. */
   evh__die_mem_heap( (Addr)p, szB );
}

static void hg_cli__free ( ThreadId tid, void* p ) {
   handle_free(tid, p);
}
static void hg_cli____builtin_delete ( ThreadId tid, void* p ) {
   handle_free(tid, p);
}
static void hg_cli____builtin_vec_delete ( ThreadId tid, void* p ) {
   handle_free(tid, p);
}


static void* hg_cli__realloc ( ThreadId tid, void* payloadV, SizeT new_size )
{
   MallocMeta *md, *md_new, *md_tmp;
   SizeT      i;

   Addr payload = (Addr)payloadV;

   if (((SSizeT)new_size) < 0) return NULL;

   md = (MallocMeta*) VG_(HT_lookup)( hg_mallocmeta_table, (UWord)payload );
   if (!md)
      return NULL; /* apparently realloc-ing a bogus address.  Oh well. */
  
   tl_assert(md->payload == payload);

   if (md->szB == new_size) {
      /* size unchanged */
      md->where = VG_(record_ExeContext)(tid, 0);
      return payloadV;
   }

   if (md->szB > new_size) {
      /* new size is smaller */
      md->szB   = new_size;
      md->where = VG_(record_ExeContext)(tid, 0);
      evh__die_mem_heap( md->payload + new_size, md->szB - new_size );
      return payloadV;
   }

   /* else */ {
      /* new size is bigger */
      Addr p_new = (Addr)VG_(cli_malloc)(VG_(clo_alignment), new_size);

      /* First half kept and copied, second half new */
      // FIXME: shouldn't we use a copier which implements the
      // memory state machine?
      shadow_mem_copy_range( payload, p_new, md->szB );
      evh__new_mem_heap ( p_new + md->szB, new_size - md->szB,
                          /*inited*/False );
      /* FIXME: can anything funny happen here?  specifically, if the
         old range contained a lock, then die_mem_heap will complain.
         Is that the correct behaviour?  Not sure. */
      evh__die_mem_heap( payload, md->szB );

      /* Copy from old to new */
      for (i = 0; i < md->szB; i++)
         ((UChar*)p_new)[i] = ((UChar*)payload)[i];

      /* Because the metadata hash table is index by payload address,
         we have to get rid of the old hash table entry and make a new
         one.  We can't just modify the existing metadata in place,
         because then it would (almost certainly) be in the wrong hash
         chain. */
      md_new = new_MallocMeta();
      *md_new = *md;

      md_tmp = VG_(HT_remove)( hg_mallocmeta_table, payload );
      tl_assert(md_tmp);
      tl_assert(md_tmp == md);

      VG_(cli_free)((void*)md->payload);
      delete_MallocMeta(md);

      /* Update fields */
      md_new->where   = VG_(record_ExeContext)( tid, 0 );
      md_new->szB     = new_size;
      md_new->payload = p_new;
      md_new->thr     = map_threads_lookup( tid );

      /* and add */
      VG_(HT_add_node)( hg_mallocmeta_table, (VgHashNode*)md_new );

      return (void*)p_new;
   }  
}

static SizeT hg_cli_malloc_usable_size ( ThreadId tid, void* p )
{
   MallocMeta *md = VG_(HT_lookup)( hg_mallocmeta_table, (UWord)p );

   // There may be slop, but pretend there isn't because only the asked-for
   // area will have been shadowed properly.
   return ( md ? md->szB : 0 );
}


/*--------------------------------------------------------------*/
/*--- Instrumentation                                        ---*/
/*--------------------------------------------------------------*/

static void instrument_mem_access ( IRSB*   bbOut, 
                                    IRExpr* addr,
                                    Int     szB,
                                    Bool    isStore,
                                    Int     hWordTy_szB )
{
   IRType   tyAddr   = Ity_INVALID;
   HChar*   hName    = NULL;
   void*    hAddr    = NULL;
   Int      regparms = 0;
   IRExpr** argv     = NULL;
   IRDirty* di       = NULL;

   tl_assert(isIRAtom(addr));
   tl_assert(hWordTy_szB == 4 || hWordTy_szB == 8);

   tyAddr = typeOfIRExpr( bbOut->tyenv, addr );
   tl_assert(tyAddr == Ity_I32 || tyAddr == Ity_I64);

   /* So the effective address is in 'addr' now. */
   regparms = 1; // unless stated otherwise
   if (isStore) {
      switch (szB) {
         case 1:
            hName = "evh__mem_help_write_1";
            hAddr = &evh__mem_help_write_1;
            argv = mkIRExprVec_1( addr );
            break;
         case 2:
            hName = "evh__mem_help_write_2";
            hAddr = &evh__mem_help_write_2;
            argv = mkIRExprVec_1( addr );
            break;
         case 4:
            hName = "evh__mem_help_write_4";
            hAddr = &evh__mem_help_write_4;
            argv = mkIRExprVec_1( addr );
            break;
         case 8:
            hName = "evh__mem_help_write_8";
            hAddr = &evh__mem_help_write_8;
            argv = mkIRExprVec_1( addr );
            break;
         default:
            tl_assert(szB > 8 && szB <= 512); /* stay sane */
            regparms = 2;
            hName = "evh__mem_help_write_N";
            hAddr = &evh__mem_help_write_N;
            argv = mkIRExprVec_2( addr, mkIRExpr_HWord( szB ));
            break;
      }
   } else {
      switch (szB) {
         case 1:
            hName = "evh__mem_help_read_1";
            hAddr = &evh__mem_help_read_1;
            argv = mkIRExprVec_1( addr );
            break;
         case 2:
            hName = "evh__mem_help_read_2";
            hAddr = &evh__mem_help_read_2;
            argv = mkIRExprVec_1( addr );
            break;
         case 4:
            hName = "evh__mem_help_read_4";
            hAddr = &evh__mem_help_read_4;
            argv = mkIRExprVec_1( addr );
            break;
         case 8:
            hName = "evh__mem_help_read_8";
            hAddr = &evh__mem_help_read_8;
            argv = mkIRExprVec_1( addr );
            break;
         default: 
            tl_assert(szB > 8 && szB <= 512); /* stay sane */
            regparms = 2;
            hName = "evh__mem_help_read_N";
            hAddr = &evh__mem_help_read_N;
            argv = mkIRExprVec_2( addr, mkIRExpr_HWord( szB ));
            break;
      }
   }

   /* Add the helper. */
   tl_assert(hName);
   tl_assert(hAddr);
   tl_assert(argv);
   di = unsafeIRDirty_0_N( regparms,
                           hName, VG_(fnptr_to_fnentry)( hAddr ),
                           argv );
   addStmtToIRSB( bbOut, IRStmt_Dirty(di) );
}


//static void instrument_memory_bus_event ( IRSB* bbOut, IRMBusEvent event )
//{
//   switch (event) {
//      case Imbe_SnoopedStoreBegin:
//      case Imbe_SnoopedStoreEnd:
//         /* These arise from ppc stwcx. insns.  They should perhaps be
//            handled better. */
//         break;
//      case Imbe_Fence:
//         break; /* not interesting */
//      case Imbe_BusLock:
//      case Imbe_BusUnlock:
//         addStmtToIRSB(
//            bbOut,
//            IRStmt_Dirty(
//               unsafeIRDirty_0_N( 
//                  0/*regparms*/, 
//                  event == Imbe_BusLock ? "evh__bus_lock"
//                                        : "evh__bus_unlock",
//                  VG_(fnptr_to_fnentry)(
//                     event == Imbe_BusLock ? &evh__bus_lock 
//                                           : &evh__bus_unlock 
//                  ),
//                  mkIRExprVec_0() 
//               )
//            )
//         );
//         break;
//      default:
//         tl_assert(0);
//   }
//}


static
IRSB* hg_instrument ( VgCallbackClosure* closure,
                      IRSB* bbIn,
                      VexGuestLayout* layout,
                      VexGuestExtents* vge,
                      IRType gWordTy, IRType hWordTy )
{
   Int   i;
   IRSB* bbOut;
   Bool  x86busLocked   = False;
   Bool  isSnoopedStore = False;

   if (gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
   }

   /* Set up BB */
   bbOut           = emptyIRSB();
   bbOut->tyenv    = deepCopyIRTypeEnv(bbIn->tyenv);
   bbOut->next     = deepCopyIRExpr(bbIn->next);
   bbOut->jumpkind = bbIn->jumpkind;

   // Copy verbatim any IR preamble preceding the first IMark
   i = 0;
   while (i < bbIn->stmts_used && bbIn->stmts[i]->tag != Ist_IMark) {
      addStmtToIRSB( bbOut, bbIn->stmts[i] );
      i++;
   }

   for (/*use current i*/; i < bbIn->stmts_used; i++) {
      IRStmt* st = bbIn->stmts[i];
      tl_assert(st);
      tl_assert(isFlatIRStmt(st));
      switch (st->tag) {
         case Ist_NoOp:
         case Ist_AbiHint:
         case Ist_Put:
         case Ist_PutI:
         case Ist_IMark:
         case Ist_Exit:
            /* None of these can contain any memory references. */
            break;

         case Ist_MBE:
            //instrument_memory_bus_event( bbOut, st->Ist.MBE.event );
            switch (st->Ist.MBE.event) {
               case Imbe_Fence:
                  break; /* not interesting */
               /* Imbe_Bus{Lock,Unlock} arise from x86/amd64 LOCK
                  prefixed instructions. */
               case Imbe_BusLock:
                  tl_assert(x86busLocked == False);
                  x86busLocked = True;
                  break;
               case Imbe_BusUnlock:
                  tl_assert(x86busLocked == True);
                  x86busLocked = False;
                  break;
                  /* Imbe_SnoopedStore{Begin,End} arise from ppc
                     stwcx. instructions. */
               case Imbe_SnoopedStoreBegin:
                  tl_assert(isSnoopedStore == False);
                  isSnoopedStore = True;
                  break;
               case Imbe_SnoopedStoreEnd:
                  tl_assert(isSnoopedStore == True);
                  isSnoopedStore = False;
                  break;
               default:
                  goto unhandled;
            }
            break;

         case Ist_Store:
            if (!x86busLocked && !isSnoopedStore)
               instrument_mem_access( 
                  bbOut, 
                  st->Ist.Store.addr, 
                  sizeofIRType(typeOfIRExpr(bbIn->tyenv, st->Ist.Store.data)),
                  True/*isStore*/,
                  sizeofIRType(hWordTy)
               );
            break;

         case Ist_WrTmp: {
            IRExpr* data = st->Ist.WrTmp.data;
            if (data->tag == Iex_Load) {
               instrument_mem_access(
                  bbOut,
                  data->Iex.Load.addr,
                  sizeofIRType(data->Iex.Load.ty),
                  False/*!isStore*/,
                  sizeofIRType(hWordTy)
               );
            }
            break;
         }

         case Ist_Dirty: {
            Int      dataSize;
            IRDirty* d = st->Ist.Dirty.details;
            if (d->mFx != Ifx_None) {
               /* This dirty helper accesses memory.  Collect the
                  details. */
               tl_assert(d->mAddr != NULL);
               tl_assert(d->mSize != 0);
               dataSize = d->mSize;
               if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify) {
                  instrument_mem_access( 
                     bbOut, d->mAddr, dataSize, False/*!isStore*/,
                     sizeofIRType(hWordTy)
                  );
               }
               /* This isn't really correct.  Really the
                  instrumentation should be only added when
                  (!x86busLocked && !isSnoopedStore), just like with
                  Ist_Store.  Still, I don't think this is
                  particularly important. */
               if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify) {
                  instrument_mem_access( 
                     bbOut, d->mAddr, dataSize, True/*isStore*/,
                     sizeofIRType(hWordTy)
                  );
               }
            } else {
               tl_assert(d->mAddr == NULL);
               tl_assert(d->mSize == 0);
            }
            break;
         }

         default:
         unhandled:
            ppIRStmt(st);
            tl_assert(0);

      } /* switch (st->tag) */

      addStmtToIRSB( bbOut, st );
   } /* iterate over bbIn->stmts */

   return bbOut;
}


/*----------------------------------------------------------------*/
/*--- Client requests                                          ---*/
/*----------------------------------------------------------------*/

/* Sheesh.  Yet another goddam finite map. */
static WordFM* map_pthread_t_to_Thread = NULL; /* pthread_t -> Thread* */

static void map_pthread_t_to_Thread_INIT ( void ) {
   if (UNLIKELY(map_pthread_t_to_Thread == NULL)) {
      map_pthread_t_to_Thread = VG_(newFM)( HG_(zalloc), "hg.mpttT.1", 
                                            HG_(free), NULL );
      tl_assert(map_pthread_t_to_Thread != NULL);
   }
}


static 
Bool hg_handle_client_request ( ThreadId tid, UWord* args, UWord* ret)
{
   if (!VG_IS_TOOL_USERREQ('H','G',args[0]))
      return False;

   /* Anything that gets past the above check is one of ours, so we
      should be able to handle it. */

   /* default, meaningless return value, unless otherwise set */
   *ret = 0;

   switch (args[0]) {

      /* --- --- User-visible client requests --- --- */

      case VG_USERREQ__HG_CLEAN_MEMORY:
         if (0) VG_(printf)("VG_USERREQ__HG_CLEAN_MEMORY(%#lx,%ld)\n",
                            args[1], args[2]);
         /* Call die_mem to (expensively) tidy up properly, if there
            are any held locks etc in the area.  Calling evh__die_mem
            and then evh__new_mem is a bit inefficient; probably just
            the latter would do. */
         if (args[2] > 0) { /* length */
            evh__die_mem(args[1], args[2]);
            /* and then set it to New */
            evh__new_mem(args[1], args[2]);
         }
         break;

      /* --- --- Client requests for Helgrind's use only --- --- */

      /* Some thread is telling us its pthread_t value.  Record the
         binding between that and the associated Thread*, so we can
         later find the Thread* again when notified of a join by the
         thread. */
      case _VG_USERREQ__HG_SET_MY_PTHREAD_T: {
         Thread* my_thr = NULL;
         if (0)
         VG_(printf)("SET_MY_PTHREAD_T (tid %d): pthread_t = %p\n", (Int)tid,
                     (void*)args[1]);
         map_pthread_t_to_Thread_INIT();
         my_thr = map_threads_maybe_lookup( tid );
         /* This assertion should hold because the map_threads (tid to
            Thread*) binding should have been made at the point of
            low-level creation of this thread, which should have
            happened prior to us getting this client request for it.
            That's because this client request is sent from
            client-world from the 'thread_wrapper' function, which
            only runs once the thread has been low-level created. */
         tl_assert(my_thr != NULL);
         /* So now we know that (pthread_t)args[1] is associated with
            (Thread*)my_thr.  Note that down. */
         if (0)
         VG_(printf)("XXXX: bind pthread_t %p to Thread* %p\n",
                     (void*)args[1], (void*)my_thr );
         VG_(addToFM)( map_pthread_t_to_Thread, (Word)args[1], (Word)my_thr );
         break;
      }

      case _VG_USERREQ__HG_PTH_API_ERROR: {
         Thread* my_thr = NULL;
         map_pthread_t_to_Thread_INIT();
         my_thr = map_threads_maybe_lookup( tid );
         tl_assert(my_thr); /* See justification above in SET_MY_PTHREAD_T */
         HG_(record_error_PthAPIerror)(
            my_thr, (HChar*)args[1], (Word)args[2], (HChar*)args[3] );
         break;
      }

      /* This thread (tid) has completed a join with the quitting
         thread whose pthread_t is in args[1]. */
      case _VG_USERREQ__HG_PTHREAD_JOIN_POST: {
         Thread* thr_q = NULL; /* quitter Thread* */
         Bool    found = False;
         if (0)
         VG_(printf)("NOTIFY_JOIN_COMPLETE (tid %d): quitter = %p\n", (Int)tid,
                     (void*)args[1]);
         map_pthread_t_to_Thread_INIT();
         found = VG_(lookupFM)( map_pthread_t_to_Thread, 
                                NULL, (Word*)&thr_q, (Word)args[1] );
          /* Can this fail?  It would mean that our pthread_join
             wrapper observed a successful join on args[1] yet that
             thread never existed (or at least, it never lodged an
             entry in the mapping (via SET_MY_PTHREAD_T)).  Which
             sounds like a bug in the threads library. */
         // FIXME: get rid of this assertion; handle properly
         tl_assert(found);
         if (found) {
            if (0)
            VG_(printf)(".................... quitter Thread* = %p\n", 
                        thr_q);
            evh__HG_PTHREAD_JOIN_POST( tid, thr_q );
         }
         break;
      }

      /* EXPOSITION only: by intercepting lock init events we can show
         the user where the lock was initialised, rather than only
         being able to show where it was first locked.  Intercepting
         lock initialisations is not necessary for the basic operation
         of the race checker. */
      case _VG_USERREQ__HG_PTHREAD_MUTEX_INIT_POST:
         evh__HG_PTHREAD_MUTEX_INIT_POST( tid, (void*)args[1], args[2] );
         break;

      case _VG_USERREQ__HG_PTHREAD_MUTEX_DESTROY_PRE:
         evh__HG_PTHREAD_MUTEX_DESTROY_PRE( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_MUTEX_UNLOCK_PRE:   // pth_mx_t*
         evh__HG_PTHREAD_MUTEX_UNLOCK_PRE( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_MUTEX_UNLOCK_POST:  // pth_mx_t*
         evh__HG_PTHREAD_MUTEX_UNLOCK_POST( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_MUTEX_LOCK_PRE:     // pth_mx_t*, Word
         evh__HG_PTHREAD_MUTEX_LOCK_PRE( tid, (void*)args[1], args[2] );
         break;

      case _VG_USERREQ__HG_PTHREAD_MUTEX_LOCK_POST:    // pth_mx_t*
         evh__HG_PTHREAD_MUTEX_LOCK_POST( tid, (void*)args[1] );
         break;

      /* This thread is about to do pthread_cond_signal on the
         pthread_cond_t* in arg[1].  Ditto pthread_cond_broadcast. */
      case _VG_USERREQ__HG_PTHREAD_COND_SIGNAL_PRE:
      case _VG_USERREQ__HG_PTHREAD_COND_BROADCAST_PRE:
         evh__HG_PTHREAD_COND_SIGNAL_PRE( tid, (void*)args[1] );
         break;

      /* Entry into pthread_cond_wait, cond=arg[1], mutex=arg[2].
         Returns a flag indicating whether or not the mutex is believed to be
         valid for this operation. */
      case _VG_USERREQ__HG_PTHREAD_COND_WAIT_PRE: {
         Bool mutex_is_valid
            = evh__HG_PTHREAD_COND_WAIT_PRE( tid, (void*)args[1], 
                                                  (void*)args[2] );
         *ret = mutex_is_valid ? 1 : 0;
         break;
      }

      /* cond=arg[1] */
      case _VG_USERREQ__HG_PTHREAD_COND_DESTROY_PRE:
         evh__HG_PTHREAD_COND_DESTROY_PRE( tid, (void*)args[1] );
         break;

      /* Thread successfully completed pthread_cond_wait, cond=arg[1],
         mutex=arg[2] */
      case _VG_USERREQ__HG_PTHREAD_COND_WAIT_POST:
         evh__HG_PTHREAD_COND_WAIT_POST( tid,
                                         (void*)args[1], (void*)args[2] );
         break;

      case _VG_USERREQ__HG_PTHREAD_RWLOCK_INIT_POST:
         evh__HG_PTHREAD_RWLOCK_INIT_POST( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_RWLOCK_DESTROY_PRE:
         evh__HG_PTHREAD_RWLOCK_DESTROY_PRE( tid, (void*)args[1] );
         break;

      /* rwlock=arg[1], isW=arg[2], isTryLock=arg[3] */
      case _VG_USERREQ__HG_PTHREAD_RWLOCK_LOCK_PRE:
         evh__HG_PTHREAD_RWLOCK_LOCK_PRE( tid, (void*)args[1],
                                               args[2], args[3] );
         break;

      /* rwlock=arg[1], isW=arg[2] */
      case _VG_USERREQ__HG_PTHREAD_RWLOCK_LOCK_POST:
         evh__HG_PTHREAD_RWLOCK_LOCK_POST( tid, (void*)args[1], args[2] );
         break;

      case _VG_USERREQ__HG_PTHREAD_RWLOCK_UNLOCK_PRE:
         evh__HG_PTHREAD_RWLOCK_UNLOCK_PRE( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_RWLOCK_UNLOCK_POST:
         evh__HG_PTHREAD_RWLOCK_UNLOCK_POST( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_POSIX_SEM_INIT_POST: /* sem_t*, unsigned long */
         evh__HG_POSIX_SEM_INIT_POST( tid, (void*)args[1], args[2] );
         break;

      case _VG_USERREQ__HG_POSIX_SEM_DESTROY_PRE: /* sem_t* */
         evh__HG_POSIX_SEM_DESTROY_PRE( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_POSIX_SEM_POST_PRE: /* sem_t* */
         evh__HG_POSIX_SEM_POST_PRE( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_POSIX_SEM_WAIT_POST: /* sem_t* */
         evh__HG_POSIX_SEM_WAIT_POST( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_BARRIER_INIT_PRE:
         /* pth_bar_t*, ulong */
         evh__HG_PTHREAD_BARRIER_INIT_PRE( tid, (void*)args[1], args[2] );
         break;

      case _VG_USERREQ__HG_PTHREAD_BARRIER_WAIT_PRE:
         /* pth_bar_t* */
         evh__HG_PTHREAD_BARRIER_WAIT_PRE( tid, (void*)args[1] );
         break;

      case _VG_USERREQ__HG_PTHREAD_BARRIER_DESTROY_PRE:
         /* pth_bar_t* */
         evh__HG_PTHREAD_BARRIER_DESTROY_PRE( tid, (void*)args[1] );
         break;

      default:
         /* Unhandled Helgrind client request! */
         tl_assert2(0, "unhandled Helgrind client request 0x%lx",
                       args[0]);
   }

   return True;
}


/*----------------------------------------------------------------*/
/*--- Setup                                                    ---*/
/*----------------------------------------------------------------*/

static Bool hg_process_cmd_line_option ( Char* arg )
{
   Char* tmp_str;

   if      VG_BOOL_CLO(arg, "--track-lockorders",
                            HG_(clo_track_lockorders)) {}
   else if VG_BOOL_CLO(arg, "--cmp-race-err-addrs",
                            HG_(clo_cmp_race_err_addrs)) {}
   else if VG_BOOL_CLO(arg, "--show-conflicts",
                            HG_(clo_show_conflicts)) {}

   /* If you change the 10k/10mill limits, remember to also change
      them in assertions at the top of event_map_maybe_GC. */
   else if VG_BINT_CLO(arg, "--conflict-cache-size",
                       HG_(clo_conflict_cache_size), 10*1000, 10*1000*1000) {}

   /* "stuvwx" --> stuvwx (binary) */
   else if VG_STR_CLO(arg, "--hg-sanity-flags", tmp_str) {
      Int j;
   
      if (6 != VG_(strlen)(tmp_str)) {
         VG_(message)(Vg_UserMsg, 
                      "--hg-sanity-flags argument must have 6 digits");
         return False;
      }
      for (j = 0; j < 6; j++) {
         if      ('0' == tmp_str[j]) { /* do nothing */ }
         else if ('1' == tmp_str[j]) HG_(clo_sanity_flags) |= (1 << (6-1-j));
         else {
            VG_(message)(Vg_UserMsg, "--hg-sanity-flags argument can "
                                     "only contain 0s and 1s");
            return False;
         }
      }
      if (0) VG_(printf)("XXX sanity flags: 0x%lx\n", HG_(clo_sanity_flags));
   }

   else 
      return VG_(replacement_malloc_process_cmd_line_option)(arg);

   return True;
}

static void hg_print_usage ( void )
{
   VG_(printf)(
"    --track-lockorders=no|yes show lock ordering errors? [yes]\n"
"    --show-conflicts=no|yes   show both stack traces in a race? [yes]\n"
"    --conflict-cache-size=N   size of conflict history cache [1000000]\n"
   );
   VG_(replacement_malloc_print_usage)();
}

static void hg_print_debug_usage ( void )
{
   VG_(replacement_malloc_print_debug_usage)();
   VG_(printf)("    --cmp-race-err-addrs=no|yes  are data addresses in "
               "race errors significant? [no]\n");
   VG_(printf)("    --hg-sanity-flags=<XXXXXX>   sanity check "
               "  at events (X = 0|1) [000000]\n");
   VG_(printf)("    --hg-sanity-flags values:\n");
   VG_(printf)("       010000   after changes to "
               "lock-order-acquisition-graph\n");
   VG_(printf)("       001000   at memory accesses (NB: not currently used)\n");
   VG_(printf)("       000100   at mem permission setting for "
               "ranges >= %d bytes\n", SCE_BIGRANGE_T);
   VG_(printf)("       000010   at lock/unlock events\n");
   VG_(printf)("       000001   at thread create/join events\n");
}

static void hg_post_clo_init ( void )
{
}

static void hg_fini ( Int exitcode )
{
   if (SHOW_DATA_STRUCTURES)
      pp_everything( PP_ALL, "SK_(fini)" );
   if (HG_(clo_sanity_flags))
      all__sanity_check("SK_(fini)");

   if (VG_(clo_verbosity) >= 2) {

      if (1) {
         VG_(printf)("\n");
         HG_(ppWSUstats)( univ_tsets, "univ_tsets" );
         VG_(printf)("\n");
         HG_(ppWSUstats)( univ_lsets, "univ_lsets" );
         VG_(printf)("\n");
         HG_(ppWSUstats)( univ_laog,  "univ_laog" );
      }

      //zz       VG_(printf)("\n");
      //zz       VG_(printf)(" hbefore: %'10lu queries\n",        stats__hbefore_queries);
      //zz       VG_(printf)(" hbefore: %'10lu cache 0 hits\n",   stats__hbefore_cache0s);
      //zz       VG_(printf)(" hbefore: %'10lu cache > 0 hits\n", stats__hbefore_cacheNs);
      //zz       VG_(printf)(" hbefore: %'10lu graph searches\n", stats__hbefore_gsearches);
      //zz       VG_(printf)(" hbefore: %'10lu   of which slow\n",
      //zz                   stats__hbefore_gsearches - stats__hbefore_gsearchFs);
      //zz       VG_(printf)(" hbefore: %'10lu stack high water mark\n",
      //zz                   stats__hbefore_stk_hwm);
      //zz       VG_(printf)(" hbefore: %'10lu cache invals\n",   stats__hbefore_invals);
      //zz       VG_(printf)(" hbefore: %'10lu probes\n",         stats__hbefore_probes);

      VG_(printf)("\n");
      VG_(printf)("        locksets: %'8d unique lock sets\n",
                  (Int)HG_(cardinalityWSU)( univ_lsets ));
      VG_(printf)("      threadsets: %'8d unique thread sets\n",
                  (Int)HG_(cardinalityWSU)( univ_tsets ));
      VG_(printf)("       univ_laog: %'8d unique lock sets\n",
                  (Int)HG_(cardinalityWSU)( univ_laog ));

      //VG_(printf)("L(ast)L(ock) map: %'8lu inserts (%d map size)\n",
      //            stats__ga_LL_adds,
      //            (Int)(ga_to_lastlock ? VG_(sizeFM)( ga_to_lastlock ) : 0) );

      VG_(printf)("  LockN-to-P map: %'8llu queries (%llu map size)\n",
                  HG_(stats__LockN_to_P_queries),
                  HG_(stats__LockN_to_P_get_map_size)() );

      VG_(printf)("string table map: %'8llu queries (%llu map size)\n",
                  HG_(stats__string_table_queries),
                  HG_(stats__string_table_get_map_size)() );
      VG_(printf)("            LAOG: %'8d map size\n",
                  (Int)(laog ? VG_(sizeFM)( laog ) : 0));
      VG_(printf)(" LAOG exposition: %'8d map size\n",
                  (Int)(laog_exposition ? VG_(sizeFM)( laog_exposition ) : 0));
      VG_(printf)("           locks: %'8lu acquires, "
                  "%'lu releases\n",
                  stats__lockN_acquires,
                  stats__lockN_releases
                 );
      VG_(printf)("   sanity checks: %'8lu\n", stats__sanity_checks);

      VG_(printf)("\n");
      libhb_shutdown(True);
   }
}

/* FIXME: move these somewhere sane */

static
void for_libhb__get_stacktrace ( Thr* hbt, Addr* frames, UWord nRequest )
{
   Thread*     thr;
   ThreadId    tid;
   UWord       nActual;
   tl_assert(hbt);
   thr = libhb_get_Thr_opaque( hbt );
   tl_assert(thr);
   tid = map_threads_maybe_reverse_lookup_SLOW(thr);
   nActual = (UWord)VG_(get_StackTrace)( tid, frames, (UInt)nRequest,
                                         NULL, NULL, 0 );
   tl_assert(nActual <= nRequest);
   for (; nActual < nRequest; nActual++)
      frames[nActual] = 0;
}

static
ExeContext*  for_libhb__get_EC ( Thr* hbt )
{
   Thread*     thr;
   ThreadId    tid;
   ExeContext* ec;
   tl_assert(hbt);
   thr = libhb_get_Thr_opaque( hbt );
   tl_assert(thr);
   tid = map_threads_maybe_reverse_lookup_SLOW(thr);
   ec = VG_(record_ExeContext)( tid, 0 );
   return ec;
}


static void hg_pre_clo_init ( void )
{
   Thr* hbthr_root;

   VG_(details_name)            ("Helgrind");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("a thread error detector");
   VG_(details_copyright_author)(
      "Copyright (C) 2007-2009, and GNU GPL'd, by OpenWorks LLP et al.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);
   VG_(details_avg_translation_sizeB) ( 200 );

   VG_(basic_tool_funcs)          (hg_post_clo_init,
                                   hg_instrument,
                                   hg_fini);

   VG_(needs_core_errors)         ();
   VG_(needs_tool_errors)         (HG_(eq_Error),
                                   HG_(pp_Error),
                                   False,/*show TIDs for errors*/
                                   HG_(update_extra),
                                   HG_(recognised_suppression),
                                   HG_(read_extra_suppression_info),
                                   HG_(error_matches_suppression),
                                   HG_(get_error_name),
                                   HG_(print_extra_suppression_info));

   VG_(needs_command_line_options)(hg_process_cmd_line_option,
                                   hg_print_usage,
                                   hg_print_debug_usage);
   VG_(needs_client_requests)     (hg_handle_client_request);

   // FIXME?
   //VG_(needs_sanity_checks)       (hg_cheap_sanity_check,
   //                                hg_expensive_sanity_check);

   VG_(needs_malloc_replacement)  (hg_cli__malloc,
                                   hg_cli____builtin_new,
                                   hg_cli____builtin_vec_new,
                                   hg_cli__memalign,
                                   hg_cli__calloc,
                                   hg_cli__free,
                                   hg_cli____builtin_delete,
                                   hg_cli____builtin_vec_delete,
                                   hg_cli__realloc,
                                   hg_cli_malloc_usable_size,
                                   HG_CLI__MALLOC_REDZONE_SZB );

   /* 21 Dec 08: disabled this; it mostly causes H to start more
      slowly and use significantly more memory, without very often
      providing useful results.  The user can request to load this
      information manually with --read-var-info=yes. */
   if (0) VG_(needs_var_info)(); /* optional */

   VG_(track_new_mem_startup)     ( evh__new_mem_w_perms );
   VG_(track_new_mem_stack_signal)( evh__new_mem_w_tid );
   VG_(track_new_mem_brk)         ( evh__new_mem_w_tid );
   VG_(track_new_mem_mmap)        ( evh__new_mem_w_perms );
   VG_(track_new_mem_stack)       ( evh__new_mem );

   // FIXME: surely this isn't thread-aware
   VG_(track_copy_mem_remap)      ( shadow_mem_copy_range );

   VG_(track_change_mem_mprotect) ( evh__set_perms );

   VG_(track_die_mem_stack_signal)( evh__die_mem );
   VG_(track_die_mem_brk)         ( evh__die_mem );
   VG_(track_die_mem_munmap)      ( evh__die_mem );
   VG_(track_die_mem_stack)       ( evh__die_mem );

   // FIXME: what is this for?
   VG_(track_ban_mem_stack)       (NULL);

   VG_(track_pre_mem_read)        ( evh__pre_mem_read );
   VG_(track_pre_mem_read_asciiz) ( evh__pre_mem_read_asciiz );
   VG_(track_pre_mem_write)       ( evh__pre_mem_write );
   VG_(track_post_mem_write)      (NULL);

   /////////////////

   VG_(track_pre_thread_ll_create)( evh__pre_thread_ll_create );
   VG_(track_pre_thread_ll_exit)  ( evh__pre_thread_ll_exit );

   VG_(track_start_client_code)( evh__start_client_code );
   VG_(track_stop_client_code)( evh__stop_client_code );

   /////////////////////////////////////////////
   hbthr_root = libhb_init( for_libhb__get_stacktrace, 
                            for_libhb__get_EC );
   /////////////////////////////////////////////

   initialise_data_structures(hbthr_root);

   /* Ensure that requirements for "dodgy C-as-C++ style inheritance"
      as described in comments at the top of pub_tool_hashtable.h, are
      met.  Blargh. */
   tl_assert( sizeof(void*) == sizeof(struct _MallocMeta*) );
   tl_assert( sizeof(UWord) == sizeof(Addr) );
   hg_mallocmeta_table
      = VG_(HT_construct)( "hg_malloc_metadata_table" );

}

VG_DETERMINE_INTERFACE_VERSION(hg_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                hg_main.c ---*/
/*--------------------------------------------------------------------*/
