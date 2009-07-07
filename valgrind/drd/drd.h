/* -*- mode: C; c-basic-offset: 3; -*- */

/*
  ----------------------------------------------------------------

  Notice that the following BSD-style license applies to this one
  file (drd.h) only.  The rest of Valgrind is licensed under the
  terms of the GNU General Public License, version 2, unless
  otherwise indicated.  See the COPYING file in the source
  distribution for details.

  ----------------------------------------------------------------

  This file is part of DRD, a Valgrind tool for verification of
  multithreaded programs.

  Copyright (C) 2006-2009 Bart Van Assche <bart.vanassche@gmail.com>.
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  1. Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  2. The origin of this software must not be misrepresented; you must
  not claim that you wrote the original software.  If you use this
  software in a product, an acknowledgment in the product
  documentation would be appreciated but is not required.

  3. Altered source versions must be plainly marked as such, and must
  not be misrepresented as being the original software.

  4. The name of the author may not be used to endorse or promote
  products derived from this software without specific prior written
  permission.

  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
  WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  ----------------------------------------------------------------

  Notice that the above BSD-style license applies to this one file
  (drd.h) only.  The entire rest of Valgrind is licensed under
  the terms of the GNU General Public License, version 2.  See the
  COPYING file in the source distribution for details.

  ----------------------------------------------------------------
*/

#ifndef __VALGRIND_DRD_H
#define __VALGRIND_DRD_H


#include "valgrind.h"


/** Prefix for the (inline) functions defined in this header file. */
#define DRDCL_(str) vgDrdCl_##str


/** Obtain the thread ID assigned by Valgrind's core. */
#define DRD_GET_VALGRIND_THREADID (DRDCL_(get_valgrind_threadid)())

/** Obtain the thread ID assigned by DRD. */
#define DRD_GET_DRD_THREADID (DRDCL_(get_drd_threadid)())

/** Tell DRD not to complain about data races for the specified variable. */
#define DRD_IGNORE_VAR(x) DRDCL_(ignore_range)(&(x), sizeof(x))

/**
 * Tell DRD to trace all memory accesses on the specified variable. 
 * until the memory that was allocated for the variable is freed.
 */
#define DRD_TRACE_VAR(x) DRDCL_(trace_range)(&(x), sizeof(x))

/* !! APIWARNING !! APIWARNING !! APIWARNING !! APIWARNING !!
   The semantics and the names of the macro's defined below are still
   under discussion and subject to change without notice.
*/

/**
 * Tell DRD to insert a mark. addr is the address of an object that is not a
 * pthread synchronization object. Inserting two 'happens before' annotations
 * while no thread has passed by a 'happens after' annotation is an error.
 */
#define ANNOTATE_HAPPENS_BEFORE(addr) DRDCL_(annotate_happens_before)(addr)

/**
 * Tell DRD that the memory accesses executed after this annotation will happen
 * after the memory accesses performed before the most recent
 * ANNOTATE_HAPPENS_BEFORE(addr). addr is the address of an object that is not
 * a pthread synchronization object. Inserting a 'happens after' annotation
 * before any other thread has passed by a 'happens before' annotation for the
 * same address is an error.
 */
#define ANNOTATE_HAPPENS_AFTER(addr) DRDCL_(annotate_happens_after)(addr)

/**
 * Tell DRD that waiting on the condition variable at address cv has succeeded
 * and a lock on the mutex at address mtx is now held. Since DRD always inserts
 * a happens before relation between the pthread_cond_signal() or
 * pthread_cond_broadcast() call that wakes up a pthread_cond_wait() or
 * pthread_cond_timedwait() call and the woken up thread, this macro has been
 * defined such that it has no effect.
 */
#define ANNOTATE_CONDVAR_LOCK_WAIT(cv, mtx) do { } while(0)

/**
 * Tell DRD that the condition variable at address cv is about to be signaled.
 */
#define ANNOTATE_CONDVAR_SIGNAL(cv) do { } while(0)

/**
 * Tell DRD that waiting on condition variable at address cv succeeded and that
 * the memory operations performed after this annotation should be considered
 * to happen after the matching ANNOTATE_CONDVAR_SIGNAL(cv). Since this is the
 * default behavior of DRD, this macro and the macro above have been defined
 * such that they have no effect.
 */
#define ANNOTATE_CONDVAR_WAIT(cv) do { } while(0)

/**
 * Tell DRD to consider the memory operations that happened before a mutex
 * unlock event and after the subsequent mutex lock event on the same mutex as
 * ordered. This is how DRD always behaves, so this macro has been defined
 * such that it has no effect.
 */
#define ANNOTATE_MUTEX_IS_USED_AS_CONDVAR(mtx) do { } while(0)

/**
 * Tell DRD to handle the specified memory range like a pure happens-before
 * detector would do. Since this is how DRD always behaves, this annotation
 * has been defined such that it has no effect.
 */
#define ANNOTATE_PUBLISH_MEMORY_RANGE(addr, size) do { } while(0)

/**
 * Tell DRD to undo the effect of ANNOTATE_PUBLISH_MEMORY_RANGE().
 */
#define ANNOTATE_UNPUBLISH_MEMORY_RANGE(addr, size) do { } while(0)

/** Tell DRD that a reader-writer lock object has been initialized. */
#define ANNOTATE_RWLOCK_CREATE(rwlock) \
   DRDCL_(annotate_rwlock)(rwlock, 0, 0)

/** Tell DRD that a reader-writer lock object has been destroyed. */
#define ANNOTATE_RWLOCK_DESTROY(rwlock) \
   DRDCL_(annotate_rwlock)(rwlock, 1, 0)

/**
 * Tell DRD that a reader-writer lock has been acquired. is_w == 1 means that
 * a write lock has been obtained, is_w == 0 means that a read lock has been
 * obtained.
 */
#define ANNOTATE_RWLOCK_ACQUIRED(rwlock, is_w) \
   DRDCL_(annotate_rwlock)(rwlock, 2, is_w)

/**
 * Tell DRD that a reader-writer lock is about to be released. is_w == 1 means
 * that a write lock is about to be released, is_w == 0 means that a read lock
 * is about to be released.
 */
#define ANNOTATE_RWLOCK_RELEASED(rwlock, is_w) \
   DRDCL_(annotate_rwlock)(rwlock, 3, is_w)

/**
 * Tell DRD that a FIFO queue has been created. The abbreviation PCQ stands for
 * <em>producer-consumer</em>.
 */
#define ANNOTATE_PCQ_CREATE(pcq) do { } while(0)

/** Tell DRD that a FIFO queue has been destroyed. */
#define ANNOTATE_PCQ_DESTROY(pcq) do { } while(0)

/**
 * Tell DRD that an element has been added to the FIFO queue at address pcq.
 */
#define ANNOTATE_PCQ_PUT(pcq) do { } while(0)

/**
 * Tell DRD that an element has been removed from the FIFO queue at address pcq,
 * and that DRD should insert a happens-before relationship between the memory
 * accesses that occurred before the corresponding ANNOTATE_PCQ_PUT(pcq)
 * annotation and the memory accesses after this annotation. Correspondence
 * between PUT and GET annotations happens in FIFO order. Since locking
 * of the queue is needed anyway to add elements to or to remove elements from
 * the queue, for DRD all four FIFO annotations are defined as no-ops.
 */
#define ANNOTATE_PCQ_GET(pcq) do { } while(0)

/**
 * Tell DRD that data races in the specified address range are expected and
 * must not be reported.
 */
#define ANNOTATE_BENIGN_RACE(addr, descr) DRDCL_(ignore_range)(addr, 4)

/** Tell DRD to ignore all reads performed by the current thread. */
#define ANNOTATE_IGNORE_READS_BEGIN() DRDCL_(set_record_loads)(0)

/** Tell DRD to no longer ignore the reads performed by the current thread. */
#define ANNOTATE_IGNORE_READS_END() DRDCL_(set_record_loads)(1)

/** Tell DRD to ignore all writes performed by the current thread. */
#define ANNOTATE_IGNORE_WRITES_BEGIN() DRDCL_(set_record_stores)(0)

/** Tell DRD to no longer ignore the writes performed by the current thread. */
#define ANNOTATE_IGNORE_WRITES_END() DRDCL_(set_record_stores)(1)

/** Tell DRD to ignore all memory accesses performed by the current thread. */
#define ANNOTATE_IGNORE_READS_AND_WRITES_BEGIN() \
   do { DRDCL_(set_record_loads)(0); DRD_(set_record_stores)(0); } while(0)

/**
 * Tell DRD to no longer ignore the memory accesses performed by the current
 * thread.
 */
#define ANNOTATE_IGNORE_READS_AND_WRITES_END() \
   do { DRDCL_(set_record_loads)(1); DRD_(set_record_stores)(1); } while(0)

/**
 * Tell DRD that size bytes starting at addr has been allocated by a custom
 * memory allocator.
 */
#define ANNOTATE_NEW_MEMORY(addr, size) DRDCL_(clean_memory)(addr, size)

/** Ask DRD to report every access to the specified address range. */
#define ANNOTATE_TRACE_MEMORY(addr) DRDCL_(trace_range)(addr, 1)

/**
 * Tell DRD to assign the specified name to the current thread. This name will
 * be used in error messages printed by DRD.
 */
#define ANNOTATE_THREAD_NAME(name) DRDCL_(set_thread_name)(name)

/* !! APIWARNING !! APIWARNING !! APIWARNING !! APIWARNING !!
   The semantics and the names of the macro's defined above are still
   under discussion and subject to change without notice.
*/


/* !! ABIWARNING !! ABIWARNING !! ABIWARNING !! ABIWARNING !!
   This enum comprises an ABI exported by Valgrind to programs
   which use client requests.  DO NOT CHANGE THE ORDER OF THESE
   ENTRIES, NOR DELETE ANY -- add new ones at the end.
*/
enum {
   /* Ask the DRD tool to discard all information about memory accesses   */
   /* and client objects for the specified range. This client request is  */
   /* binary compatible with the similarly named Helgrind client request. */
   VG_USERREQ__DRD_CLEAN_MEMORY = VG_USERREQ_TOOL_BASE('H','G'),
   /* args: Addr, SizeT. */

   /* Ask the DRD tool the thread ID assigned by Valgrind. */
   VG_USERREQ__DRD_GET_VALGRIND_THREAD_ID = VG_USERREQ_TOOL_BASE('D','R'),
   /* args: none. */
   /* Ask the DRD tool the thread ID assigned by DRD. */
   VG_USERREQ__DRD_GET_DRD_THREAD_ID,
   /* args: none. */

   /* To tell the DRD tool to suppress data race detection on the */
   /* specified address range. */
   VG_USERREQ__DRD_START_SUPPRESSION,
   /* args: start address, size in bytes */
   /* To tell the DRD tool no longer to suppress data race detection on */
   /* the specified address range. */
   VG_USERREQ__DRD_FINISH_SUPPRESSION,
   /* args: start address, size in bytes */

   /* To ask the DRD tool to trace all accesses to the specified range. */
   VG_USERREQ__DRD_START_TRACE_ADDR,
   /* args: Addr, SizeT. */
   /* To ask the DRD tool to stop tracing accesses to the specified range. */
   VG_USERREQ__DRD_STOP_TRACE_ADDR,
   /* args: Addr, SizeT. */

   /* Tell DRD whether or not to record memory loads in the calling thread. */
   VG_USERREQ__DRD_RECORD_LOADS,
   /* args: Bool. */
   /* Tell DRD whether or not to record memory stores in the calling thread. */
   VG_USERREQ__DRD_RECORD_STORES,
   /* args: Bool. */

   /* Set the name of the thread that performs this client request. */
   VG_USERREQ__DRD_SET_THREAD_NAME,
   /* args: null-terminated character string. */

   /* Tell DRD to insert a happens before annotation. */
   VG_USERREQ__DRD_ANNOTATE_HAPPENS_BEFORE,
   /* args: Addr. */
   /* Tell DRD to insert a happens after annotation. */
   VG_USERREQ__DRD_ANNOTATE_HAPPENS_AFTER,
   /* args: Addr. */

   /* Tell DRD about an operation performed on a user-defined reader-writer
    * synchronization object. */
   VG_USERREQ__DRD_ANNOTATE_RWLOCK,
   /* args: Addr, Int operation_type, Int is_rw. */
};


/*
 * Do not call the inline functions below directly but use the macro's defined
 * above. The names of these inline functions may change from one release to
 * another.
 */

static __inline__
void DRDCL_(clean_memory)(const void* const addr, const int size)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_CLEAN_MEMORY,
                              addr, size, 0, 0, 0);
}

static __inline__
int DRDCL_(get_valgrind_threadid)(void)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_GET_VALGRIND_THREAD_ID,
                              0, 0, 0, 0, 0);
   return res;
}

static __inline__
int DRDCL_(get_drd_threadid)(void)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_GET_DRD_THREAD_ID,
                              0, 0, 0, 0, 0);
   return res;
}

static __inline__
void DRDCL_(ignore_range)(const void* const addr, const int size)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_START_SUPPRESSION,
                              addr, size, 0, 0, 0);
}

static __inline__
void DRDCL_(trace_range)(const void* const addr, const int size)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_START_TRACE_ADDR,
                              addr, size, 0, 0, 0);
}

static __inline__
void DRDCL_(set_record_loads)(const int enabled)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_RECORD_LOADS,
                              enabled, 0, 0, 0, 0);
}

static __inline__
void DRDCL_(set_record_stores)(const int enabled)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_RECORD_STORES,
                              enabled, 0, 0, 0, 0);
}

static __inline__
void DRDCL_(set_thread_name)(const char* const name)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_SET_THREAD_NAME,
                              name, 0, 0, 0, 0);
}

static __inline__
void DRDCL_(annotate_happens_before)(const void* const addr)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_ANNOTATE_HAPPENS_BEFORE,
                              addr, 0, 0, 0, 0);
}

static __inline__
void DRDCL_(annotate_happens_after)(const void* const addr)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0, VG_USERREQ__DRD_ANNOTATE_HAPPENS_AFTER,
                              addr, 0, 0, 0, 0);
}

static __inline__
void DRDCL_(annotate_rwlock)(const void* const rwlock, const int op,
                             const int is_w)
{
   int res;
   VALGRIND_DO_CLIENT_REQUEST(res, 0,
                              VG_USERREQ__DRD_ANNOTATE_RWLOCK,
                              rwlock, op, is_w, 0, 0);
}

#endif /* __VALGRIND_DRD_H */
