
/*--------------------------------------------------------------------*/
/*--- MemCheck: Maintain bitmaps of memory, tracking the           ---*/
/*--- accessibility (A) and validity (V) status of each byte.      ---*/
/*---                                                    mc_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of MemCheck, a heavyweight Valgrind tool for
   detecting memory errors.

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

#include "pub_tool_basics.h"
#include "pub_tool_aspacemgr.h"
#include "pub_tool_hashtable.h"     // For mc_include.h
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_options.h"
#include "pub_tool_oset.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_threadstate.h"

#include "mc_include.h"
#include "memcheck.h"   /* for client requests */


/* Set to 1 to do a little more sanity checking */
#define VG_DEBUG_MEMORY 0

#define DEBUG(fmt, args...) //VG_(printf)(fmt, ## args)

static void ocache_sarp_Set_Origins ( Addr, UWord, UInt ); /* fwds */
static void ocache_sarp_Clear_Origins ( Addr, UWord ); /* fwds */


/*------------------------------------------------------------*/
/*--- Fast-case knobs                                      ---*/
/*------------------------------------------------------------*/
 
// Comment these out to disable the fast cases (don't just set them to zero).

#define PERF_FAST_LOADV    1
#define PERF_FAST_STOREV   1

#define PERF_FAST_SARP     1

#define PERF_FAST_STACK    1
#define PERF_FAST_STACK2   1

/* Change this to 1 to enable assertions on origin tracking cache fast
   paths */
#define OC_ENABLE_ASSERTIONS 0


/*------------------------------------------------------------*/
/*--- Comments on the origin tracking implementation       ---*/
/*------------------------------------------------------------*/

/* See detailed comment entitled
   AN OVERVIEW OF THE ORIGIN TRACKING IMPLEMENTATION
   which is contained further on in this file. */


/*------------------------------------------------------------*/
/*--- V bits and A bits                                    ---*/
/*------------------------------------------------------------*/

/* Conceptually, every byte value has 8 V bits, which track whether Memcheck
   thinks the corresponding value bit is defined.  And every memory byte
   has an A bit, which tracks whether Memcheck thinks the program can access
   it safely (ie. it's mapped, and has at least one of the RWX permission bits
   set).  So every N-bit register is shadowed with N V bits, and every memory
   byte is shadowed with 8 V bits and one A bit.

   In the implementation, we use two forms of compression (compressed V bits
   and distinguished secondary maps) to avoid the 9-bit-per-byte overhead
   for memory.

   Memcheck also tracks extra information about each heap block that is
   allocated, for detecting memory leaks and other purposes.
*/

/*------------------------------------------------------------*/
/*--- Basic A/V bitmap representation.                     ---*/
/*------------------------------------------------------------*/

/* All reads and writes are checked against a memory map (a.k.a. shadow
   memory), which records the state of all memory in the process.  
   
   On 32-bit machines the memory map is organised as follows.
   The top 16 bits of an address are used to index into a top-level
   map table, containing 65536 entries.  Each entry is a pointer to a
   second-level map, which records the accesibililty and validity
   permissions for the 65536 bytes indexed by the lower 16 bits of the
   address.  Each byte is represented by two bits (details are below).  So
   each second-level map contains 16384 bytes.  This two-level arrangement
   conveniently divides the 4G address space into 64k lumps, each size 64k
   bytes.

   All entries in the primary (top-level) map must point to a valid
   secondary (second-level) map.  Since many of the 64kB chunks will
   have the same status for every bit -- ie. noaccess (for unused
   address space) or entirely addressable and defined (for code segments) --
   there are three distinguished secondary maps, which indicate 'noaccess',
   'undefined' and 'defined'.  For these uniform 64kB chunks, the primary
   map entry points to the relevant distinguished map.  In practice,
   typically more than half of the addressable memory is represented with
   the 'undefined' or 'defined' distinguished secondary map, so it gives a
   good saving.  It also lets us set the V+A bits of large address regions
   quickly in set_address_range_perms().

   On 64-bit machines it's more complicated.  If we followed the same basic
   scheme we'd have a four-level table which would require too many memory
   accesses.  So instead the top-level map table has 2^19 entries (indexed
   using bits 16..34 of the address);  this covers the bottom 32GB.  Any
   accesses above 32GB are handled with a slow, sparse auxiliary table.
   Valgrind's address space manager tries very hard to keep things below
   this 32GB barrier so that performance doesn't suffer too much.

   Note that this file has a lot of different functions for reading and
   writing shadow memory.  Only a couple are strictly necessary (eg.
   get_vabits2 and set_vabits2), most are just specialised for specific
   common cases to improve performance.

   Aside: the V+A bits are less precise than they could be -- we have no way
   of marking memory as read-only.  It would be great if we could add an
   extra state VA_BITSn_READONLY.  But then we'd have 5 different states,
   which requires 2.3 bits to hold, and there's no way to do that elegantly
   -- we'd have to double up to 4 bits of metadata per byte, which doesn't
   seem worth it.
*/

/* --------------- Basic configuration --------------- */

/* Only change this.  N_PRIMARY_MAP *must* be a power of 2. */

#if VG_WORDSIZE == 4

/* cover the entire address space */
#  define N_PRIMARY_BITS  16

#else

/* Just handle the first 32G fast and the rest via auxiliary
   primaries.  If you change this, Memcheck will assert at startup.
   See the definition of UNALIGNED_OR_HIGH for extensive comments. */
#  define N_PRIMARY_BITS  19

#endif


/* Do not change this. */
#define N_PRIMARY_MAP  ( ((UWord)1) << N_PRIMARY_BITS)

/* Do not change this. */
#define MAX_PRIMARY_ADDRESS (Addr)((((Addr)65536) * N_PRIMARY_MAP)-1)


/* --------------- Secondary maps --------------- */

// Each byte of memory conceptually has an A bit, which indicates its
// addressability, and 8 V bits, which indicates its definedness.
//
// But because very few bytes are partially defined, we can use a nice
// compression scheme to reduce the size of shadow memory.  Each byte of
// memory has 2 bits which indicates its state (ie. V+A bits):
//
//   00:  noaccess    (unaddressable but treated as fully defined)
//   01:  undefined   (addressable and fully undefined)
//   10:  defined     (addressable and fully defined)
//   11:  partdefined (addressable and partially defined)
//
// In the "partdefined" case, we use a secondary table to store the V bits.
// Each entry in the secondary-V-bits table maps a byte address to its 8 V
// bits.
//
// We store the compressed V+A bits in 8-bit chunks, ie. the V+A bits for
// four bytes (32 bits) of memory are in each chunk.  Hence the name
// "vabits8".  This lets us get the V+A bits for four bytes at a time
// easily (without having to do any shifting and/or masking), and that is a
// very common operation.  (Note that although each vabits8 chunk
// is 8 bits in size, it represents 32 bits of memory.)
//
// The representation is "inverse" little-endian... each 4 bytes of
// memory is represented by a 1 byte value, where:
//
// - the status of byte (a+0) is held in bits [1..0]
// - the status of byte (a+1) is held in bits [3..2]
// - the status of byte (a+2) is held in bits [5..4]
// - the status of byte (a+3) is held in bits [7..6]
//
// It's "inverse" because endianness normally describes a mapping from
// value bits to memory addresses;  in this case the mapping is inverted.
// Ie. instead of particular value bits being held in certain addresses, in
// this case certain addresses are represented by particular value bits.
// See insert_vabits2_into_vabits8() for an example.
// 
// But note that we don't compress the V bits stored in registers;  they
// need to be explicit to made the shadow operations possible.  Therefore
// when moving values between registers and memory we need to convert
// between the expanded in-register format and the compressed in-memory
// format.  This isn't so difficult, it just requires careful attention in a
// few places.

// These represent eight bits of memory.
#define VA_BITS2_NOACCESS     0x0      // 00b
#define VA_BITS2_UNDEFINED    0x1      // 01b
#define VA_BITS2_DEFINED      0x2      // 10b
#define VA_BITS2_PARTDEFINED  0x3      // 11b

// These represent 16 bits of memory.
#define VA_BITS4_NOACCESS     0x0      // 00_00b
#define VA_BITS4_UNDEFINED    0x5      // 01_01b
#define VA_BITS4_DEFINED      0xa      // 10_10b

// These represent 32 bits of memory.
#define VA_BITS8_NOACCESS     0x00     // 00_00_00_00b
#define VA_BITS8_UNDEFINED    0x55     // 01_01_01_01b
#define VA_BITS8_DEFINED      0xaa     // 10_10_10_10b

// These represent 64 bits of memory.
#define VA_BITS16_NOACCESS    0x0000   // 00_00_00_00b x 2
#define VA_BITS16_UNDEFINED   0x5555   // 01_01_01_01b x 2
#define VA_BITS16_DEFINED     0xaaaa   // 10_10_10_10b x 2


#define SM_CHUNKS             16384
#define SM_OFF(aaa)           (((aaa) & 0xffff) >> 2)
#define SM_OFF_16(aaa)        (((aaa) & 0xffff) >> 3)

// Paranoia:  it's critical for performance that the requested inlining
// occurs.  So try extra hard.
#define INLINE    inline __attribute__((always_inline))

static INLINE Addr start_of_this_sm ( Addr a ) {
   return (a & (~SM_MASK));
}
static INLINE Bool is_start_of_sm ( Addr a ) {
   return (start_of_this_sm(a) == a);
}

typedef 
   struct {
      UChar vabits8[SM_CHUNKS];
   }
   SecMap;

// 3 distinguished secondary maps, one for no-access, one for
// accessible but undefined, and one for accessible and defined.
// Distinguished secondaries may never be modified.
#define SM_DIST_NOACCESS   0
#define SM_DIST_UNDEFINED  1
#define SM_DIST_DEFINED    2

static SecMap sm_distinguished[3];

static INLINE Bool is_distinguished_sm ( SecMap* sm ) {
   return sm >= &sm_distinguished[0] && sm <= &sm_distinguished[2];
}

// Forward declaration
static void update_SM_counts(SecMap* oldSM, SecMap* newSM);

/* dist_sm points to one of our three distinguished secondaries.  Make
   a copy of it so that we can write to it.
*/
static SecMap* copy_for_writing ( SecMap* dist_sm )
{
   SecMap* new_sm;
   tl_assert(dist_sm == &sm_distinguished[0]
          || dist_sm == &sm_distinguished[1]
          || dist_sm == &sm_distinguished[2]);

   new_sm = VG_(am_shadow_alloc)(sizeof(SecMap));
   if (new_sm == NULL)
      VG_(out_of_memory_NORETURN)( "memcheck:allocate new SecMap", 
                                   sizeof(SecMap) );
   VG_(memcpy)(new_sm, dist_sm, sizeof(SecMap));
   update_SM_counts(dist_sm, new_sm);
   return new_sm;
}

/* --------------- Stats --------------- */

static Int   n_issued_SMs      = 0;
static Int   n_deissued_SMs    = 0;
static Int   n_noaccess_SMs    = N_PRIMARY_MAP; // start with many noaccess DSMs
static Int   n_undefined_SMs   = 0;
static Int   n_defined_SMs     = 0;
static Int   n_non_DSM_SMs     = 0;
static Int   max_noaccess_SMs  = 0;
static Int   max_undefined_SMs = 0;
static Int   max_defined_SMs   = 0;
static Int   max_non_DSM_SMs   = 0;

/* # searches initiated in auxmap_L1, and # base cmps required */
static ULong n_auxmap_L1_searches  = 0;
static ULong n_auxmap_L1_cmps      = 0;
/* # of searches that missed in auxmap_L1 and therefore had to
   be handed to auxmap_L2. And the number of nodes inserted. */
static ULong n_auxmap_L2_searches  = 0;
static ULong n_auxmap_L2_nodes     = 0;

static Int   n_sanity_cheap     = 0;
static Int   n_sanity_expensive = 0;

static Int   n_secVBit_nodes   = 0;
static Int   max_secVBit_nodes = 0;

static void update_SM_counts(SecMap* oldSM, SecMap* newSM)
{
   if      (oldSM == &sm_distinguished[SM_DIST_NOACCESS ]) n_noaccess_SMs --;
   else if (oldSM == &sm_distinguished[SM_DIST_UNDEFINED]) n_undefined_SMs--;
   else if (oldSM == &sm_distinguished[SM_DIST_DEFINED  ]) n_defined_SMs  --;
   else                                                  { n_non_DSM_SMs  --;
                                                           n_deissued_SMs ++; }

   if      (newSM == &sm_distinguished[SM_DIST_NOACCESS ]) n_noaccess_SMs ++;
   else if (newSM == &sm_distinguished[SM_DIST_UNDEFINED]) n_undefined_SMs++;
   else if (newSM == &sm_distinguished[SM_DIST_DEFINED  ]) n_defined_SMs  ++;
   else                                                  { n_non_DSM_SMs  ++;
                                                           n_issued_SMs   ++; }

   if (n_noaccess_SMs  > max_noaccess_SMs ) max_noaccess_SMs  = n_noaccess_SMs;
   if (n_undefined_SMs > max_undefined_SMs) max_undefined_SMs = n_undefined_SMs;
   if (n_defined_SMs   > max_defined_SMs  ) max_defined_SMs   = n_defined_SMs;
   if (n_non_DSM_SMs   > max_non_DSM_SMs  ) max_non_DSM_SMs   = n_non_DSM_SMs;   
}

/* --------------- Primary maps --------------- */

/* The main primary map.  This covers some initial part of the address
   space, addresses 0 .. (N_PRIMARY_MAP << 16)-1.  The rest of it is
   handled using the auxiliary primary map.  
*/
static SecMap* primary_map[N_PRIMARY_MAP];


/* An entry in the auxiliary primary map.  base must be a 64k-aligned
   value, and sm points at the relevant secondary map.  As with the
   main primary map, the secondary may be either a real secondary, or
   one of the three distinguished secondaries.  DO NOT CHANGE THIS
   LAYOUT: the first word has to be the key for OSet fast lookups.
*/
typedef
   struct { 
      Addr    base;
      SecMap* sm;
   }
   AuxMapEnt;

/* Tunable parameter: How big is the L1 queue? */
#define N_AUXMAP_L1 24

/* Tunable parameter: How far along the L1 queue to insert
   entries resulting from L2 lookups? */
#define AUXMAP_L1_INSERT_IX 12

static struct {
          Addr       base;
          AuxMapEnt* ent; // pointer to the matching auxmap_L2 node
       } 
       auxmap_L1[N_AUXMAP_L1];

static OSet* auxmap_L2 = NULL;

static void init_auxmap_L1_L2 ( void )
{
   Int i;
   for (i = 0; i < N_AUXMAP_L1; i++) {
      auxmap_L1[i].base = 0;
      auxmap_L1[i].ent  = NULL;
   }

   tl_assert(0 == offsetof(AuxMapEnt,base));
   tl_assert(sizeof(Addr) == sizeof(void*));
   auxmap_L2 = VG_(OSetGen_Create)( /*keyOff*/  offsetof(AuxMapEnt,base),
                                    /*fastCmp*/ NULL,
                                    VG_(malloc), "mc.iaLL.1", VG_(free) );
}

/* Check representation invariants; if OK return NULL; else a
   descriptive bit of text.  Also return the number of
   non-distinguished secondary maps referred to from the auxiliary
   primary maps. */

static HChar* check_auxmap_L1_L2_sanity ( Word* n_secmaps_found )
{
   Word i, j;
   /* On a 32-bit platform, the L2 and L1 tables should
      both remain empty forever.

      On a 64-bit platform:
      In the L2 table:
       all .base & 0xFFFF == 0
       all .base > MAX_PRIMARY_ADDRESS
      In the L1 table:
       all .base & 0xFFFF == 0
       all (.base > MAX_PRIMARY_ADDRESS
            .base & 0xFFFF == 0
            and .ent points to an AuxMapEnt with the same .base)
           or
           (.base == 0 and .ent == NULL)
   */
   *n_secmaps_found = 0;
   if (sizeof(void*) == 4) {
      /* 32-bit platform */
      if (VG_(OSetGen_Size)(auxmap_L2) != 0)
         return "32-bit: auxmap_L2 is non-empty";
      for (i = 0; i < N_AUXMAP_L1; i++) 
        if (auxmap_L1[i].base != 0 || auxmap_L1[i].ent != NULL)
      return "32-bit: auxmap_L1 is non-empty";
   } else {
      /* 64-bit platform */
      UWord elems_seen = 0;
      AuxMapEnt *elem, *res;
      AuxMapEnt key;
      /* L2 table */
      VG_(OSetGen_ResetIter)(auxmap_L2);
      while ( (elem = VG_(OSetGen_Next)(auxmap_L2)) ) {
         elems_seen++;
         if (0 != (elem->base & (Addr)0xFFFF))
            return "64-bit: nonzero .base & 0xFFFF in auxmap_L2";
         if (elem->base <= MAX_PRIMARY_ADDRESS)
            return "64-bit: .base <= MAX_PRIMARY_ADDRESS in auxmap_L2";
         if (elem->sm == NULL)
            return "64-bit: .sm in _L2 is NULL";
         if (!is_distinguished_sm(elem->sm))
            (*n_secmaps_found)++;
      }
      if (elems_seen != n_auxmap_L2_nodes)
         return "64-bit: disagreement on number of elems in _L2";
      /* Check L1-L2 correspondence */
      for (i = 0; i < N_AUXMAP_L1; i++) {
         if (auxmap_L1[i].base == 0 && auxmap_L1[i].ent == NULL)
            continue;
         if (0 != (auxmap_L1[i].base & (Addr)0xFFFF))
            return "64-bit: nonzero .base & 0xFFFF in auxmap_L1";
         if (auxmap_L1[i].base <= MAX_PRIMARY_ADDRESS)
            return "64-bit: .base <= MAX_PRIMARY_ADDRESS in auxmap_L1";
         if (auxmap_L1[i].ent == NULL)
            return "64-bit: .ent is NULL in auxmap_L1";
         if (auxmap_L1[i].ent->base != auxmap_L1[i].base)
            return "64-bit: _L1 and _L2 bases are inconsistent";
         /* Look it up in auxmap_L2. */
         key.base = auxmap_L1[i].base;
         key.sm   = 0;
         res = VG_(OSetGen_Lookup)(auxmap_L2, &key);
         if (res == NULL)
            return "64-bit: _L1 .base not found in _L2";
         if (res != auxmap_L1[i].ent)
            return "64-bit: _L1 .ent disagrees with _L2 entry";
      }
      /* Check L1 contains no duplicates */
      for (i = 0; i < N_AUXMAP_L1; i++) {
         if (auxmap_L1[i].base == 0)
            continue;
	 for (j = i+1; j < N_AUXMAP_L1; j++) {
            if (auxmap_L1[j].base == 0)
               continue;
            if (auxmap_L1[j].base == auxmap_L1[i].base)
               return "64-bit: duplicate _L1 .base entries";
         }
      }
   }
   return NULL; /* ok */
}

static void insert_into_auxmap_L1_at ( Word rank, AuxMapEnt* ent )
{
   Word i;
   tl_assert(ent);
   tl_assert(rank >= 0 && rank < N_AUXMAP_L1);
   for (i = N_AUXMAP_L1-1; i > rank; i--)
      auxmap_L1[i] = auxmap_L1[i-1];
   auxmap_L1[rank].base = ent->base;
   auxmap_L1[rank].ent  = ent;
}

static INLINE AuxMapEnt* maybe_find_in_auxmap ( Addr a )
{
   AuxMapEnt  key;
   AuxMapEnt* res;
   Word       i;

   tl_assert(a > MAX_PRIMARY_ADDRESS);
   a &= ~(Addr)0xFFFF;

   /* First search the front-cache, which is a self-organising
      list containing the most popular entries. */

   if (LIKELY(auxmap_L1[0].base == a))
      return auxmap_L1[0].ent;
   if (LIKELY(auxmap_L1[1].base == a)) {
      Addr       t_base = auxmap_L1[0].base;
      AuxMapEnt* t_ent  = auxmap_L1[0].ent;
      auxmap_L1[0].base = auxmap_L1[1].base;
      auxmap_L1[0].ent  = auxmap_L1[1].ent;
      auxmap_L1[1].base = t_base;
      auxmap_L1[1].ent  = t_ent;
      return auxmap_L1[0].ent;
   }

   n_auxmap_L1_searches++;

   for (i = 0; i < N_AUXMAP_L1; i++) {
      if (auxmap_L1[i].base == a) {
         break;
      }
   }
   tl_assert(i >= 0 && i <= N_AUXMAP_L1);

   n_auxmap_L1_cmps += (ULong)(i+1);

   if (i < N_AUXMAP_L1) {
      if (i > 0) {
         Addr       t_base = auxmap_L1[i-1].base;
         AuxMapEnt* t_ent  = auxmap_L1[i-1].ent;
         auxmap_L1[i-1].base = auxmap_L1[i-0].base;
         auxmap_L1[i-1].ent  = auxmap_L1[i-0].ent;
         auxmap_L1[i-0].base = t_base;
         auxmap_L1[i-0].ent  = t_ent;
         i--;
      }
      return auxmap_L1[i].ent;
   }

   n_auxmap_L2_searches++;

   /* First see if we already have it. */
   key.base = a;
   key.sm   = 0;

   res = VG_(OSetGen_Lookup)(auxmap_L2, &key);
   if (res)
      insert_into_auxmap_L1_at( AUXMAP_L1_INSERT_IX, res );
   return res;
}

static AuxMapEnt* find_or_alloc_in_auxmap ( Addr a )
{
   AuxMapEnt *nyu, *res;

   /* First see if we already have it. */
   res = maybe_find_in_auxmap( a );
   if (LIKELY(res))
      return res;

   /* Ok, there's no entry in the secondary map, so we'll have
      to allocate one. */
   a &= ~(Addr)0xFFFF;

   nyu = (AuxMapEnt*) VG_(OSetGen_AllocNode)( auxmap_L2, sizeof(AuxMapEnt) );
   tl_assert(nyu);
   nyu->base = a;
   nyu->sm   = &sm_distinguished[SM_DIST_NOACCESS];
   VG_(OSetGen_Insert)( auxmap_L2, nyu );
   insert_into_auxmap_L1_at( AUXMAP_L1_INSERT_IX, nyu );
   n_auxmap_L2_nodes++;
   return nyu;
}

/* --------------- SecMap fundamentals --------------- */

// In all these, 'low' means it's definitely in the main primary map,
// 'high' means it's definitely in the auxiliary table.

static INLINE SecMap** get_secmap_low_ptr ( Addr a )
{
   UWord pm_off = a >> 16;
#  if VG_DEBUG_MEMORY >= 1
   tl_assert(pm_off < N_PRIMARY_MAP);
#  endif
   return &primary_map[ pm_off ];
}

static INLINE SecMap** get_secmap_high_ptr ( Addr a )
{
   AuxMapEnt* am = find_or_alloc_in_auxmap(a);
   return &am->sm;
}

static SecMap** get_secmap_ptr ( Addr a )
{
   return ( a <= MAX_PRIMARY_ADDRESS 
          ? get_secmap_low_ptr(a) 
          : get_secmap_high_ptr(a));
}

static INLINE SecMap* get_secmap_for_reading_low ( Addr a )
{
   return *get_secmap_low_ptr(a);
}

static INLINE SecMap* get_secmap_for_reading_high ( Addr a )
{
   return *get_secmap_high_ptr(a);
}

static INLINE SecMap* get_secmap_for_writing_low(Addr a)
{
   SecMap** p = get_secmap_low_ptr(a);
   if (UNLIKELY(is_distinguished_sm(*p)))
      *p = copy_for_writing(*p);
   return *p;
}

static INLINE SecMap* get_secmap_for_writing_high ( Addr a )
{
   SecMap** p = get_secmap_high_ptr(a);
   if (UNLIKELY(is_distinguished_sm(*p)))
      *p = copy_for_writing(*p);
   return *p;
}

/* Produce the secmap for 'a', either from the primary map or by
   ensuring there is an entry for it in the aux primary map.  The
   secmap may be a distinguished one as the caller will only want to
   be able to read it. 
*/
static INLINE SecMap* get_secmap_for_reading ( Addr a )
{
   return ( a <= MAX_PRIMARY_ADDRESS
          ? get_secmap_for_reading_low (a)
          : get_secmap_for_reading_high(a) );
}

/* Produce the secmap for 'a', either from the primary map or by
   ensuring there is an entry for it in the aux primary map.  The
   secmap may not be a distinguished one, since the caller will want
   to be able to write it.  If it is a distinguished secondary, make a
   writable copy of it, install it, and return the copy instead.  (COW
   semantics).
*/
static SecMap* get_secmap_for_writing ( Addr a )
{
   return ( a <= MAX_PRIMARY_ADDRESS
          ? get_secmap_for_writing_low (a)
          : get_secmap_for_writing_high(a) );
}

/* If 'a' has a SecMap, produce it.  Else produce NULL.  But don't
   allocate one if one doesn't already exist.  This is used by the
   leak checker.
*/
static SecMap* maybe_get_secmap_for ( Addr a )
{
   if (a <= MAX_PRIMARY_ADDRESS) {
      return get_secmap_for_reading_low(a);
   } else {
      AuxMapEnt* am = maybe_find_in_auxmap(a);
      return am ? am->sm : NULL;
   }
}

/* --------------- Fundamental functions --------------- */

static INLINE
void insert_vabits2_into_vabits8 ( Addr a, UChar vabits2, UChar* vabits8 )
{
   UInt shift =  (a & 3)  << 1;        // shift by 0, 2, 4, or 6
   *vabits8  &= ~(0x3     << shift);   // mask out the two old bits
   *vabits8  |=  (vabits2 << shift);   // mask  in the two new bits
}

static INLINE
void insert_vabits4_into_vabits8 ( Addr a, UChar vabits4, UChar* vabits8 )
{
   UInt shift;
   tl_assert(VG_IS_2_ALIGNED(a));      // Must be 2-aligned
   shift     =  (a & 2)   << 1;        // shift by 0 or 4
   *vabits8 &= ~(0xf      << shift);   // mask out the four old bits
   *vabits8 |=  (vabits4 << shift);    // mask  in the four new bits
}

static INLINE
UChar extract_vabits2_from_vabits8 ( Addr a, UChar vabits8 )
{
   UInt shift = (a & 3) << 1;          // shift by 0, 2, 4, or 6
   vabits8 >>= shift;                  // shift the two bits to the bottom
   return 0x3 & vabits8;               // mask out the rest
}

static INLINE
UChar extract_vabits4_from_vabits8 ( Addr a, UChar vabits8 )
{
   UInt shift;
   tl_assert(VG_IS_2_ALIGNED(a));      // Must be 2-aligned
   shift = (a & 2) << 1;               // shift by 0 or 4
   vabits8 >>= shift;                  // shift the four bits to the bottom
   return 0xf & vabits8;               // mask out the rest
}

// Note that these four are only used in slow cases.  The fast cases do
// clever things like combine the auxmap check (in
// get_secmap_{read,writ}able) with alignment checks.

// *** WARNING! ***
// Any time this function is called, if it is possible that vabits2
// is equal to VA_BITS2_PARTDEFINED, then the corresponding entry in the
// sec-V-bits table must also be set!
static INLINE
void set_vabits2 ( Addr a, UChar vabits2 )
{
   SecMap* sm       = get_secmap_for_writing(a);
   UWord   sm_off   = SM_OFF(a);
   insert_vabits2_into_vabits8( a, vabits2, &(sm->vabits8[sm_off]) );
}

static INLINE
UChar get_vabits2 ( Addr a )
{
   SecMap* sm       = get_secmap_for_reading(a);
   UWord   sm_off   = SM_OFF(a);
   UChar   vabits8  = sm->vabits8[sm_off];
   return extract_vabits2_from_vabits8(a, vabits8);
}

// *** WARNING! ***
// Any time this function is called, if it is possible that any of the
// 4 2-bit fields in vabits8 are equal to VA_BITS2_PARTDEFINED, then the 
// corresponding entry(s) in the sec-V-bits table must also be set!
static INLINE
UChar get_vabits8_for_aligned_word32 ( Addr a )
{
   SecMap* sm       = get_secmap_for_reading(a);
   UWord   sm_off   = SM_OFF(a);
   UChar   vabits8  = sm->vabits8[sm_off];
   return vabits8;
}

static INLINE
void set_vabits8_for_aligned_word32 ( Addr a, UChar vabits8 )
{
   SecMap* sm       = get_secmap_for_writing(a);
   UWord   sm_off   = SM_OFF(a);
   sm->vabits8[sm_off] = vabits8;
}


// Forward declarations
static UWord get_sec_vbits8(Addr a);
static void  set_sec_vbits8(Addr a, UWord vbits8);

// Returns False if there was an addressability error.
static INLINE
Bool set_vbits8 ( Addr a, UChar vbits8 )
{
   Bool  ok      = True;
   UChar vabits2 = get_vabits2(a);
   if ( VA_BITS2_NOACCESS != vabits2 ) {
      // Addressable.  Convert in-register format to in-memory format.
      // Also remove any existing sec V bit entry for the byte if no
      // longer necessary.
      if      ( V_BITS8_DEFINED   == vbits8 ) { vabits2 = VA_BITS2_DEFINED;   }
      else if ( V_BITS8_UNDEFINED == vbits8 ) { vabits2 = VA_BITS2_UNDEFINED; }
      else                                    { vabits2 = VA_BITS2_PARTDEFINED;
                                                set_sec_vbits8(a, vbits8);  }
      set_vabits2(a, vabits2);

   } else {
      // Unaddressable!  Do nothing -- when writing to unaddressable
      // memory it acts as a black hole, and the V bits can never be seen
      // again.  So we don't have to write them at all.
      ok = False;
   }
   return ok;
}

// Returns False if there was an addressability error.  In that case, we put
// all defined bits into vbits8.
static INLINE
Bool get_vbits8 ( Addr a, UChar* vbits8 )
{
   Bool  ok      = True;
   UChar vabits2 = get_vabits2(a);

   // Convert the in-memory format to in-register format.
   if      ( VA_BITS2_DEFINED   == vabits2 ) { *vbits8 = V_BITS8_DEFINED;   }
   else if ( VA_BITS2_UNDEFINED == vabits2 ) { *vbits8 = V_BITS8_UNDEFINED; }
   else if ( VA_BITS2_NOACCESS  == vabits2 ) {
      *vbits8 = V_BITS8_DEFINED;    // Make V bits defined!
      ok = False;
   } else {
      tl_assert( VA_BITS2_PARTDEFINED == vabits2 );
      *vbits8 = get_sec_vbits8(a);
   }
   return ok;
}


/* --------------- Secondary V bit table ------------ */

// This table holds the full V bit pattern for partially-defined bytes
// (PDBs) that are represented by VA_BITS2_PARTDEFINED in the main shadow
// memory.
//
// Note: the nodes in this table can become stale.  Eg. if you write a PDB,
// then overwrite the same address with a fully defined byte, the sec-V-bit
// node will not necessarily be removed.  This is because checking for
// whether removal is necessary would slow down the fast paths.  
//
// To avoid the stale nodes building up too much, we periodically (once the
// table reaches a certain size) garbage collect (GC) the table by
// traversing it and evicting any "sufficiently stale" nodes, ie. nodes that
// are stale and haven't been touched for a certain number of collections.
// If more than a certain proportion of nodes survived, we increase the
// table size so that GCs occur less often.  
//
// (So this a bit different to a traditional GC, where you definitely want
// to remove any dead nodes.  It's more like we have a resizable cache and
// we're trying to find the right balance how many elements to evict and how
// big to make the cache.)
//
// This policy is designed to avoid bad table bloat in the worst case where
// a program creates huge numbers of stale PDBs -- we would get this bloat
// if we had no GC -- while handling well the case where a node becomes
// stale but shortly afterwards is rewritten with a PDB and so becomes
// non-stale again (which happens quite often, eg. in perf/bz2).  If we just
// remove all stale nodes as soon as possible, we just end up re-adding a
// lot of them in later again.  The "sufficiently stale" approach avoids
// this.  (If a program has many live PDBs, performance will just suck,
// there's no way around that.)

static OSet* secVBitTable;

// Stats
static ULong sec_vbits_new_nodes = 0;
static ULong sec_vbits_updates   = 0;

// This must be a power of two;  this is checked in mc_pre_clo_init().
// The size chosen here is a trade-off:  if the nodes are bigger (ie. cover
// a larger address range) they take more space but we can get multiple
// partially-defined bytes in one if they are close to each other, reducing
// the number of total nodes.  In practice sometimes they are clustered (eg.
// perf/bz2 repeatedly writes then reads more than 20,000 in a contiguous
// row), but often not.  So we choose something intermediate.
#define BYTES_PER_SEC_VBIT_NODE     16

// We make the table bigger if more than this many nodes survive a GC.
#define MAX_SURVIVOR_PROPORTION  0.5

// Each time we make the table bigger, we increase it by this much.
#define TABLE_GROWTH_FACTOR      2

// This defines "sufficiently stale" -- any node that hasn't been touched in
// this many GCs will be removed.
#define MAX_STALE_AGE            2
      
// We GC the table when it gets this many nodes in it, ie. it's effectively
// the table size.  It can change.
static Int  secVBitLimit = 1024;

// The number of GCs done, used to age sec-V-bit nodes for eviction.
// Because it's unsigned, wrapping doesn't matter -- the right answer will
// come out anyway.
static UInt GCs_done = 0;

typedef 
   struct {
      Addr  a;
      UChar vbits8[BYTES_PER_SEC_VBIT_NODE];
      UInt  last_touched;
   } 
   SecVBitNode;

static OSet* createSecVBitTable(void)
{
   return VG_(OSetGen_Create)( offsetof(SecVBitNode, a), 
                               NULL, // use fast comparisons
                               VG_(malloc), "mc.cSVT.1 (sec VBit table)", 
                               VG_(free) );
}

static void gcSecVBitTable(void)
{
   OSet*        secVBitTable2;
   SecVBitNode* n;
   Int          i, n_nodes = 0, n_survivors = 0;

   GCs_done++;

   // Create the new table.
   secVBitTable2 = createSecVBitTable();

   // Traverse the table, moving fresh nodes into the new table.
   VG_(OSetGen_ResetIter)(secVBitTable);
   while ( (n = VG_(OSetGen_Next)(secVBitTable)) ) {
      Bool keep = False;
      if ( (GCs_done - n->last_touched) <= MAX_STALE_AGE ) {
         // Keep node if it's been touched recently enough (regardless of
         // freshness/staleness).
         keep = True;
      } else {
         // Keep node if any of its bytes are non-stale.  Using
         // get_vabits2() for the lookup is not very efficient, but I don't
         // think it matters.
         for (i = 0; i < BYTES_PER_SEC_VBIT_NODE; i++) {
            if (VA_BITS2_PARTDEFINED == get_vabits2(n->a + i)) {
               keep = True;      // Found a non-stale byte, so keep
               break;
            }
         }
      }

      if ( keep ) {
         // Insert a copy of the node into the new table.
         SecVBitNode* n2 = 
            VG_(OSetGen_AllocNode)(secVBitTable2, sizeof(SecVBitNode));
         *n2 = *n;
         VG_(OSetGen_Insert)(secVBitTable2, n2);
      }
   }

   // Get the before and after sizes.
   n_nodes     = VG_(OSetGen_Size)(secVBitTable);
   n_survivors = VG_(OSetGen_Size)(secVBitTable2);

   // Destroy the old table, and put the new one in its place.
   VG_(OSetGen_Destroy)(secVBitTable);
   secVBitTable = secVBitTable2;

   if (VG_(clo_verbosity) > 1) {
      Char percbuf[6];
      VG_(percentify)(n_survivors, n_nodes, 1, 6, percbuf);
      VG_(message)(Vg_DebugMsg, "memcheck GC: %d nodes, %d survivors (%s)",
                   n_nodes, n_survivors, percbuf);
   }

   // Increase table size if necessary.
   if (n_survivors > (secVBitLimit * MAX_SURVIVOR_PROPORTION)) {
      secVBitLimit *= TABLE_GROWTH_FACTOR;
      if (VG_(clo_verbosity) > 1)
         VG_(message)(Vg_DebugMsg, "memcheck GC: increase table size to %d",
                      secVBitLimit);
   }
}

static UWord get_sec_vbits8(Addr a)
{
   Addr         aAligned = VG_ROUNDDN(a, BYTES_PER_SEC_VBIT_NODE);
   Int          amod     = a % BYTES_PER_SEC_VBIT_NODE;
   SecVBitNode* n        = VG_(OSetGen_Lookup)(secVBitTable, &aAligned);
   UChar        vbits8;
   tl_assert2(n, "get_sec_vbits8: no node for address %p (%p)\n", aAligned, a);
   // Shouldn't be fully defined or fully undefined -- those cases shouldn't
   // make it to the secondary V bits table.
   vbits8 = n->vbits8[amod];
   tl_assert(V_BITS8_DEFINED != vbits8 && V_BITS8_UNDEFINED != vbits8);
   return vbits8;
}

static void set_sec_vbits8(Addr a, UWord vbits8)
{
   Addr         aAligned = VG_ROUNDDN(a, BYTES_PER_SEC_VBIT_NODE);
   Int          i, amod  = a % BYTES_PER_SEC_VBIT_NODE;
   SecVBitNode* n        = VG_(OSetGen_Lookup)(secVBitTable, &aAligned);
   // Shouldn't be fully defined or fully undefined -- those cases shouldn't
   // make it to the secondary V bits table.
   tl_assert(V_BITS8_DEFINED != vbits8 && V_BITS8_UNDEFINED != vbits8);
   if (n) {
      n->vbits8[amod] = vbits8;     // update
      n->last_touched = GCs_done;
      sec_vbits_updates++;
   } else {
      // New node:  assign the specific byte, make the rest invalid (they
      // should never be read as-is, but be cautious).
      n = VG_(OSetGen_AllocNode)(secVBitTable, sizeof(SecVBitNode));
      n->a            = aAligned;
      for (i = 0; i < BYTES_PER_SEC_VBIT_NODE; i++) {
         n->vbits8[i] = V_BITS8_UNDEFINED;
      }
      n->vbits8[amod] = vbits8;
      n->last_touched = GCs_done;

      // Do a table GC if necessary.  Nb: do this before inserting the new
      // node, to avoid erroneously GC'ing the new node.
      if (secVBitLimit == VG_(OSetGen_Size)(secVBitTable)) {
         gcSecVBitTable();
      }

      // Insert the new node.
      VG_(OSetGen_Insert)(secVBitTable, n);
      sec_vbits_new_nodes++;

      n_secVBit_nodes = VG_(OSetGen_Size)(secVBitTable);
      if (n_secVBit_nodes > max_secVBit_nodes)
         max_secVBit_nodes = n_secVBit_nodes;
   }
}

/* --------------- Endianness helpers --------------- */

/* Returns the offset in memory of the byteno-th most significant byte
   in a wordszB-sized word, given the specified endianness. */
static INLINE UWord byte_offset_w ( UWord wordszB, Bool bigendian, 
                                    UWord byteno ) {
   return bigendian ? (wordszB-1-byteno) : byteno;
}


/* --------------- Ignored address ranges --------------- */

#define M_IGNORE_RANGES 4

typedef
   struct {
      Int  used;
      Addr start[M_IGNORE_RANGES];
      Addr end[M_IGNORE_RANGES];
   }
   IgnoreRanges;

static IgnoreRanges ignoreRanges;

INLINE Bool MC_(in_ignored_range) ( Addr a )
{
   Int i;
   if (LIKELY(ignoreRanges.used == 0))
      return False;
   for (i = 0; i < ignoreRanges.used; i++) {
      if (a >= ignoreRanges.start[i] && a < ignoreRanges.end[i])
         return True;
   }
   return False;
}


/* Parse a 32- or 64-bit hex number, including leading 0x, from string
   starting at *ppc, putting result in *result, and return True.  Or
   fail, in which case *ppc and *result are undefined, and return
   False. */

static Bool isHex ( UChar c )
{
  return ((c >= '0' && c <= '9') ||
	  (c >= 'a' && c <= 'f') ||
	  (c >= 'A' && c <= 'F'));
}

static UInt fromHex ( UChar c )
{
   if (c >= '0' && c <= '9')
      return (UInt)c - (UInt)'0';
   if (c >= 'a' && c <= 'f')
      return 10 +  (UInt)c - (UInt)'a';
   if (c >= 'A' && c <= 'F')
      return 10 +  (UInt)c - (UInt)'A';
   /*NOTREACHED*/
   tl_assert(0);
   return 0;
}

static Bool parse_Addr ( UChar** ppc, Addr* result )
{
   Int used, limit = 2 * sizeof(Addr);
   if (**ppc != '0')
      return False;
   (*ppc)++;
   if (**ppc != 'x')
      return False;
   (*ppc)++;
   *result = 0;
   used = 0;
   while (isHex(**ppc)) {
      UInt d = fromHex(**ppc);
      tl_assert(d < 16);
      *result = ((*result) << 4) | fromHex(**ppc);
      (*ppc)++;
      used++;
      if (used > limit) return False;
   }
   if (used == 0)
      return False;
   return True;
}

/* Parse two such numbers separated by a dash, or fail. */

static Bool parse_range ( UChar** ppc, Addr* result1, Addr* result2 )
{
   Bool ok = parse_Addr(ppc, result1);
   if (!ok)
      return False;
   if (**ppc != '-')
      return False;
   (*ppc)++;
   ok = parse_Addr(ppc, result2);
   if (!ok)
      return False;
   return True;
}

/* Parse a set of ranges separated by commas into 'ignoreRanges', or
   fail. */

static Bool parse_ignore_ranges ( UChar* str0 )
{
   Addr start, end;
   Bool ok;
   UChar*  str = str0;
   UChar** ppc = &str;
   ignoreRanges.used = 0;
   while (1) {
      ok = parse_range(ppc, &start, &end);
      if (!ok)
         return False;
      if (ignoreRanges.used >= M_IGNORE_RANGES)
         return False;
      ignoreRanges.start[ignoreRanges.used] = start;
      ignoreRanges.end[ignoreRanges.used] = end;
      ignoreRanges.used++;
      if (**ppc == 0)
         return True;
      if (**ppc != ',')
         return False;
      (*ppc)++;
   }
   /*NOTREACHED*/
   return False;
}


/* --------------- Load/store slow cases. --------------- */

static
#ifndef PERF_FAST_LOADV
INLINE
#endif
ULong mc_LOADVn_slow ( Addr a, SizeT nBits, Bool bigendian )
{
   /* Make up a 64-bit result V word, which contains the loaded data for
      valid addresses and Defined for invalid addresses.  Iterate over
      the bytes in the word, from the most significant down to the
      least. */
   ULong vbits64     = V_BITS64_UNDEFINED;
   SizeT szB         = nBits / 8;
   SSizeT i;                        // Must be signed.
   SizeT n_addrs_bad = 0;
   Addr  ai;
   Bool  partial_load_exemption_applies;
   UChar vbits8;
   Bool  ok;

   PROF_EVENT(30, "mc_LOADVn_slow");

   /* ------------ BEGIN semi-fast cases ------------ */
   /* These deal quickly-ish with the common auxiliary primary map
      cases on 64-bit platforms.  Are merely a speedup hack; can be
      omitted without loss of correctness/functionality.  Note that in
      both cases the "sizeof(void*) == 8" causes these cases to be
      folded out by compilers on 32-bit platforms.  These are derived
      from LOADV64 and LOADV32.
   */
   if (LIKELY(sizeof(void*) == 8 
                      && nBits == 64 && VG_IS_8_ALIGNED(a))) {
      SecMap* sm       = get_secmap_for_reading(a);
      UWord   sm_off16 = SM_OFF_16(a);
      UWord   vabits16 = ((UShort*)(sm->vabits8))[sm_off16];
      if (LIKELY(vabits16 == VA_BITS16_DEFINED))
         return V_BITS64_DEFINED;
      if (LIKELY(vabits16 == VA_BITS16_UNDEFINED))
         return V_BITS64_UNDEFINED;
      /* else fall into the slow case */
   }
   if (LIKELY(sizeof(void*) == 8 
                      && nBits == 32 && VG_IS_4_ALIGNED(a))) {
      SecMap* sm = get_secmap_for_reading(a);
      UWord sm_off = SM_OFF(a);
      UWord vabits8 = sm->vabits8[sm_off];
      if (LIKELY(vabits8 == VA_BITS8_DEFINED))
         return ((UWord)0xFFFFFFFF00000000ULL | (UWord)V_BITS32_DEFINED);
      if (LIKELY(vabits8 == VA_BITS8_UNDEFINED))
         return ((UWord)0xFFFFFFFF00000000ULL | (UWord)V_BITS32_UNDEFINED);
      /* else fall into slow case */
   }
   /* ------------ END semi-fast cases ------------ */

   tl_assert(nBits == 64 || nBits == 32 || nBits == 16 || nBits == 8);

   for (i = szB-1; i >= 0; i--) {
      PROF_EVENT(31, "mc_LOADVn_slow(loop)");
      ai = a + byte_offset_w(szB, bigendian, i);
      ok = get_vbits8(ai, &vbits8);
      if (!ok) n_addrs_bad++;
      vbits64 <<= 8; 
      vbits64 |= vbits8;
   }

   /* This is a hack which avoids producing errors for code which
      insists in stepping along byte strings in aligned word-sized
      chunks, and there is a partially defined word at the end.  (eg,
      optimised strlen).  Such code is basically broken at least WRT
      semantics of ANSI C, but sometimes users don't have the option
      to fix it, and so this option is provided.  Note it is now
      defaulted to not-engaged.

      A load from a partially-addressible place is allowed if:
      - the command-line flag is set
      - it's a word-sized, word-aligned load
      - at least one of the addresses in the word *is* valid
   */
   partial_load_exemption_applies
      = MC_(clo_partial_loads_ok) && szB == VG_WORDSIZE 
                                   && VG_IS_WORD_ALIGNED(a) 
                                   && n_addrs_bad < VG_WORDSIZE;

   if (n_addrs_bad > 0 && !partial_load_exemption_applies)
      MC_(record_address_error)( VG_(get_running_tid)(), a, szB, False );

   return vbits64;
}


static
#ifndef PERF_FAST_STOREV
INLINE
#endif
void mc_STOREVn_slow ( Addr a, SizeT nBits, ULong vbytes, Bool bigendian )
{
   SizeT szB = nBits / 8;
   SizeT i, n_addrs_bad = 0;
   UChar vbits8;
   Addr  ai;
   Bool  ok;

   PROF_EVENT(35, "mc_STOREVn_slow");

   /* ------------ BEGIN semi-fast cases ------------ */
   /* These deal quickly-ish with the common auxiliary primary map
      cases on 64-bit platforms.  Are merely a speedup hack; can be
      omitted without loss of correctness/functionality.  Note that in
      both cases the "sizeof(void*) == 8" causes these cases to be
      folded out by compilers on 32-bit platforms.  These are derived
      from STOREV64 and STOREV32.
   */
   if (LIKELY(sizeof(void*) == 8 
                      && nBits == 64 && VG_IS_8_ALIGNED(a))) {
      SecMap* sm       = get_secmap_for_reading(a);
      UWord   sm_off16 = SM_OFF_16(a);
      UWord   vabits16 = ((UShort*)(sm->vabits8))[sm_off16];
      if (LIKELY( !is_distinguished_sm(sm) && 
                          (VA_BITS16_DEFINED   == vabits16 ||
                           VA_BITS16_UNDEFINED == vabits16) )) {
         /* Handle common case quickly: a is suitably aligned, */
         /* is mapped, and is addressible. */
         // Convert full V-bits in register to compact 2-bit form.
         if (LIKELY(V_BITS64_DEFINED == vbytes)) {
            ((UShort*)(sm->vabits8))[sm_off16] = (UShort)VA_BITS16_DEFINED;
            return;
         } else if (V_BITS64_UNDEFINED == vbytes) {
            ((UShort*)(sm->vabits8))[sm_off16] = (UShort)VA_BITS16_UNDEFINED;
            return;
         }
         /* else fall into the slow case */
      }
      /* else fall into the slow case */
   }
   if (LIKELY(sizeof(void*) == 8
                      && nBits == 32 && VG_IS_4_ALIGNED(a))) {
      SecMap* sm      = get_secmap_for_reading(a);
      UWord   sm_off  = SM_OFF(a);
      UWord   vabits8 = sm->vabits8[sm_off];
      if (LIKELY( !is_distinguished_sm(sm) && 
                          (VA_BITS8_DEFINED   == vabits8 ||
                           VA_BITS8_UNDEFINED == vabits8) )) {
         /* Handle common case quickly: a is suitably aligned, */
         /* is mapped, and is addressible. */
         // Convert full V-bits in register to compact 2-bit form.
         if (LIKELY(V_BITS32_DEFINED == (vbytes & 0xFFFFFFFF))) {
            sm->vabits8[sm_off] = VA_BITS8_DEFINED;
            return;
         } else if (V_BITS32_UNDEFINED == (vbytes & 0xFFFFFFFF)) {
            sm->vabits8[sm_off] = VA_BITS8_UNDEFINED;
            return;
         }
         /* else fall into the slow case */
      }
      /* else fall into the slow case */
   }
   /* ------------ END semi-fast cases ------------ */

   tl_assert(nBits == 64 || nBits == 32 || nBits == 16 || nBits == 8);

   /* Dump vbytes in memory, iterating from least to most significant
      byte.  At the same time establish addressibility of the location. */
   for (i = 0; i < szB; i++) {
      PROF_EVENT(36, "mc_STOREVn_slow(loop)");
      ai     = a + byte_offset_w(szB, bigendian, i);
      vbits8 = vbytes & 0xff;
      ok     = set_vbits8(ai, vbits8);
      if (!ok) n_addrs_bad++;
      vbytes >>= 8;
   }

   /* If an address error has happened, report it. */
   if (n_addrs_bad > 0)
      MC_(record_address_error)( VG_(get_running_tid)(), a, szB, True );
}


/*------------------------------------------------------------*/
/*--- Setting permissions over address ranges.             ---*/
/*------------------------------------------------------------*/

static void set_address_range_perms ( Addr a, SizeT lenT, UWord vabits16,
                                      UWord dsm_num )
{
   UWord    sm_off, sm_off16;
   UWord    vabits2 = vabits16 & 0x3;
   SizeT    lenA, lenB, len_to_next_secmap;
   Addr     aNext;
   SecMap*  sm;
   SecMap** sm_ptr;
   SecMap*  example_dsm;

   PROF_EVENT(150, "set_address_range_perms");

   /* Check the V+A bits make sense. */
   tl_assert(VA_BITS16_NOACCESS  == vabits16 ||
             VA_BITS16_UNDEFINED == vabits16 ||
             VA_BITS16_DEFINED   == vabits16);

   // This code should never write PDBs;  ensure this.  (See comment above
   // set_vabits2().)
   tl_assert(VA_BITS2_PARTDEFINED != vabits2);

   if (lenT == 0)
      return;

   if (lenT > 256 * 1024 * 1024) {
      if (VG_(clo_verbosity) > 0 && !VG_(clo_xml)) {
         Char* s = "unknown???";
         if (vabits16 == VA_BITS16_NOACCESS ) s = "noaccess";
         if (vabits16 == VA_BITS16_UNDEFINED) s = "undefined";
         if (vabits16 == VA_BITS16_DEFINED  ) s = "defined";
         VG_(message)(Vg_UserMsg, "Warning: set address range perms: "
                                  "large range [0x%lx, 0x%lx) (%s)",
                                  a, a + lenT, s);
      }
   }

#ifndef PERF_FAST_SARP
   /*------------------ debug-only case ------------------ */
   {
      // Endianness doesn't matter here because all bytes are being set to
      // the same value.
      // Nb: We don't have to worry about updating the sec-V-bits table
      // after these set_vabits2() calls because this code never writes
      // VA_BITS2_PARTDEFINED values.
      SizeT i;
      for (i = 0; i < lenT; i++) {
         set_vabits2(a + i, vabits2);
      }
      return;
   }
#endif

   /*------------------ standard handling ------------------ */

   /* Get the distinguished secondary that we might want
      to use (part of the space-compression scheme). */
   example_dsm = &sm_distinguished[dsm_num];

   // We have to handle ranges covering various combinations of partial and
   // whole sec-maps.  Here is how parts 1, 2 and 3 are used in each case.
   // Cases marked with a '*' are common.
   //
   //   TYPE                                             PARTS USED
   //   ----                                             ----------
   // * one partial sec-map                  (p)         1
   // - one whole sec-map                    (P)         2
   //
   // * two partial sec-maps                 (pp)        1,3 
   // - one partial, one whole sec-map       (pP)        1,2
   // - one whole, one partial sec-map       (Pp)        2,3
   // - two whole sec-maps                   (PP)        2,2
   //
   // * one partial, one whole, one partial  (pPp)       1,2,3
   // - one partial, two whole               (pPP)       1,2,2
   // - two whole, one partial               (PPp)       2,2,3
   // - three whole                          (PPP)       2,2,2
   //
   // * one partial, N-2 whole, one partial  (pP...Pp)   1,2...2,3
   // - one partial, N-1 whole               (pP...PP)   1,2...2,2
   // - N-1 whole, one partial               (PP...Pp)   2,2...2,3
   // - N whole                              (PP...PP)   2,2...2,3

   // Break up total length (lenT) into two parts:  length in the first
   // sec-map (lenA), and the rest (lenB);   lenT == lenA + lenB.
   aNext = start_of_this_sm(a) + SM_SIZE;
   len_to_next_secmap = aNext - a;
   if ( lenT <= len_to_next_secmap ) {
      // Range entirely within one sec-map.  Covers almost all cases.
      PROF_EVENT(151, "set_address_range_perms-single-secmap");
      lenA = lenT;
      lenB = 0;
   } else if (is_start_of_sm(a)) {
      // Range spans at least one whole sec-map, and starts at the beginning
      // of a sec-map; skip to Part 2.
      PROF_EVENT(152, "set_address_range_perms-startof-secmap");
      lenA = 0;
      lenB = lenT;
      goto part2;
   } else {
      // Range spans two or more sec-maps, first one is partial.
      PROF_EVENT(153, "set_address_range_perms-multiple-secmaps");
      lenA = len_to_next_secmap;
      lenB = lenT - lenA;
   }

   //------------------------------------------------------------------------
   // Part 1: Deal with the first sec_map.  Most of the time the range will be
   // entirely within a sec_map and this part alone will suffice.  Also,
   // doing it this way lets us avoid repeatedly testing for the crossing of
   // a sec-map boundary within these loops.
   //------------------------------------------------------------------------

   // If it's distinguished, make it undistinguished if necessary.
   sm_ptr = get_secmap_ptr(a);
   if (is_distinguished_sm(*sm_ptr)) {
      if (*sm_ptr == example_dsm) {
         // Sec-map already has the V+A bits that we want, so skip.
         PROF_EVENT(154, "set_address_range_perms-dist-sm1-quick");
         a    = aNext;
         lenA = 0;
      } else {
         PROF_EVENT(155, "set_address_range_perms-dist-sm1");
         *sm_ptr = copy_for_writing(*sm_ptr);
      }
   }
   sm = *sm_ptr;

   // 1 byte steps
   while (True) {
      if (VG_IS_8_ALIGNED(a)) break;
      if (lenA < 1)           break;
      PROF_EVENT(156, "set_address_range_perms-loop1a");
      sm_off = SM_OFF(a);
      insert_vabits2_into_vabits8( a, vabits2, &(sm->vabits8[sm_off]) );
      a    += 1;
      lenA -= 1;
   }
   // 8-aligned, 8 byte steps
   while (True) {
      if (lenA < 8) break;
      PROF_EVENT(157, "set_address_range_perms-loop8a");
      sm_off16 = SM_OFF_16(a);
      ((UShort*)(sm->vabits8))[sm_off16] = vabits16;
      a    += 8;
      lenA -= 8;
   }
   // 1 byte steps
   while (True) {
      if (lenA < 1) break;
      PROF_EVENT(158, "set_address_range_perms-loop1b");
      sm_off = SM_OFF(a);
      insert_vabits2_into_vabits8( a, vabits2, &(sm->vabits8[sm_off]) );
      a    += 1;
      lenA -= 1;
   }

   // We've finished the first sec-map.  Is that it?
   if (lenB == 0)
      return;

   //------------------------------------------------------------------------
   // Part 2: Fast-set entire sec-maps at a time.
   //------------------------------------------------------------------------
  part2:
   // 64KB-aligned, 64KB steps.
   // Nb: we can reach here with lenB < SM_SIZE
   tl_assert(0 == lenA);
   while (True) {
      if (lenB < SM_SIZE) break;
      tl_assert(is_start_of_sm(a));
      PROF_EVENT(159, "set_address_range_perms-loop64K");
      sm_ptr = get_secmap_ptr(a);
      if (!is_distinguished_sm(*sm_ptr)) {
         PROF_EVENT(160, "set_address_range_perms-loop64K-free-dist-sm");
         // Free the non-distinguished sec-map that we're replacing.  This
         // case happens moderately often, enough to be worthwhile.
         VG_(am_munmap_valgrind)((Addr)*sm_ptr, sizeof(SecMap));
      }
      update_SM_counts(*sm_ptr, example_dsm);
      // Make the sec-map entry point to the example DSM
      *sm_ptr = example_dsm;
      lenB -= SM_SIZE;
      a    += SM_SIZE;
   }

   // We've finished the whole sec-maps.  Is that it?
   if (lenB == 0)
      return;

   //------------------------------------------------------------------------
   // Part 3: Finish off the final partial sec-map, if necessary.
   //------------------------------------------------------------------------

   tl_assert(is_start_of_sm(a) && lenB < SM_SIZE);

   // If it's distinguished, make it undistinguished if necessary.
   sm_ptr = get_secmap_ptr(a);
   if (is_distinguished_sm(*sm_ptr)) {
      if (*sm_ptr == example_dsm) {
         // Sec-map already has the V+A bits that we want, so stop.
         PROF_EVENT(161, "set_address_range_perms-dist-sm2-quick");
         return;
      } else {
         PROF_EVENT(162, "set_address_range_perms-dist-sm2");
         *sm_ptr = copy_for_writing(*sm_ptr);
      }
   }
   sm = *sm_ptr;

   // 8-aligned, 8 byte steps
   while (True) {
      if (lenB < 8) break;
      PROF_EVENT(163, "set_address_range_perms-loop8b");
      sm_off16 = SM_OFF_16(a);
      ((UShort*)(sm->vabits8))[sm_off16] = vabits16;
      a    += 8;
      lenB -= 8;
   }
   // 1 byte steps
   while (True) {
      if (lenB < 1) return;
      PROF_EVENT(164, "set_address_range_perms-loop1c");
      sm_off = SM_OFF(a);
      insert_vabits2_into_vabits8( a, vabits2, &(sm->vabits8[sm_off]) );
      a    += 1;
      lenB -= 1;
   }
}


/* --- Set permissions for arbitrary address ranges --- */

void MC_(make_mem_noaccess) ( Addr a, SizeT len )
{
   PROF_EVENT(40, "MC_(make_mem_noaccess)");
   DEBUG("MC_(make_mem_noaccess)(%p, %lu)\n", a, len);
   set_address_range_perms ( a, len, VA_BITS16_NOACCESS, SM_DIST_NOACCESS );
   if (UNLIKELY( MC_(clo_mc_level) == 3 ))
      ocache_sarp_Clear_Origins ( a, len );
}

static void make_mem_undefined ( Addr a, SizeT len )
{
   PROF_EVENT(41, "make_mem_undefined");
   DEBUG("make_mem_undefined(%p, %lu)\n", a, len);
   set_address_range_perms ( a, len, VA_BITS16_UNDEFINED, SM_DIST_UNDEFINED );
}

void MC_(make_mem_undefined_w_otag) ( Addr a, SizeT len, UInt otag )
{
   PROF_EVENT(41, "MC_(make_mem_undefined)");
   DEBUG("MC_(make_mem_undefined)(%p, %lu)\n", a, len);
   set_address_range_perms ( a, len, VA_BITS16_UNDEFINED, SM_DIST_UNDEFINED );
   if (UNLIKELY( MC_(clo_mc_level) == 3 ))
      ocache_sarp_Set_Origins ( a, len, otag );
}

static
void make_mem_undefined_w_tid_and_okind ( Addr a, SizeT len,
                                          ThreadId tid, UInt okind )
{
   UInt        ecu;
   ExeContext* here;
   /* VG_(record_ExeContext) checks for validity of tid, and asserts
      if it is invalid.  So no need to do it here. */
   tl_assert(okind <= 3);
   here = VG_(record_ExeContext)( tid, 0/*first_ip_delta*/ );
   tl_assert(here);
   ecu = VG_(get_ECU_from_ExeContext)(here);
   tl_assert(VG_(is_plausible_ECU)(ecu));
   MC_(make_mem_undefined_w_otag) ( a, len, ecu | okind );
}

static
void make_mem_undefined_w_tid ( Addr a, SizeT len, ThreadId tid ) {
   make_mem_undefined_w_tid_and_okind ( a, len, tid, MC_OKIND_UNKNOWN );
}


void MC_(make_mem_defined) ( Addr a, SizeT len )
{
   PROF_EVENT(42, "MC_(make_mem_defined)");
   DEBUG("MC_(make_mem_defined)(%p, %lu)\n", a, len);
   set_address_range_perms ( a, len, VA_BITS16_DEFINED, SM_DIST_DEFINED );
   if (UNLIKELY( MC_(clo_mc_level) == 3 ))
      ocache_sarp_Clear_Origins ( a, len );
}

/* For each byte in [a,a+len), if the byte is addressable, make it be
   defined, but if it isn't addressible, leave it alone.  In other
   words a version of MC_(make_mem_defined) that doesn't mess with
   addressibility.  Low-performance implementation. */
static void make_mem_defined_if_addressable ( Addr a, SizeT len )
{
   SizeT i;
   UChar vabits2;
   DEBUG("make_mem_defined_if_addressable(%p, %llu)\n", a, (ULong)len);
   for (i = 0; i < len; i++) {
      vabits2 = get_vabits2( a+i );
      if (LIKELY(VA_BITS2_NOACCESS != vabits2)) {
         set_vabits2(a+i, VA_BITS2_DEFINED);
         if (UNLIKELY(MC_(clo_mc_level) >= 3)) {
            MC_(helperc_b_store1)( a+i, 0 ); /* clear the origin tag */
         } 
      }
   }
}


/* --- Block-copy permissions (needed for implementing realloc() and
       sys_mremap). --- */

void MC_(copy_address_range_state) ( Addr src, Addr dst, SizeT len )
{
   SizeT i, j;
   UChar vabits2, vabits8;
   Bool  aligned, nooverlap;

   DEBUG("MC_(copy_address_range_state)\n");
   PROF_EVENT(50, "MC_(copy_address_range_state)");

   if (len == 0 || src == dst)
      return;

   aligned   = VG_IS_4_ALIGNED(src) && VG_IS_4_ALIGNED(dst);
   nooverlap = src+len <= dst || dst+len <= src;

   if (nooverlap && aligned) {

      /* Vectorised fast case, when no overlap and suitably aligned */
      /* vector loop */
      i = 0;
      while (len >= 4) {
         vabits8 = get_vabits8_for_aligned_word32( src+i );
         set_vabits8_for_aligned_word32( dst+i, vabits8 );
         if (LIKELY(VA_BITS8_DEFINED == vabits8 
                            || VA_BITS8_UNDEFINED == vabits8 
                            || VA_BITS8_NOACCESS == vabits8)) {
            /* do nothing */
         } else {
            /* have to copy secondary map info */
            if (VA_BITS2_PARTDEFINED == get_vabits2( src+i+0 ))
               set_sec_vbits8( dst+i+0, get_sec_vbits8( src+i+0 ) );
            if (VA_BITS2_PARTDEFINED == get_vabits2( src+i+1 ))
               set_sec_vbits8( dst+i+1, get_sec_vbits8( src+i+1 ) );
            if (VA_BITS2_PARTDEFINED == get_vabits2( src+i+2 ))
               set_sec_vbits8( dst+i+2, get_sec_vbits8( src+i+2 ) );
            if (VA_BITS2_PARTDEFINED == get_vabits2( src+i+3 ))
               set_sec_vbits8( dst+i+3, get_sec_vbits8( src+i+3 ) );
         }
         i += 4;
         len -= 4;
      }
      /* fixup loop */
      while (len >= 1) {
         vabits2 = get_vabits2( src+i );
         set_vabits2( dst+i, vabits2 );
         if (VA_BITS2_PARTDEFINED == vabits2) {
            set_sec_vbits8( dst+i, get_sec_vbits8( src+i ) );
         }
         i++;
         len--;
      }

   } else {

      /* We have to do things the slow way */
      if (src < dst) {
         for (i = 0, j = len-1; i < len; i++, j--) {
            PROF_EVENT(51, "MC_(copy_address_range_state)(loop)");
            vabits2 = get_vabits2( src+j );
            set_vabits2( dst+j, vabits2 );
            if (VA_BITS2_PARTDEFINED == vabits2) {
               set_sec_vbits8( dst+j, get_sec_vbits8( src+j ) );
            }
         }
      }

      if (src > dst) {
         for (i = 0; i < len; i++) {
            PROF_EVENT(52, "MC_(copy_address_range_state)(loop)");
            vabits2 = get_vabits2( src+i );
            set_vabits2( dst+i, vabits2 );
            if (VA_BITS2_PARTDEFINED == vabits2) {
               set_sec_vbits8( dst+i, get_sec_vbits8( src+i ) );
            }
         }
      }
   }

}


/*------------------------------------------------------------*/
/*--- Origin tracking stuff - cache basics                 ---*/
/*------------------------------------------------------------*/

/* AN OVERVIEW OF THE ORIGIN TRACKING IMPLEMENTATION
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Note that this implementation draws inspiration from the "origin
   tracking by value piggybacking" scheme described in "Tracking Bad
   Apples: Reporting the Origin of Null and Undefined Value Errors"
   (Michael Bond, Nicholas Nethercote, Stephen Kent, Samuel Guyer,
   Kathryn McKinley, OOPSLA07, Montreal, Oct 2007) but in fact it is
   implemented completely differently.

   Origin tags and ECUs -- about the shadow values
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   This implementation tracks the defining point of all uninitialised
   values using so called "origin tags", which are 32-bit integers,
   rather than using the values themselves to encode the origins.  The
   latter, so-called value piggybacking", is what the OOPSLA07 paper
   describes.

   Origin tags, as tracked by the machinery below, are 32-bit unsigned
   ints (UInts), regardless of the machine's word size.  Each tag
   comprises an upper 30-bit ECU field and a lower 2-bit
   'kind' field.  The ECU field is a number given out by m_execontext
   and has a 1-1 mapping with ExeContext*s.  An ECU can be used
   directly as an origin tag (otag), but in fact we want to put
   additional information 'kind' field to indicate roughly where the
   tag came from.  This helps print more understandable error messages
   for the user -- it has no other purpose.  In summary:

   * Both ECUs and origin tags are represented as 32-bit words

   * m_execontext and the core-tool interface deal purely in ECUs.
     They have no knowledge of origin tags - that is a purely
     Memcheck-internal matter.

   * all valid ECUs have the lowest 2 bits zero and at least
     one of the upper 30 bits nonzero (see VG_(is_plausible_ECU))

   * to convert from an ECU to an otag, OR in one of the MC_OKIND_
     constants defined in mc_include.h.

   * to convert an otag back to an ECU, AND it with ~3

   One important fact is that no valid otag is zero.  A zero otag is
   used by the implementation to indicate "no origin", which could
   mean that either the value is defined, or it is undefined but the
   implementation somehow managed to lose the origin.

   The ECU used for memory created by malloc etc is derived from the
   stack trace at the time the malloc etc happens.  This means the
   mechanism can show the exact allocation point for heap-created
   uninitialised values.

   In contrast, it is simply too expensive to create a complete
   backtrace for each stack allocation.  Therefore we merely use a
   depth-1 backtrace for stack allocations, which can be done once at
   translation time, rather than N times at run time.  The result of
   this is that, for stack created uninitialised values, Memcheck can
   only show the allocating function, and not what called it.
   Furthermore, compilers tend to move the stack pointer just once at
   the start of the function, to allocate all locals, and so in fact
   the stack origin almost always simply points to the opening brace
   of the function.  Net result is, for stack origins, the mechanism
   can tell you in which function the undefined value was created, but
   that's all.  Users will need to carefully check all locals in the
   specified function.

   Shadowing registers and memory
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Memory is shadowed using a two level cache structure (ocacheL1 and
   ocacheL2).  Memory references are first directed to ocacheL1.  This
   is a traditional 2-way set associative cache with 32-byte lines and
   approximate LRU replacement within each set.

   A naive implementation would require storing one 32 bit otag for
   each byte of memory covered, a 4:1 space overhead.  Instead, there
   is one otag for every 4 bytes of memory covered, plus a 4-bit mask
   that shows which of the 4 bytes have that shadow value and which
   have a shadow value of zero (indicating no origin).  Hence a lot of
   space is saved, but the cost is that only one different origin per
   4 bytes of address space can be represented.  This is a source of
   imprecision, but how much of a problem it really is remains to be
   seen.

   A cache line that contains all zeroes ("no origins") contains no
   useful information, and can be ejected from the L1 cache "for
   free", in the sense that a read miss on the L1 causes a line of
   zeroes to be installed.  However, ejecting a line containing
   nonzeroes risks losing origin information permanently.  In order to
   prevent such lossage, ejected nonzero lines are placed in a
   secondary cache (ocacheL2), which is an OSet (AVL tree) of cache
   lines.  This can grow arbitrarily large, and so should ensure that
   Memcheck runs out of memory in preference to losing useful origin
   info due to cache size limitations.

   Shadowing registers is a bit tricky, because the shadow values are
   32 bits, regardless of the size of the register.  That gives a
   problem for registers smaller than 32 bits.  The solution is to
   find spaces in the guest state that are unused, and use those to
   shadow guest state fragments smaller than 32 bits.  For example, on
   ppc32/64, each vector register is 16 bytes long.  If 4 bytes of the
   shadow are allocated for the register's otag, then there are still
   12 bytes left over which could be used to shadow 3 other values.

   This implies there is some non-obvious mapping from guest state
   (start,length) pairs to the relevant shadow offset (for the origin
   tags).  And it is unfortunately guest-architecture specific.  The
   mapping is contained in mc_machine.c, which is quite lengthy but
   straightforward.

   Instrumenting the IR
   ~~~~~~~~~~~~~~~~~~~~

   Instrumentation is largely straightforward, and done by the
   functions schemeE and schemeS in mc_translate.c.  These generate
   code for handling the origin tags of expressions (E) and statements
   (S) respectively.  The rather strange names are a reference to the
   "compilation schemes" shown in Simon Peyton Jones' book "The
   Implementation of Functional Programming Languages" (Prentice Hall,
   1987, see
   http://research.microsoft.com/~simonpj/papers/slpj-book-1987/index.htm).

   schemeS merely arranges to move shadow values around the guest
   state to track the incoming IR.  schemeE is largely trivial too.
   The only significant point is how to compute the otag corresponding
   to binary (or ternary, quaternary, etc) operator applications.  The
   rule is simple: just take whichever value is larger (32-bit
   unsigned max).  Constants get the special value zero.  Hence this
   rule always propagates a nonzero (known) otag in preference to a
   zero (unknown, or more likely, value-is-defined) tag, as we want.
   If two different undefined values are inputs to a binary operator
   application, then which is propagated is arbitrary, but that
   doesn't matter, since the program is erroneous in using either of
   the values, and so there's no point in attempting to propagate
   both.

   Since constants are abstracted to (otag) zero, much of the
   instrumentation code can be folded out without difficulty by the
   generic post-instrumentation IR cleanup pass, using these rules:
   Max32U(0,x) -> x, Max32U(x,0) -> x, Max32(x,y) where x and y are
   constants is evaluated at JIT time.  And the resulting dead code
   removal.  In practice this causes surprisingly few Max32Us to
   survive through to backend code generation.

   Integration with the V-bits machinery
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   This is again largely straightforward.  Mostly the otag and V bits
   stuff are independent.  The only point of interaction is when the V
   bits instrumenter creates a call to a helper function to report an
   uninitialised value error -- in that case it must first use schemeE
   to get hold of the origin tag expression for the value, and pass
   that to the helper too.

   There is the usual stuff to do with setting address range
   permissions.  When memory is painted undefined, we must also know
   the origin tag to paint with, which involves some tedious plumbing,
   particularly to do with the fast case stack handlers.  When memory
   is painted defined or noaccess then the origin tags must be forced
   to zero.

   One of the goals of the implementation was to ensure that the
   non-origin tracking mode isn't slowed down at all.  To do this,
   various functions to do with memory permissions setting (again,
   mostly pertaining to the stack) are duplicated for the with- and
   without-otag case.

   Dealing with stack redzones, and the NIA cache
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   This is one of the few non-obvious parts of the implementation.

   Some ABIs (amd64-ELF, ppc64-ELF, ppc32/64-XCOFF) define a small
   reserved area below the stack pointer, that can be used as scratch
   space by compiler generated code for functions.  In the Memcheck
   sources this is referred to as the "stack redzone".  The important
   thing here is that such redzones are considered volatile across
   function calls and returns.  So Memcheck takes care to mark them as
   undefined for each call and return, on the afflicted platforms.
   Past experience shows this is essential in order to get reliable
   messages about uninitialised values that come from the stack.

   So the question is, when we paint a redzone undefined, what origin
   tag should we use for it?  Consider a function f() calling g().  If
   we paint the redzone using an otag derived from the ExeContext of
   the CALL/BL instruction in f, then any errors in g causing it to
   use uninitialised values that happen to lie in the redzone, will be
   reported as having their origin in f.  Which is highly confusing.

   The same applies for returns: if, on a return, we paint the redzone
   using a origin tag derived from the ExeContext of the RET/BLR
   instruction in g, then any later errors in f causing it to use
   uninitialised values in the redzone, will be reported as having
   their origin in g.  Which is just as confusing.

   To do it right, in both cases we need to use an origin tag which
   pertains to the instruction which dynamically follows the CALL/BL
   or RET/BLR.  In short, one derived from the NIA - the "next
   instruction address".

   To make this work, Memcheck's redzone-painting helper,
   MC_(helperc_MAKE_STACK_UNINIT), now takes a third argument, the
   NIA.  It converts the NIA to a 1-element ExeContext, and uses that
   ExeContext's ECU as the basis for the otag used to paint the
   redzone.  The expensive part of this is converting an NIA into an
   ECU, since this happens once for every call and every return.  So
   we use a simple 511-line, 2-way set associative cache
   (nia_to_ecu_cache) to cache the mappings, and that knocks most of
   the cost out.

   Further background comments
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~

   > Question: why is otag a UInt?  Wouldn't a UWord be better?  Isn't
   > it really just the address of the relevant ExeContext?

   Well, it's not the address, but a value which has a 1-1 mapping
   with ExeContexts, and is guaranteed not to be zero, since zero
   denotes (to memcheck) "unknown origin or defined value".  So these
   UInts are just numbers starting at 4 and incrementing by 4; each
   ExeContext is given a number when it is created.  (*** NOTE this
   confuses otags and ECUs; see comments above ***).

   Making these otags 32-bit regardless of the machine's word size
   makes the 64-bit implementation easier (next para).  And it doesn't
   really limit us in any way, since for the tags to overflow would
   require that the program somehow caused 2^30-1 different
   ExeContexts to be created, in which case it is probably in deep
   trouble.  Not to mention V will have soaked up many tens of
   gigabytes of memory merely to store them all.

   So having 64-bit origins doesn't really buy you anything, and has
   the following downsides:

   Suppose that instead, an otag is a UWord.  This would mean that, on
   a 64-bit target,

   1. It becomes hard to shadow any element of guest state which is
      smaller than 8 bytes.  To do so means you'd need to find some
      8-byte-sized hole in the guest state which you don't want to
      shadow, and use that instead to hold the otag.  On ppc64, the
      condition code register(s) are split into 20 UChar sized pieces,
      all of which need to be tracked (guest_XER_SO .. guest_CR7_0)
      and so that would entail finding 160 bytes somewhere else in the
      guest state.

      Even on x86, I want to track origins for %AH .. %DH (bits 15:8
      of %EAX .. %EDX) that are separate from %AL .. %DL (bits 7:0 of
      same) and so I had to look for 4 untracked otag-sized areas in
      the guest state to make that possible.

      The same problem exists of course when origin tags are only 32
      bits, but it's less extreme.

   2. (More compelling) it doubles the size of the origin shadow
      memory.  Given that the shadow memory is organised as a fixed
      size cache, and that accuracy of tracking is limited by origins
      falling out the cache due to space conflicts, this isn't good.

   > Another question: is the origin tracking perfect, or are there
   > cases where it fails to determine an origin?

   It is imperfect for at least for the following reasons, and
   probably more:

   * Insufficient capacity in the origin cache.  When a line is
     evicted from the cache it is gone forever, and so subsequent
     queries for the line produce zero, indicating no origin
     information.  Interestingly, a line containing all zeroes can be
     evicted "free" from the cache, since it contains no useful
     information, so there is scope perhaps for some cleverer cache
     management schemes.  (*** NOTE, with the introduction of the
     second level origin tag cache, ocacheL2, this is no longer a
     problem. ***)

   * The origin cache only stores one otag per 32-bits of address
     space, plus 4 bits indicating which of the 4 bytes has that tag
     and which are considered defined.  The result is that if two
     undefined bytes in the same word are stored in memory, the first
     stored byte's origin will be lost and replaced by the origin for
     the second byte.

   * Nonzero origin tags for defined values.  Consider a binary
     operator application op(x,y).  Suppose y is undefined (and so has
     a valid nonzero origin tag), and x is defined, but erroneously
     has a nonzero origin tag (defined values should have tag zero).
     If the erroneous tag has a numeric value greater than y's tag,
     then the rule for propagating origin tags though binary
     operations, which is simply to take the unsigned max of the two
     tags, will erroneously propagate x's tag rather than y's.

   * Some obscure uses of x86/amd64 byte registers can cause lossage
     or confusion of origins.  %AH .. %DH are treated as different
     from, and unrelated to, their parent registers, %EAX .. %EDX.
     So some wierd sequences like

        movb undefined-value, %AH
        movb defined-value, %AL
        .. use %AX or %EAX ..

     will cause the origin attributed to %AH to be ignored, since %AL,
     %AX, %EAX are treated as the same register, and %AH as a
     completely separate one.

   But having said all that, it actually seems to work fairly well in
   practice.
*/

static UWord stats_ocacheL1_find           = 0;
static UWord stats_ocacheL1_found_at_1     = 0;
static UWord stats_ocacheL1_found_at_N     = 0;
static UWord stats_ocacheL1_misses         = 0;
static UWord stats_ocacheL1_lossage        = 0;
static UWord stats_ocacheL1_movefwds       = 0;

static UWord stats__ocacheL2_refs          = 0;
static UWord stats__ocacheL2_misses        = 0;
static UWord stats__ocacheL2_n_nodes_max   = 0;

/* Cache of 32-bit values, one every 32 bits of address space */

#define OC_BITS_PER_LINE 5
#define OC_W32S_PER_LINE (1 << (OC_BITS_PER_LINE - 2))

static INLINE UWord oc_line_offset ( Addr a ) {
   return (a >> 2) & (OC_W32S_PER_LINE - 1);
}
static INLINE Bool is_valid_oc_tag ( Addr tag ) {
   return 0 == (tag & ((1 << OC_BITS_PER_LINE) - 1));
}

#define OC_LINES_PER_SET 2

#define OC_N_SET_BITS    20
#define OC_N_SETS        (1 << OC_N_SET_BITS)

/* These settings give:
   64 bit host: ocache:  100,663,296 sizeB    67,108,864 useful
   32 bit host: ocache:   92,274,688 sizeB    67,108,864 useful
*/

#define OC_MOVE_FORWARDS_EVERY_BITS 7


typedef
   struct {
      Addr  tag;
      UInt  w32[OC_W32S_PER_LINE];
      UChar descr[OC_W32S_PER_LINE];
   }
   OCacheLine;

/* Classify and also sanity-check 'line'.  Return 'e' (empty) if not
   in use, 'n' (nonzero) if it contains at least one valid origin tag,
   and 'z' if all the represented tags are zero. */
static UChar classify_OCacheLine ( OCacheLine* line )
{
   UWord i;
   if (line->tag == 1/*invalid*/)
      return 'e'; /* EMPTY */
   tl_assert(is_valid_oc_tag(line->tag));
   for (i = 0; i < OC_W32S_PER_LINE; i++) {
      tl_assert(0 == ((~0xF) & line->descr[i]));
      if (line->w32[i] > 0 && line->descr[i] > 0)
         return 'n'; /* NONZERO - contains useful info */
   }
   return 'z'; /* ZERO - no useful info */
}

typedef
   struct {
      OCacheLine line[OC_LINES_PER_SET];
   }
   OCacheSet;

typedef
   struct {
      OCacheSet set[OC_N_SETS];
   }
   OCache;

static OCache* ocacheL1 = NULL;
static UWord   ocacheL1_event_ctr = 0;

static void init_ocacheL2 ( void ); /* fwds */
static void init_OCache ( void )
{
   UWord line, set;
   tl_assert(MC_(clo_mc_level) >= 3);
   tl_assert(ocacheL1 == NULL);
   ocacheL1 = VG_(am_shadow_alloc)(sizeof(OCache));
   if (ocacheL1 == NULL) {
      VG_(out_of_memory_NORETURN)( "memcheck:allocating ocacheL1", 
                                   sizeof(OCache) );
   }
   tl_assert(ocacheL1 != NULL);
   for (set = 0; set < OC_N_SETS; set++) {
      for (line = 0; line < OC_LINES_PER_SET; line++) {
         ocacheL1->set[set].line[line].tag = 1/*invalid*/;
      }
   }
   init_ocacheL2();
}

static void moveLineForwards ( OCacheSet* set, UWord lineno )
{
   OCacheLine tmp;
   stats_ocacheL1_movefwds++;
   tl_assert(lineno > 0 && lineno < OC_LINES_PER_SET);
   tmp = set->line[lineno-1];
   set->line[lineno-1] = set->line[lineno];
   set->line[lineno] = tmp;
}

static void zeroise_OCacheLine ( OCacheLine* line, Addr tag ) {
   UWord i;
   for (i = 0; i < OC_W32S_PER_LINE; i++) {
      line->w32[i] = 0; /* NO ORIGIN */
      line->descr[i] = 0; /* REALLY REALLY NO ORIGIN! */
   }
   line->tag = tag;
}

//////////////////////////////////////////////////////////////
//// OCache backing store

static OSet* ocacheL2 = NULL;

static void* ocacheL2_malloc ( HChar* cc, SizeT szB ) {
   return VG_(malloc)(cc, szB);
}
static void ocacheL2_free ( void* v ) {
   VG_(free)( v );
}

/* Stats: # nodes currently in tree */
static UWord stats__ocacheL2_n_nodes = 0;

static void init_ocacheL2 ( void )
{
   tl_assert(!ocacheL2);
   tl_assert(sizeof(Word) == sizeof(Addr)); /* since OCacheLine.tag :: Addr */
   tl_assert(0 == offsetof(OCacheLine,tag));
   ocacheL2 
      = VG_(OSetGen_Create)( offsetof(OCacheLine,tag), 
                             NULL, /* fast cmp */
                             ocacheL2_malloc, "mc.ioL2", ocacheL2_free );
   tl_assert(ocacheL2);
   stats__ocacheL2_n_nodes = 0;
}

/* Find line with the given tag in the tree, or NULL if not found. */
static OCacheLine* ocacheL2_find_tag ( Addr tag )
{
   OCacheLine* line;
   tl_assert(is_valid_oc_tag(tag));
   stats__ocacheL2_refs++;
   line = VG_(OSetGen_Lookup)( ocacheL2, &tag );
   return line;
}

/* Delete the line with the given tag from the tree, if it is present, and
   free up the associated memory. */
static void ocacheL2_del_tag ( Addr tag )
{
   OCacheLine* line;
   tl_assert(is_valid_oc_tag(tag));
   stats__ocacheL2_refs++;
   line = VG_(OSetGen_Remove)( ocacheL2, &tag );
   if (line) {
      VG_(OSetGen_FreeNode)(ocacheL2, line);
      tl_assert(stats__ocacheL2_n_nodes > 0);
      stats__ocacheL2_n_nodes--;
   }
}

/* Add a copy of the given line to the tree.  It must not already be
   present. */
static void ocacheL2_add_line ( OCacheLine* line )
{
   OCacheLine* copy;
   tl_assert(is_valid_oc_tag(line->tag));
   copy = VG_(OSetGen_AllocNode)( ocacheL2, sizeof(OCacheLine) );
   tl_assert(copy);
   *copy = *line;
   stats__ocacheL2_refs++;
   VG_(OSetGen_Insert)( ocacheL2, copy );
   stats__ocacheL2_n_nodes++;
   if (stats__ocacheL2_n_nodes > stats__ocacheL2_n_nodes_max)
      stats__ocacheL2_n_nodes_max = stats__ocacheL2_n_nodes;
}

////
//////////////////////////////////////////////////////////////

__attribute__((noinline))
static OCacheLine* find_OCacheLine_SLOW ( Addr a )
{
   OCacheLine *victim, *inL2;
   UChar c;
   UWord line;
   UWord setno   = (a >> OC_BITS_PER_LINE) & (OC_N_SETS - 1);
   UWord tagmask = ~((1 << OC_BITS_PER_LINE) - 1);
   UWord tag     = a & tagmask;
   tl_assert(setno >= 0 && setno < OC_N_SETS);

   /* we already tried line == 0; skip therefore. */
   for (line = 1; line < OC_LINES_PER_SET; line++) {
      if (ocacheL1->set[setno].line[line].tag == tag) {
         if (line == 1) {
            stats_ocacheL1_found_at_1++;
         } else {
            stats_ocacheL1_found_at_N++;
         }
         if (UNLIKELY(0 == (ocacheL1_event_ctr++ 
                            & ((1<<OC_MOVE_FORWARDS_EVERY_BITS)-1)))) {
            moveLineForwards( &ocacheL1->set[setno], line );
            line--;
         }
         return &ocacheL1->set[setno].line[line];
      }
   }

   /* A miss.  Use the last slot.  Implicitly this means we're
      ejecting the line in the last slot. */
   stats_ocacheL1_misses++;
   tl_assert(line == OC_LINES_PER_SET);
   line--;
   tl_assert(line > 0);

   /* First, move the to-be-ejected line to the L2 cache. */
   victim = &ocacheL1->set[setno].line[line];
   c = classify_OCacheLine(victim);
   switch (c) {
      case 'e':
         /* the line is empty (has invalid tag); ignore it. */
         break;
      case 'z':
         /* line contains zeroes.  We must ensure the backing store is
            updated accordingly, either by copying the line there
            verbatim, or by ensuring it isn't present there.  We
            chosse the latter on the basis that it reduces the size of
            the backing store. */
         ocacheL2_del_tag( victim->tag );
         break;
      case 'n':
         /* line contains at least one real, useful origin.  Copy it
            to the backing store. */
         stats_ocacheL1_lossage++;
         inL2 = ocacheL2_find_tag( victim->tag );
         if (inL2) {
            *inL2 = *victim;
         } else {
            ocacheL2_add_line( victim );
         }
         break;
      default:
         tl_assert(0);
   }

   /* Now we must reload the L1 cache from the backing tree, if
      possible. */
   tl_assert(tag != victim->tag); /* stay sane */
   inL2 = ocacheL2_find_tag( tag );
   if (inL2) {
      /* We're in luck.  It's in the L2. */
      ocacheL1->set[setno].line[line] = *inL2;
   } else {
      /* Missed at both levels of the cache hierarchy.  We have to
         declare it as full of zeroes (unknown origins). */
      stats__ocacheL2_misses++;
      zeroise_OCacheLine( &ocacheL1->set[setno].line[line], tag );
   }

   /* Move it one forwards */
   moveLineForwards( &ocacheL1->set[setno], line );
   line--;

   return &ocacheL1->set[setno].line[line];
}

static INLINE OCacheLine* find_OCacheLine ( Addr a )
{
   UWord setno   = (a >> OC_BITS_PER_LINE) & (OC_N_SETS - 1);
   UWord tagmask = ~((1 << OC_BITS_PER_LINE) - 1);
   UWord tag     = a & tagmask;

   stats_ocacheL1_find++;

   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(setno >= 0 && setno < OC_N_SETS);
      tl_assert(0 == (tag & (4 * OC_W32S_PER_LINE - 1)));
   }

   if (LIKELY(ocacheL1->set[setno].line[0].tag == tag)) {
      return &ocacheL1->set[setno].line[0];
   }

   return find_OCacheLine_SLOW( a );
}

static INLINE void set_aligned_word64_Origin_to_undef ( Addr a, UInt otag )
{
   //// BEGIN inlined, specialised version of MC_(helperc_b_store8)
   //// Set the origins for a+0 .. a+7
   { OCacheLine* line;
     UWord lineoff = oc_line_offset(a);
     if (OC_ENABLE_ASSERTIONS) {
        tl_assert(lineoff >= 0 
                  && lineoff < OC_W32S_PER_LINE -1/*'cos 8-aligned*/);
     }
     line = find_OCacheLine( a );
     line->descr[lineoff+0] = 0xF;
     line->descr[lineoff+1] = 0xF;
     line->w32[lineoff+0]   = otag;
     line->w32[lineoff+1]   = otag;
   }
   //// END inlined, specialised version of MC_(helperc_b_store8)
}


/*------------------------------------------------------------*/
/*--- Aligned fast case permission setters,                ---*/
/*--- for dealing with stacks                              ---*/
/*------------------------------------------------------------*/

/*--------------------- 32-bit ---------------------*/

/* Nb: by "aligned" here we mean 4-byte aligned */

static INLINE void make_aligned_word32_undefined ( Addr a )
{
   PROF_EVENT(300, "make_aligned_word32_undefined");

#ifndef PERF_FAST_STACK2
   make_mem_undefined(a, 4);
#else
   {
      UWord   sm_off;
      SecMap* sm;

      if (UNLIKELY(a > MAX_PRIMARY_ADDRESS)) {
         PROF_EVENT(301, "make_aligned_word32_undefined-slow1");
         make_mem_undefined(a, 4);
         return;
      }

      sm                  = get_secmap_for_writing_low(a);
      sm_off              = SM_OFF(a);
      sm->vabits8[sm_off] = VA_BITS8_UNDEFINED;
   }
#endif
}

static INLINE
void make_aligned_word32_undefined_w_otag ( Addr a, UInt otag )
{
   make_aligned_word32_undefined(a);
   //// BEGIN inlined, specialised version of MC_(helperc_b_store4)
   //// Set the origins for a+0 .. a+3
   { OCacheLine* line;
     UWord lineoff = oc_line_offset(a);
     if (OC_ENABLE_ASSERTIONS) {
        tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
     }
     line = find_OCacheLine( a );
     line->descr[lineoff] = 0xF;
     line->w32[lineoff]   = otag;
   }
   //// END inlined, specialised version of MC_(helperc_b_store4)
}

static INLINE
void make_aligned_word32_noaccess ( Addr a )
{
   PROF_EVENT(310, "make_aligned_word32_noaccess");

#ifndef PERF_FAST_STACK2
   MC_(make_mem_noaccess)(a, 4);
#else
   {
      UWord   sm_off;
      SecMap* sm;

      if (UNLIKELY(a > MAX_PRIMARY_ADDRESS)) {
         PROF_EVENT(311, "make_aligned_word32_noaccess-slow1");
         MC_(make_mem_noaccess)(a, 4);
         return;
      }

      sm                  = get_secmap_for_writing_low(a);
      sm_off              = SM_OFF(a);
      sm->vabits8[sm_off] = VA_BITS8_NOACCESS;

      //// BEGIN inlined, specialised version of MC_(helperc_b_store4)
      //// Set the origins for a+0 .. a+3.
      if (UNLIKELY( MC_(clo_mc_level) == 3 )) {
         OCacheLine* line;
         UWord lineoff = oc_line_offset(a);
         if (OC_ENABLE_ASSERTIONS) {
            tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
         }
         line = find_OCacheLine( a );
         line->descr[lineoff] = 0;
      }
      //// END inlined, specialised version of MC_(helperc_b_store4)
   }
#endif
}

/*--------------------- 64-bit ---------------------*/

/* Nb: by "aligned" here we mean 8-byte aligned */

static INLINE void make_aligned_word64_undefined ( Addr a )
{
   PROF_EVENT(320, "make_aligned_word64_undefined");

#ifndef PERF_FAST_STACK2
   make_mem_undefined(a, 8);
#else
   {
      UWord   sm_off16;
      SecMap* sm;

      if (UNLIKELY(a > MAX_PRIMARY_ADDRESS)) {
         PROF_EVENT(321, "make_aligned_word64_undefined-slow1");
         make_mem_undefined(a, 8);
         return;
      }

      sm       = get_secmap_for_writing_low(a);
      sm_off16 = SM_OFF_16(a);
      ((UShort*)(sm->vabits8))[sm_off16] = VA_BITS16_UNDEFINED;
   }
#endif
}

static INLINE
void make_aligned_word64_undefined_w_otag ( Addr a, UInt otag )
{
   make_aligned_word64_undefined(a);
   //// BEGIN inlined, specialised version of MC_(helperc_b_store8)
   //// Set the origins for a+0 .. a+7
   { OCacheLine* line;
     UWord lineoff = oc_line_offset(a);
     tl_assert(lineoff >= 0 
               && lineoff < OC_W32S_PER_LINE -1/*'cos 8-aligned*/);
     line = find_OCacheLine( a );
     line->descr[lineoff+0] = 0xF;
     line->descr[lineoff+1] = 0xF;
     line->w32[lineoff+0]   = otag;
     line->w32[lineoff+1]   = otag;
   }
   //// END inlined, specialised version of MC_(helperc_b_store8)
}

static INLINE
void make_aligned_word64_noaccess ( Addr a )
{
   PROF_EVENT(330, "make_aligned_word64_noaccess");

#ifndef PERF_FAST_STACK2
   MC_(make_mem_noaccess)(a, 8);
#else
   {
      UWord   sm_off16;
      SecMap* sm;

      if (UNLIKELY(a > MAX_PRIMARY_ADDRESS)) {
         PROF_EVENT(331, "make_aligned_word64_noaccess-slow1");
         MC_(make_mem_noaccess)(a, 8);
         return;
      }

      sm       = get_secmap_for_writing_low(a);
      sm_off16 = SM_OFF_16(a);
      ((UShort*)(sm->vabits8))[sm_off16] = VA_BITS16_NOACCESS;

      //// BEGIN inlined, specialised version of MC_(helperc_b_store8)
      //// Clear the origins for a+0 .. a+7.
      if (UNLIKELY( MC_(clo_mc_level) == 3 )) {
         OCacheLine* line;
         UWord lineoff = oc_line_offset(a);
         tl_assert(lineoff >= 0 
                   && lineoff < OC_W32S_PER_LINE -1/*'cos 8-aligned*/);
         line = find_OCacheLine( a );
         line->descr[lineoff+0] = 0;
         line->descr[lineoff+1] = 0;
      }
      //// END inlined, specialised version of MC_(helperc_b_store8)
   }
#endif
}


/*------------------------------------------------------------*/
/*--- Stack pointer adjustment                             ---*/
/*------------------------------------------------------------*/

#ifdef PERF_FAST_STACK
#  define MAYBE_USED
#else
#  define MAYBE_USED __attribute__((unused))
#endif

/*--------------- adjustment by 4 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_4_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(110, "new_mem_stack_4");
   if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 4, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_4(Addr new_SP)
{
   PROF_EVENT(110, "new_mem_stack_4");
   if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 4 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_4(Addr new_SP)
{
   PROF_EVENT(120, "die_mem_stack_4");
   if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-4 );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-4, 4 );
   }
}

/*--------------- adjustment by 8 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_8_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(111, "new_mem_stack_8");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP, otag );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP  , otag );
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+4, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 8, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_8(Addr new_SP)
{
   PROF_EVENT(111, "new_mem_stack_8");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP+4 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 8 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_8(Addr new_SP)
{
   PROF_EVENT(121, "die_mem_stack_8");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-8 );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-8 );
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-4 );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-8, 8 );
   }
}

/*--------------- adjustment by 12 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_12_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(112, "new_mem_stack_12");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP  , otag );
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8, otag );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* from previous test we don't have 8-alignment at offset +0,
         hence must have 8 alignment at offsets +4/-4.  Hence safe to
         do 4 at +0 and then 8 at +4/. */
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP  , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+4, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 12, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_12(Addr new_SP)
{
   PROF_EVENT(112, "new_mem_stack_12");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* from previous test we don't have 8-alignment at offset +0,
         hence must have 8 alignment at offsets +4/-4.  Hence safe to
         do 4 at +0 and then 8 at +4/. */
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+4 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 12 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_12(Addr new_SP)
{
   PROF_EVENT(122, "die_mem_stack_12");
   /* Note the -12 in the test */
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP-12 )) {
      /* We have 8-alignment at -12, hence ok to do 8 at -12 and 4 at
         -4. */
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-12 );
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-4  );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* We have 4-alignment at +0, but we don't have 8-alignment at
         -12.  So we must have 8-alignment at -8.  Hence do 4 at -12
         and then 8 at -8. */
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-12 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-8  );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-12, 12 );
   }
}

/*--------------- adjustment by 16 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_16_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(113, "new_mem_stack_16");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Have 8-alignment at +0, hence do 8 at +0 and 8 at +8. */
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP  , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8, otag );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Have 4 alignment at +0 but not 8; hence 8 must be at +4.
         Hence do 4 at +0, 8 at +4, 4 at +12. */
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP   , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+4 , otag );
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+12, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 16, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_16(Addr new_SP)
{
   PROF_EVENT(113, "new_mem_stack_16");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Have 8-alignment at +0, hence do 8 at +0 and 8 at +8. */
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Have 4 alignment at +0 but not 8; hence 8 must be at +4.
         Hence do 4 at +0, 8 at +4, 4 at +12. */
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+4  );
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP+12 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 16 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_16(Addr new_SP)
{
   PROF_EVENT(123, "die_mem_stack_16");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Have 8-alignment at +0, hence do 8 at -16 and 8 at -8. */
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-8  );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* 8 alignment must be at -12.  Do 4 at -16, 8 at -12, 4 at -4. */
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-12 );
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-4  );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-16, 16 );
   }
}

/*--------------- adjustment by 32 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_32_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(114, "new_mem_stack_32");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Straightforward */
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP   , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8 , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+16, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+24, otag );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* 8 alignment must be at +4.  Hence do 8 at +4,+12,+20 and 4 at
         +0,+28. */
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP   , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+4 , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+12, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+20, otag );
      make_aligned_word32_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+28, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 32, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_32(Addr new_SP)
{
   PROF_EVENT(114, "new_mem_stack_32");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Straightforward */
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+16 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+24 );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* 8 alignment must be at +4.  Hence do 8 at +4,+12,+20 and 4 at
         +0,+28. */
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+4 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+12 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+20 );
      make_aligned_word32_undefined ( -VG_STACK_REDZONE_SZB + new_SP+28 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 32 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_32(Addr new_SP)
{
   PROF_EVENT(124, "die_mem_stack_32");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* Straightforward */
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-32 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-24 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP- 8 );
   } else if (VG_IS_4_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      /* 8 alignment must be at -4 etc.  Hence do 8 at -12,-20,-28 and
         4 at -32,-4. */
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-32 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-28 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-20 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-12 );
      make_aligned_word32_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-4  );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-32, 32 );
   }
}

/*--------------- adjustment by 112 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_112_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(115, "new_mem_stack_112");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP   , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8 , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+16, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+24, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+32, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+40, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+48, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+56, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+64, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+72, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+80, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+88, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+96, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+104, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 112, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_112(Addr new_SP)
{
   PROF_EVENT(115, "new_mem_stack_112");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+16 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+24 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+32 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+40 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+48 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+56 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+64 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+72 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+80 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+88 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+96 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+104 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 112 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_112(Addr new_SP)
{
   PROF_EVENT(125, "die_mem_stack_112");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-112);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-104);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-96 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-88 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-80 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-72 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-64 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-56 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-48 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-40 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-32 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-24 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP- 8 );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-112, 112 );
   }
}

/*--------------- adjustment by 128 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_128_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(116, "new_mem_stack_128");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP   , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8 , otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+16, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+24, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+32, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+40, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+48, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+56, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+64, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+72, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+80, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+88, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+96, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+104, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+112, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+120, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 128, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_128(Addr new_SP)
{
   PROF_EVENT(116, "new_mem_stack_128");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+16 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+24 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+32 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+40 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+48 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+56 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+64 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+72 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+80 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+88 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+96 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+104 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+112 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+120 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 128 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_128(Addr new_SP)
{
   PROF_EVENT(126, "die_mem_stack_128");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-128);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-120);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-112);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-104);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-96 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-88 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-80 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-72 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-64 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-56 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-48 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-40 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-32 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-24 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP- 8 );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-128, 128 );
   }
}

/*--------------- adjustment by 144 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_144_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(117, "new_mem_stack_144");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP,     otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8,   otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+16,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+24,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+32,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+40,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+48,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+56,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+64,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+72,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+80,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+88,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+96,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+104, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+112, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+120, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+128, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+136, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 144, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_144(Addr new_SP)
{
   PROF_EVENT(117, "new_mem_stack_144");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+16 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+24 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+32 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+40 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+48 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+56 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+64 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+72 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+80 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+88 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+96 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+104 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+112 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+120 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+128 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+136 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 144 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_144(Addr new_SP)
{
   PROF_EVENT(127, "die_mem_stack_144");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-144);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-136);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-128);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-120);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-112);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-104);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-96 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-88 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-80 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-72 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-64 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-56 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-48 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-40 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-32 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-24 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP- 8 );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-144, 144 );
   }
}

/*--------------- adjustment by 160 bytes ---------------*/

MAYBE_USED
static void VG_REGPARM(2) mc_new_mem_stack_160_w_ECU(Addr new_SP, UInt ecu)
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(118, "new_mem_stack_160");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP,     otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+8,   otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+16,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+24,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+32,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+40,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+48,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+56,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+64,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+72,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+80,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+88,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+96,  otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+104, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+112, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+120, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+128, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+136, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+144, otag );
      make_aligned_word64_undefined_w_otag ( -VG_STACK_REDZONE_SZB + new_SP+152, otag );
   } else {
      MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + new_SP, 160, otag );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_new_mem_stack_160(Addr new_SP)
{
   PROF_EVENT(118, "new_mem_stack_160");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+8 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+16 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+24 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+32 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+40 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+48 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+56 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+64 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+72 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+80 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+88 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+96 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+104 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+112 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+120 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+128 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+136 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+144 );
      make_aligned_word64_undefined ( -VG_STACK_REDZONE_SZB + new_SP+152 );
   } else {
      make_mem_undefined ( -VG_STACK_REDZONE_SZB + new_SP, 160 );
   }
}

MAYBE_USED
static void VG_REGPARM(1) mc_die_mem_stack_160(Addr new_SP)
{
   PROF_EVENT(128, "die_mem_stack_160");
   if (VG_IS_8_ALIGNED( -VG_STACK_REDZONE_SZB + new_SP )) {
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-160);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-152);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-144);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-136);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-128);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-120);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-112);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-104);
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-96 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-88 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-80 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-72 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-64 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-56 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-48 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-40 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-32 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-24 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP-16 );
      make_aligned_word64_noaccess ( -VG_STACK_REDZONE_SZB + new_SP- 8 );
   } else {
      MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + new_SP-160, 160 );
   }
}

/*--------------- adjustment by N bytes ---------------*/

static void mc_new_mem_stack_w_ECU ( Addr a, SizeT len, UInt ecu )
{
   UInt otag = ecu | MC_OKIND_STACK;
   PROF_EVENT(115, "new_mem_stack_w_otag");
   MC_(make_mem_undefined_w_otag) ( -VG_STACK_REDZONE_SZB + a, len, otag );
}

static void mc_new_mem_stack ( Addr a, SizeT len )
{
   PROF_EVENT(115, "new_mem_stack");
   make_mem_undefined ( -VG_STACK_REDZONE_SZB + a, len );
}

static void mc_die_mem_stack ( Addr a, SizeT len )
{
   PROF_EVENT(125, "die_mem_stack");
   MC_(make_mem_noaccess) ( -VG_STACK_REDZONE_SZB + a, len );
}


/* The AMD64 ABI says:

   "The 128-byte area beyond the location pointed to by %rsp is considered
    to be reserved and shall not be modified by signal or interrupt
    handlers.  Therefore, functions may use this area for temporary data
    that is not needed across function calls.  In particular, leaf functions
    may use this area for their entire stack frame, rather than adjusting
    the stack pointer in the prologue and epilogue.  This area is known as
    red zone [sic]."

   So after any call or return we need to mark this redzone as containing
   undefined values.

   Consider this:  we're in function f.  f calls g.  g moves rsp down
   modestly (say 16 bytes) and writes stuff all over the red zone, making it
   defined.  g returns.  f is buggy and reads from parts of the red zone
   that it didn't write on.  But because g filled that area in, f is going
   to be picking up defined V bits and so any errors from reading bits of
   the red zone it didn't write, will be missed.  The only solution I could
   think of was to make the red zone undefined when g returns to f.

   This is in accordance with the ABI, which makes it clear the redzone
   is volatile across function calls.

   The problem occurs the other way round too: f could fill the RZ up
   with defined values and g could mistakenly read them.  So the RZ
   also needs to be nuked on function calls.
*/


/* Here's a simple cache to hold nia -> ECU mappings.  It could be
   improved so as to have a lower miss rate. */

static UWord stats__nia_cache_queries = 0;
static UWord stats__nia_cache_misses  = 0;

typedef
   struct { UWord nia0; UWord ecu0;   /* nia0 maps to ecu0 */
            UWord nia1; UWord ecu1; } /* nia1 maps to ecu1 */
   WCacheEnt;

#define N_NIA_TO_ECU_CACHE 511

static WCacheEnt nia_to_ecu_cache[N_NIA_TO_ECU_CACHE];

static void init_nia_to_ecu_cache ( void )
{
   UWord       i;
   Addr        zero_addr = 0;
   ExeContext* zero_ec;
   UInt        zero_ecu;
   /* Fill all the slots with an entry for address zero, and the
      relevant otags accordingly.  Hence the cache is initially filled
      with valid data. */
   zero_ec = VG_(make_depth_1_ExeContext_from_Addr)(zero_addr);
   tl_assert(zero_ec);
   zero_ecu = VG_(get_ECU_from_ExeContext)(zero_ec);
   tl_assert(VG_(is_plausible_ECU)(zero_ecu));
   for (i = 0; i < N_NIA_TO_ECU_CACHE; i++) {
      nia_to_ecu_cache[i].nia0 = zero_addr;
      nia_to_ecu_cache[i].ecu0 = zero_ecu;
      nia_to_ecu_cache[i].nia1 = zero_addr;
      nia_to_ecu_cache[i].ecu1 = zero_ecu;
   }
}

static inline UInt convert_nia_to_ecu ( Addr nia )
{
   UWord i;
   UInt        ecu;
   ExeContext* ec;

   tl_assert( sizeof(nia_to_ecu_cache[0].nia1) == sizeof(nia) );

   stats__nia_cache_queries++;
   i = nia % N_NIA_TO_ECU_CACHE;
   tl_assert(i >= 0 && i < N_NIA_TO_ECU_CACHE);

   if (LIKELY( nia_to_ecu_cache[i].nia0 == nia ))
      return nia_to_ecu_cache[i].ecu0;

   if (LIKELY( nia_to_ecu_cache[i].nia1 == nia )) {
#     define SWAP(_w1,_w2) { UWord _t = _w1; _w1 = _w2; _w2 = _t; }
      SWAP( nia_to_ecu_cache[i].nia0, nia_to_ecu_cache[i].nia1 );
      SWAP( nia_to_ecu_cache[i].ecu0, nia_to_ecu_cache[i].ecu1 );
#     undef SWAP
      return nia_to_ecu_cache[i].ecu0;
   }

   stats__nia_cache_misses++;
   ec = VG_(make_depth_1_ExeContext_from_Addr)(nia);
   tl_assert(ec);
   ecu = VG_(get_ECU_from_ExeContext)(ec);
   tl_assert(VG_(is_plausible_ECU)(ecu));

   nia_to_ecu_cache[i].nia1 = nia_to_ecu_cache[i].nia0;
   nia_to_ecu_cache[i].ecu1 = nia_to_ecu_cache[i].ecu0;

   nia_to_ecu_cache[i].nia0 = nia;
   nia_to_ecu_cache[i].ecu0 = (UWord)ecu;
   return ecu;
}


/* Note that this serves both the origin-tracking and
   no-origin-tracking modes.  We assume that calls to it are
   sufficiently infrequent that it isn't worth specialising for the
   with/without origin-tracking cases. */
void MC_(helperc_MAKE_STACK_UNINIT) ( Addr base, UWord len, Addr nia )
{
   UInt otag;
   tl_assert(sizeof(UWord) == sizeof(SizeT));
   if (0)
      VG_(printf)("helperc_MAKE_STACK_UNINIT (%#lx,%lu,nia=%#lx)\n",
                  base, len, nia );

   if (UNLIKELY( MC_(clo_mc_level) == 3 )) {
      UInt ecu = convert_nia_to_ecu ( nia );
      tl_assert(VG_(is_plausible_ECU)(ecu));
      otag = ecu | MC_OKIND_STACK;
   } else {
      tl_assert(nia == 0);
      otag = 0;
   }

#  if 0
   /* Really slow version */
   MC_(make_mem_undefined)(base, len, otag);
#  endif

#  if 0
   /* Slow(ish) version, which is fairly easily seen to be correct.
   */
   if (LIKELY( VG_IS_8_ALIGNED(base) && len==128 )) {
      make_aligned_word64_undefined(base +   0, otag);
      make_aligned_word64_undefined(base +   8, otag);
      make_aligned_word64_undefined(base +  16, otag);
      make_aligned_word64_undefined(base +  24, otag);

      make_aligned_word64_undefined(base +  32, otag);
      make_aligned_word64_undefined(base +  40, otag);
      make_aligned_word64_undefined(base +  48, otag);
      make_aligned_word64_undefined(base +  56, otag);

      make_aligned_word64_undefined(base +  64, otag);
      make_aligned_word64_undefined(base +  72, otag);
      make_aligned_word64_undefined(base +  80, otag);
      make_aligned_word64_undefined(base +  88, otag);

      make_aligned_word64_undefined(base +  96, otag);
      make_aligned_word64_undefined(base + 104, otag);
      make_aligned_word64_undefined(base + 112, otag);
      make_aligned_word64_undefined(base + 120, otag);
   } else {
      MC_(make_mem_undefined)(base, len, otag);
   }
#  endif 

   /* Idea is: go fast when
         * 8-aligned and length is 128
         * the sm is available in the main primary map
         * the address range falls entirely with a single secondary map
      If all those conditions hold, just update the V+A bits by writing
      directly into the vabits array.  (If the sm was distinguished, this
      will make a copy and then write to it.)
   */

   if (LIKELY( len == 128 && VG_IS_8_ALIGNED(base) )) {
      /* Now we know the address range is suitably sized and aligned. */
      UWord a_lo = (UWord)(base);
      UWord a_hi = (UWord)(base + 128 - 1);
      tl_assert(a_lo < a_hi);             // paranoia: detect overflow
      if (a_hi <= MAX_PRIMARY_ADDRESS) {
         // Now we know the entire range is within the main primary map.
         SecMap* sm    = get_secmap_for_writing_low(a_lo);
         SecMap* sm_hi = get_secmap_for_writing_low(a_hi);
         /* Now we know that the entire address range falls within a
            single secondary map, and that that secondary 'lives' in
            the main primary map. */
         if (LIKELY(sm == sm_hi)) {
            // Finally, we know that the range is entirely within one secmap.
            UWord   v_off = SM_OFF(a_lo);
            UShort* p     = (UShort*)(&sm->vabits8[v_off]);
            p[ 0] = VA_BITS16_UNDEFINED;
            p[ 1] = VA_BITS16_UNDEFINED;
            p[ 2] = VA_BITS16_UNDEFINED;
            p[ 3] = VA_BITS16_UNDEFINED;
            p[ 4] = VA_BITS16_UNDEFINED;
            p[ 5] = VA_BITS16_UNDEFINED;
            p[ 6] = VA_BITS16_UNDEFINED;
            p[ 7] = VA_BITS16_UNDEFINED;
            p[ 8] = VA_BITS16_UNDEFINED;
            p[ 9] = VA_BITS16_UNDEFINED;
            p[10] = VA_BITS16_UNDEFINED;
            p[11] = VA_BITS16_UNDEFINED;
            p[12] = VA_BITS16_UNDEFINED;
            p[13] = VA_BITS16_UNDEFINED;
            p[14] = VA_BITS16_UNDEFINED;
            p[15] = VA_BITS16_UNDEFINED;
            if (UNLIKELY( MC_(clo_mc_level) == 3 )) {
               set_aligned_word64_Origin_to_undef( base + 8 * 0, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 1, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 2, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 3, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 4, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 5, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 6, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 7, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 8, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 9, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 10, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 11, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 12, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 13, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 14, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 15, otag );
            }
            return;
         }
      }
   }

   /* 288 bytes (36 ULongs) is the magic value for ELF ppc64. */
   if (LIKELY( len == 288 && VG_IS_8_ALIGNED(base) )) {
      /* Now we know the address range is suitably sized and aligned. */
      UWord a_lo = (UWord)(base);
      UWord a_hi = (UWord)(base + 288 - 1);
      tl_assert(a_lo < a_hi);             // paranoia: detect overflow
      if (a_hi <= MAX_PRIMARY_ADDRESS) {
         // Now we know the entire range is within the main primary map.
         SecMap* sm    = get_secmap_for_writing_low(a_lo);
         SecMap* sm_hi = get_secmap_for_writing_low(a_hi);
         /* Now we know that the entire address range falls within a
            single secondary map, and that that secondary 'lives' in
            the main primary map. */
         if (LIKELY(sm == sm_hi)) {
            // Finally, we know that the range is entirely within one secmap.
            UWord   v_off = SM_OFF(a_lo);
            UShort* p     = (UShort*)(&sm->vabits8[v_off]);
            p[ 0] = VA_BITS16_UNDEFINED;
            p[ 1] = VA_BITS16_UNDEFINED;
            p[ 2] = VA_BITS16_UNDEFINED;
            p[ 3] = VA_BITS16_UNDEFINED;
            p[ 4] = VA_BITS16_UNDEFINED;
            p[ 5] = VA_BITS16_UNDEFINED;
            p[ 6] = VA_BITS16_UNDEFINED;
            p[ 7] = VA_BITS16_UNDEFINED;
            p[ 8] = VA_BITS16_UNDEFINED;
            p[ 9] = VA_BITS16_UNDEFINED;
            p[10] = VA_BITS16_UNDEFINED;
            p[11] = VA_BITS16_UNDEFINED;
            p[12] = VA_BITS16_UNDEFINED;
            p[13] = VA_BITS16_UNDEFINED;
            p[14] = VA_BITS16_UNDEFINED;
            p[15] = VA_BITS16_UNDEFINED;
            p[16] = VA_BITS16_UNDEFINED;
            p[17] = VA_BITS16_UNDEFINED;
            p[18] = VA_BITS16_UNDEFINED;
            p[19] = VA_BITS16_UNDEFINED;
            p[20] = VA_BITS16_UNDEFINED;
            p[21] = VA_BITS16_UNDEFINED;
            p[22] = VA_BITS16_UNDEFINED;
            p[23] = VA_BITS16_UNDEFINED;
            p[24] = VA_BITS16_UNDEFINED;
            p[25] = VA_BITS16_UNDEFINED;
            p[26] = VA_BITS16_UNDEFINED;
            p[27] = VA_BITS16_UNDEFINED;
            p[28] = VA_BITS16_UNDEFINED;
            p[29] = VA_BITS16_UNDEFINED;
            p[30] = VA_BITS16_UNDEFINED;
            p[31] = VA_BITS16_UNDEFINED;
            p[32] = VA_BITS16_UNDEFINED;
            p[33] = VA_BITS16_UNDEFINED;
            p[34] = VA_BITS16_UNDEFINED;
            p[35] = VA_BITS16_UNDEFINED;
            if (UNLIKELY( MC_(clo_mc_level) == 3 )) {
               set_aligned_word64_Origin_to_undef( base + 8 * 0, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 1, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 2, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 3, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 4, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 5, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 6, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 7, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 8, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 9, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 10, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 11, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 12, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 13, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 14, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 15, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 16, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 17, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 18, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 19, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 20, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 21, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 22, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 23, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 24, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 25, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 26, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 27, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 28, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 29, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 30, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 31, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 32, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 33, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 34, otag );
               set_aligned_word64_Origin_to_undef( base + 8 * 35, otag );
            }
            return;
         }
      }
   }

   /* else fall into slow case */
   MC_(make_mem_undefined_w_otag)(base, len, otag);
}


/*------------------------------------------------------------*/
/*--- Checking memory                                      ---*/
/*------------------------------------------------------------*/

typedef 
   enum {
      MC_Ok = 5, 
      MC_AddrErr = 6, 
      MC_ValueErr = 7
   } 
   MC_ReadResult;


/* Check permissions for address range.  If inadequate permissions
   exist, *bad_addr is set to the offending address, so the caller can
   know what it is. */

/* Returns True if [a .. a+len) is not addressible.  Otherwise,
   returns False, and if bad_addr is non-NULL, sets *bad_addr to
   indicate the lowest failing address.  Functions below are
   similar. */
Bool MC_(check_mem_is_noaccess) ( Addr a, SizeT len, Addr* bad_addr )
{
   SizeT i;
   UWord vabits2;

   PROF_EVENT(60, "check_mem_is_noaccess");
   for (i = 0; i < len; i++) {
      PROF_EVENT(61, "check_mem_is_noaccess(loop)");
      vabits2 = get_vabits2(a);
      if (VA_BITS2_NOACCESS != vabits2) {
         if (bad_addr != NULL) *bad_addr = a;
         return False;
      }
      a++;
   }
   return True;
}

static Bool is_mem_addressable ( Addr a, SizeT len, 
                                 /*OUT*/Addr* bad_addr )
{
   SizeT i;
   UWord vabits2;

   PROF_EVENT(62, "is_mem_addressable");
   for (i = 0; i < len; i++) {
      PROF_EVENT(63, "is_mem_addressable(loop)");
      vabits2 = get_vabits2(a);
      if (VA_BITS2_NOACCESS == vabits2) {
         if (bad_addr != NULL) *bad_addr = a;
         return False;
      }
      a++;
   }
   return True;
}

static MC_ReadResult is_mem_defined ( Addr a, SizeT len,
                                      /*OUT*/Addr* bad_addr,
                                      /*OUT*/UInt* otag )
{
   SizeT i;
   UWord vabits2;

   PROF_EVENT(64, "is_mem_defined");
   DEBUG("is_mem_defined\n");

   if (otag)     *otag = 0;
   if (bad_addr) *bad_addr = 0;
   for (i = 0; i < len; i++) {
      PROF_EVENT(65, "is_mem_defined(loop)");
      vabits2 = get_vabits2(a);
      if (VA_BITS2_DEFINED != vabits2) {
         // Error!  Nb: Report addressability errors in preference to
         // definedness errors.  And don't report definedeness errors unless
         // --undef-value-errors=yes.
         if (bad_addr) {
            *bad_addr = a;
         }
         if (VA_BITS2_NOACCESS == vabits2) {
            return MC_AddrErr;
         }
         if (MC_(clo_mc_level) >= 2) {
            if (otag && MC_(clo_mc_level) == 3) {
               *otag = MC_(helperc_b_load1)( a );
            }
            return MC_ValueErr;
         }
      }
      a++;
   }
   return MC_Ok;
}


/* Check a zero-terminated ascii string.  Tricky -- don't want to
   examine the actual bytes, to find the end, until we're sure it is
   safe to do so. */

static Bool mc_is_defined_asciiz ( Addr a, Addr* bad_addr, UInt* otag )
{
   UWord vabits2;

   PROF_EVENT(66, "mc_is_defined_asciiz");
   DEBUG("mc_is_defined_asciiz\n");

   if (otag)     *otag = 0;
   if (bad_addr) *bad_addr = 0;
   while (True) {
      PROF_EVENT(67, "mc_is_defined_asciiz(loop)");
      vabits2 = get_vabits2(a);
      if (VA_BITS2_DEFINED != vabits2) {
         // Error!  Nb: Report addressability errors in preference to
         // definedness errors.  And don't report definedeness errors unless
         // --undef-value-errors=yes.
         if (bad_addr) {
            *bad_addr = a;
         }
         if (VA_BITS2_NOACCESS == vabits2) {
            return MC_AddrErr;
         }
         if (MC_(clo_mc_level) >= 2) {
            if (otag && MC_(clo_mc_level) == 3) {
               *otag = MC_(helperc_b_load1)( a );
            }
            return MC_ValueErr;
         }
      }
      /* Ok, a is safe to read. */
      if (* ((UChar*)a) == 0) {
         return MC_Ok;
      }
      a++;
   }
}


/*------------------------------------------------------------*/
/*--- Memory event handlers                                ---*/
/*------------------------------------------------------------*/

static
void check_mem_is_addressable ( CorePart part, ThreadId tid, Char* s,
                                Addr base, SizeT size )
{
   Addr bad_addr;
   Bool ok = is_mem_addressable ( base, size, &bad_addr );

   if (!ok) {
      switch (part) {
      case Vg_CoreSysCall:
         MC_(record_memparam_error) ( tid, bad_addr, 
                                      /*isAddrErr*/True, s, 0/*otag*/ );
         break;

      case Vg_CoreSignal:
         MC_(record_core_mem_error)( tid, s );
         break;

      default:
         VG_(tool_panic)("check_mem_is_addressable: unexpected CorePart");
      }
   }
}

static
void check_mem_is_defined ( CorePart part, ThreadId tid, Char* s,
                            Addr base, SizeT size )
{     
   UInt otag = 0;
   Addr bad_addr;
   MC_ReadResult res = is_mem_defined ( base, size, &bad_addr, &otag );

   if (MC_Ok != res) {
      Bool isAddrErr = ( MC_AddrErr == res ? True : False );

      switch (part) {
      case Vg_CoreSysCall:
         MC_(record_memparam_error) ( tid, bad_addr, isAddrErr, s,
                                      isAddrErr ? 0 : otag );
         break;
      
      case Vg_CoreSysCallArgInMem:
         MC_(record_regparam_error) ( tid, s, otag );
         break;

      /* If we're being asked to jump to a silly address, record an error 
         message before potentially crashing the entire system. */
      case Vg_CoreTranslate:
         MC_(record_jump_error)( tid, bad_addr );
         break;

      default:
         VG_(tool_panic)("check_mem_is_defined: unexpected CorePart");
      }
   }
}

static
void check_mem_is_defined_asciiz ( CorePart part, ThreadId tid,
                                   Char* s, Addr str )
{
   MC_ReadResult res;
   Addr bad_addr = 0;   // shut GCC up
   UInt otag = 0;

   tl_assert(part == Vg_CoreSysCall);
   res = mc_is_defined_asciiz ( (Addr)str, &bad_addr, &otag );
   if (MC_Ok != res) {
      Bool isAddrErr = ( MC_AddrErr == res ? True : False );
      MC_(record_memparam_error) ( tid, bad_addr, isAddrErr, s,
                                   isAddrErr ? 0 : otag );
   }
}

static
void mc_new_mem_mmap ( Addr a, SizeT len, Bool rr, Bool ww, Bool xx,
                       ULong di_handle )
{
   if (rr || ww || xx)
      MC_(make_mem_defined)(a, len);
   else
      MC_(make_mem_noaccess)(a, len);
}

static
void mc_new_mem_startup( Addr a, SizeT len,
                         Bool rr, Bool ww, Bool xx, ULong di_handle )
{
   // Because code is defined, initialised variables get put in the data
   // segment and are defined, and uninitialised variables get put in the
   // bss segment and are auto-zeroed (and so defined).  
   //
   // It's possible that there will be padding between global variables.
   // This will also be auto-zeroed, and marked as defined by Memcheck.  If
   // a program uses it, Memcheck will not complain.  This is arguably a
   // false negative, but it's a grey area -- the behaviour is defined (the
   // padding is zeroed) but it's probably not what the user intended.  And
   // we can't avoid it.
   //
   // Note: we generally ignore RWX permissions, because we can't track them
   // without requiring more than one A bit which would slow things down a
   // lot.  But on Darwin the 0th page is mapped but !R and !W and !X.
   // So we mark any such pages as "unaddressable".
   DEBUG("mc_new_mem_startup(%#lx, %llu, rr=%u, ww=%u, xx=%u)\n",
         a, (ULong)len, rr, ww, xx);
   mc_new_mem_mmap(a, len, rr, ww, xx, di_handle);
}

static
void mc_post_mem_write(CorePart part, ThreadId tid, Addr a, SizeT len)
{
   MC_(make_mem_defined)(a, len);
}


/*------------------------------------------------------------*/
/*--- Register event handlers                              ---*/
/*------------------------------------------------------------*/

/* Try and get a nonzero origin for the guest state section of thread
   tid characterised by (offset,size).  Return 0 if nothing to show
   for it. */
static UInt mb_get_origin_for_guest_offset ( ThreadId tid,
                                             Int offset, SizeT size )
{
   Int   sh2off;
   UChar area[6];
   UInt  otag;
   sh2off = MC_(get_otrack_shadow_offset)( offset, size );
   if (sh2off == -1)
      return 0;  /* This piece of guest state is not tracked */
   tl_assert(sh2off >= 0);
   tl_assert(0 == (sh2off % 4));
   area[0] = 0x31;
   area[5] = 0x27;
   VG_(get_shadow_regs_area)( tid, &area[1], 2/*shadowno*/,sh2off,4 );
   tl_assert(area[0] == 0x31);
   tl_assert(area[5] == 0x27);
   otag = *(UInt*)&area[1];
   return otag;
}


/* When some chunk of guest state is written, mark the corresponding
   shadow area as valid.  This is used to initialise arbitrarily large
   chunks of guest state, hence the _SIZE value, which has to be as
   big as the biggest guest state.
*/
static void mc_post_reg_write ( CorePart part, ThreadId tid, 
                                PtrdiffT offset, SizeT size)
{
#  define MAX_REG_WRITE_SIZE 1408
   UChar area[MAX_REG_WRITE_SIZE];
   tl_assert(size <= MAX_REG_WRITE_SIZE);
   VG_(memset)(area, V_BITS8_DEFINED, size);
   VG_(set_shadow_regs_area)( tid, 1/*shadowNo*/,offset,size, area );
#  undef MAX_REG_WRITE_SIZE
}

static 
void mc_post_reg_write_clientcall ( ThreadId tid, 
                                    PtrdiffT offset, SizeT size, Addr f)
{
   mc_post_reg_write(/*dummy*/0, tid, offset, size);
}

/* Look at the definedness of the guest's shadow state for 
   [offset, offset+len).  If any part of that is undefined, record 
   a parameter error.
*/
static void mc_pre_reg_read ( CorePart part, ThreadId tid, Char* s, 
                              PtrdiffT offset, SizeT size)
{
   Int   i;
   Bool  bad;
   UInt  otag;

   UChar area[16];
   tl_assert(size <= 16);

   VG_(get_shadow_regs_area)( tid, area, 1/*shadowNo*/,offset,size );

   bad = False;
   for (i = 0; i < size; i++) {
      if (area[i] != V_BITS8_DEFINED) {
         bad = True;
         break;
      }
   }

   if (!bad)
      return;

   /* We've found some undefinedness.  See if we can also find an
      origin for it. */
   otag = mb_get_origin_for_guest_offset( tid, offset, size );
   MC_(record_regparam_error) ( tid, s, otag );
}


/*------------------------------------------------------------*/
/*--- Functions called directly from generated code:       ---*/
/*--- Load/store handlers.                                 ---*/
/*------------------------------------------------------------*/

/* Types:  LOADV32, LOADV16, LOADV8 are:
               UWord fn ( Addr a )
   so they return 32-bits on 32-bit machines and 64-bits on
   64-bit machines.  Addr has the same size as a host word.

   LOADV64 is always  ULong fn ( Addr a )

   Similarly for STOREV8, STOREV16, STOREV32, the supplied vbits
   are a UWord, and for STOREV64 they are a ULong.
*/

/* If any part of '_a' indicated by the mask is 1, either '_a' is not
   naturally '_sz/8'-aligned, or it exceeds the range covered by the
   primary map.  This is all very tricky (and important!), so let's
   work through the maths by hand (below), *and* assert for these
   values at startup. */
#define MASK(_szInBytes) \
   ( ~((0x10000UL-(_szInBytes)) | ((N_PRIMARY_MAP-1) << 16)) )

/* MASK only exists so as to define this macro. */
#define UNALIGNED_OR_HIGH(_a,_szInBits) \
   ((_a) & MASK((_szInBits>>3)))

/* On a 32-bit machine:

   N_PRIMARY_BITS          == 16, so
   N_PRIMARY_MAP           == 0x10000, so
   N_PRIMARY_MAP-1         == 0xFFFF, so
   (N_PRIMARY_MAP-1) << 16 == 0xFFFF0000, and so

   MASK(1) = ~ ( (0x10000 - 1) | 0xFFFF0000 )
           = ~ ( 0xFFFF | 0xFFFF0000 )
           = ~ 0xFFFF'FFFF
           = 0

   MASK(2) = ~ ( (0x10000 - 2) | 0xFFFF0000 )
           = ~ ( 0xFFFE | 0xFFFF0000 )
           = ~ 0xFFFF'FFFE
           = 1

   MASK(4) = ~ ( (0x10000 - 4) | 0xFFFF0000 )
           = ~ ( 0xFFFC | 0xFFFF0000 )
           = ~ 0xFFFF'FFFC
           = 3

   MASK(8) = ~ ( (0x10000 - 8) | 0xFFFF0000 )
           = ~ ( 0xFFF8 | 0xFFFF0000 )
           = ~ 0xFFFF'FFF8
           = 7

   Hence in the 32-bit case, "a & MASK(1/2/4/8)" is a nonzero value
   precisely when a is not 1/2/4/8-bytes aligned.  And obviously, for
   the 1-byte alignment case, it is always a zero value, since MASK(1)
   is zero.  All as expected.

   On a 64-bit machine, it's more complex, since we're testing
   simultaneously for misalignment and for the address being at or
   above 32G:

   N_PRIMARY_BITS          == 19, so
   N_PRIMARY_MAP           == 0x80000, so
   N_PRIMARY_MAP-1         == 0x7FFFF, so
   (N_PRIMARY_MAP-1) << 16 == 0x7FFFF'0000, and so

   MASK(1) = ~ ( (0x10000 - 1) | 0x7FFFF'0000 )
           = ~ ( 0xFFFF | 0x7FFFF'0000 )
           = ~ 0x7FFFF'FFFF
           = 0xFFFF'FFF8'0000'0000

   MASK(2) = ~ ( (0x10000 - 2) | 0x7FFFF'0000 )
           = ~ ( 0xFFFE | 0x7FFFF'0000 )
           = ~ 0x7FFFF'FFFE
           = 0xFFFF'FFF8'0000'0001

   MASK(4) = ~ ( (0x10000 - 4) | 0x7FFFF'0000 )
           = ~ ( 0xFFFC | 0x7FFFF'0000 )
           = ~ 0x7FFFF'FFFC
           = 0xFFFF'FFF8'0000'0003

   MASK(8) = ~ ( (0x10000 - 8) | 0x7FFFF'0000 )
           = ~ ( 0xFFF8 | 0x7FFFF'0000 )
           = ~ 0x7FFFF'FFF8
           = 0xFFFF'FFF8'0000'0007
*/


/* ------------------------ Size = 8 ------------------------ */

static INLINE
ULong mc_LOADV64 ( Addr a, Bool isBigEndian )
{
   PROF_EVENT(200, "mc_LOADV64");

#ifndef PERF_FAST_LOADV
   return mc_LOADVn_slow( a, 64, isBigEndian );
#else
   {
      UWord   sm_off16, vabits16;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,64) )) {
         PROF_EVENT(201, "mc_LOADV64-slow1");
         return (ULong)mc_LOADVn_slow( a, 64, isBigEndian );
      }

      sm       = get_secmap_for_reading_low(a);
      sm_off16 = SM_OFF_16(a);
      vabits16 = ((UShort*)(sm->vabits8))[sm_off16];

      // Handle common case quickly: a is suitably aligned, is mapped, and
      // addressible.
      // Convert V bits from compact memory form to expanded register form.
      if (LIKELY(vabits16 == VA_BITS16_DEFINED)) {
         return V_BITS64_DEFINED;
      } else if (LIKELY(vabits16 == VA_BITS16_UNDEFINED)) {
         return V_BITS64_UNDEFINED;
      } else {
         /* Slow case: the 8 bytes are not all-defined or all-undefined. */
         PROF_EVENT(202, "mc_LOADV64-slow2");
         return mc_LOADVn_slow( a, 64, isBigEndian );
      }
   }
#endif
}

VG_REGPARM(1) ULong MC_(helperc_LOADV64be) ( Addr a )
{
   return mc_LOADV64(a, True);
}
VG_REGPARM(1) ULong MC_(helperc_LOADV64le) ( Addr a )
{
   return mc_LOADV64(a, False);
}


static INLINE
void mc_STOREV64 ( Addr a, ULong vbits64, Bool isBigEndian )
{
   PROF_EVENT(210, "mc_STOREV64");

#ifndef PERF_FAST_STOREV
   // XXX: this slow case seems to be marginally faster than the fast case!
   // Investigate further.
   mc_STOREVn_slow( a, 64, vbits64, isBigEndian );
#else
   {
      UWord   sm_off16, vabits16;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,64) )) {
         PROF_EVENT(211, "mc_STOREV64-slow1");
         mc_STOREVn_slow( a, 64, vbits64, isBigEndian );
         return;
      }

      sm       = get_secmap_for_reading_low(a);
      sm_off16 = SM_OFF_16(a);
      vabits16 = ((UShort*)(sm->vabits8))[sm_off16];

      if (LIKELY( !is_distinguished_sm(sm) && 
                          (VA_BITS16_DEFINED   == vabits16 ||
                           VA_BITS16_UNDEFINED == vabits16) ))
      {
         /* Handle common case quickly: a is suitably aligned, */
         /* is mapped, and is addressible. */
         // Convert full V-bits in register to compact 2-bit form.
         if (V_BITS64_DEFINED == vbits64) {
            ((UShort*)(sm->vabits8))[sm_off16] = (UShort)VA_BITS16_DEFINED;
         } else if (V_BITS64_UNDEFINED == vbits64) {
            ((UShort*)(sm->vabits8))[sm_off16] = (UShort)VA_BITS16_UNDEFINED;
         } else {
            /* Slow but general case -- writing partially defined bytes. */
            PROF_EVENT(212, "mc_STOREV64-slow2");
            mc_STOREVn_slow( a, 64, vbits64, isBigEndian );
         }
      } else {
         /* Slow but general case. */
         PROF_EVENT(213, "mc_STOREV64-slow3");
         mc_STOREVn_slow( a, 64, vbits64, isBigEndian );
      }
   }
#endif
}

VG_REGPARM(1) void MC_(helperc_STOREV64be) ( Addr a, ULong vbits64 )
{
   mc_STOREV64(a, vbits64, True);
}
VG_REGPARM(1) void MC_(helperc_STOREV64le) ( Addr a, ULong vbits64 )
{
   mc_STOREV64(a, vbits64, False);
}


/* ------------------------ Size = 4 ------------------------ */

static INLINE
UWord mc_LOADV32 ( Addr a, Bool isBigEndian )
{
   PROF_EVENT(220, "mc_LOADV32");

#ifndef PERF_FAST_LOADV
   return (UWord)mc_LOADVn_slow( a, 32, isBigEndian );
#else
   {
      UWord   sm_off, vabits8;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,32) )) {
         PROF_EVENT(221, "mc_LOADV32-slow1");
         return (UWord)mc_LOADVn_slow( a, 32, isBigEndian );
      }

      sm      = get_secmap_for_reading_low(a);
      sm_off  = SM_OFF(a);
      vabits8 = sm->vabits8[sm_off];

      // Handle common case quickly: a is suitably aligned, is mapped, and the
      // entire word32 it lives in is addressible.
      // Convert V bits from compact memory form to expanded register form.
      // For 64-bit platforms, set the high 32 bits of retval to 1 (undefined).
      // Almost certainly not necessary, but be paranoid.
      if (LIKELY(vabits8 == VA_BITS8_DEFINED)) {
         return ((UWord)0xFFFFFFFF00000000ULL | (UWord)V_BITS32_DEFINED);
      } else if (LIKELY(vabits8 == VA_BITS8_UNDEFINED)) {
         return ((UWord)0xFFFFFFFF00000000ULL | (UWord)V_BITS32_UNDEFINED);
      } else {
         /* Slow case: the 4 bytes are not all-defined or all-undefined. */
         PROF_EVENT(222, "mc_LOADV32-slow2");
         return (UWord)mc_LOADVn_slow( a, 32, isBigEndian );
      }
   }
#endif
}

VG_REGPARM(1) UWord MC_(helperc_LOADV32be) ( Addr a )
{
   return mc_LOADV32(a, True);
}
VG_REGPARM(1) UWord MC_(helperc_LOADV32le) ( Addr a )
{
   return mc_LOADV32(a, False);
}


static INLINE
void mc_STOREV32 ( Addr a, UWord vbits32, Bool isBigEndian )
{
   PROF_EVENT(230, "mc_STOREV32");

#ifndef PERF_FAST_STOREV
   mc_STOREVn_slow( a, 32, (ULong)vbits32, isBigEndian );
#else
   {
      UWord   sm_off, vabits8;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,32) )) {
         PROF_EVENT(231, "mc_STOREV32-slow1");
         mc_STOREVn_slow( a, 32, (ULong)vbits32, isBigEndian );
         return;
      }

      sm      = get_secmap_for_reading_low(a);
      sm_off  = SM_OFF(a);
      vabits8 = sm->vabits8[sm_off];

      // Cleverness:  sometimes we don't have to write the shadow memory at
      // all, if we can tell that what we want to write is the same as what is
      // already there.  The 64/16/8 bit cases also have cleverness at this
      // point, but it works a little differently to the code below.
      if (V_BITS32_DEFINED == vbits32) {
         if (vabits8 == (UInt)VA_BITS8_DEFINED) {
            return;
         } else if (!is_distinguished_sm(sm) && VA_BITS8_UNDEFINED == vabits8) {
            sm->vabits8[sm_off] = (UInt)VA_BITS8_DEFINED;
         } else {
            // not defined/undefined, or distinguished and changing state
            PROF_EVENT(232, "mc_STOREV32-slow2");
            mc_STOREVn_slow( a, 32, (ULong)vbits32, isBigEndian );
         }
      } else if (V_BITS32_UNDEFINED == vbits32) {
         if (vabits8 == (UInt)VA_BITS8_UNDEFINED) {
            return;
         } else if (!is_distinguished_sm(sm) && VA_BITS8_DEFINED == vabits8) {
            sm->vabits8[sm_off] = (UInt)VA_BITS8_UNDEFINED;
         } else {
            // not defined/undefined, or distinguished and changing state
            PROF_EVENT(233, "mc_STOREV32-slow3");
            mc_STOREVn_slow( a, 32, (ULong)vbits32, isBigEndian );
         }
      } else {
         // Partially defined word
         PROF_EVENT(234, "mc_STOREV32-slow4");
         mc_STOREVn_slow( a, 32, (ULong)vbits32, isBigEndian );
      }
   }
#endif
}

VG_REGPARM(2) void MC_(helperc_STOREV32be) ( Addr a, UWord vbits32 )
{
   mc_STOREV32(a, vbits32, True);
}
VG_REGPARM(2) void MC_(helperc_STOREV32le) ( Addr a, UWord vbits32 )
{
   mc_STOREV32(a, vbits32, False);
}


/* ------------------------ Size = 2 ------------------------ */

static INLINE
UWord mc_LOADV16 ( Addr a, Bool isBigEndian )
{
   PROF_EVENT(240, "mc_LOADV16");

#ifndef PERF_FAST_LOADV
   return (UWord)mc_LOADVn_slow( a, 16, isBigEndian );
#else
   {
      UWord   sm_off, vabits8;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,16) )) {
         PROF_EVENT(241, "mc_LOADV16-slow1");
         return (UWord)mc_LOADVn_slow( a, 16, isBigEndian );
      }

      sm      = get_secmap_for_reading_low(a);
      sm_off  = SM_OFF(a);
      vabits8 = sm->vabits8[sm_off];
      // Handle common case quickly: a is suitably aligned, is mapped, and is
      // addressible.
      // Convert V bits from compact memory form to expanded register form
      if      (vabits8 == VA_BITS8_DEFINED  ) { return V_BITS16_DEFINED;   }
      else if (vabits8 == VA_BITS8_UNDEFINED) { return V_BITS16_UNDEFINED; }
      else {
         // The 4 (yes, 4) bytes are not all-defined or all-undefined, check
         // the two sub-bytes.
         UChar vabits4 = extract_vabits4_from_vabits8(a, vabits8);
         if      (vabits4 == VA_BITS4_DEFINED  ) { return V_BITS16_DEFINED;   }
         else if (vabits4 == VA_BITS4_UNDEFINED) { return V_BITS16_UNDEFINED; }
         else {
            /* Slow case: the two bytes are not all-defined or all-undefined. */
            PROF_EVENT(242, "mc_LOADV16-slow2");
            return (UWord)mc_LOADVn_slow( a, 16, isBigEndian );
         }
      }
   }
#endif
}

VG_REGPARM(1) UWord MC_(helperc_LOADV16be) ( Addr a )
{
   return mc_LOADV16(a, True);
}
VG_REGPARM(1) UWord MC_(helperc_LOADV16le) ( Addr a )
{
   return mc_LOADV16(a, False);
}


static INLINE
void mc_STOREV16 ( Addr a, UWord vbits16, Bool isBigEndian )
{
   PROF_EVENT(250, "mc_STOREV16");

#ifndef PERF_FAST_STOREV
   mc_STOREVn_slow( a, 16, (ULong)vbits16, isBigEndian );
#else
   {
      UWord   sm_off, vabits8;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,16) )) {
         PROF_EVENT(251, "mc_STOREV16-slow1");
         mc_STOREVn_slow( a, 16, (ULong)vbits16, isBigEndian );
         return;
      }

      sm      = get_secmap_for_reading_low(a);
      sm_off  = SM_OFF(a);
      vabits8 = sm->vabits8[sm_off];
      if (LIKELY( !is_distinguished_sm(sm) && 
                          (VA_BITS8_DEFINED   == vabits8 ||
                           VA_BITS8_UNDEFINED == vabits8) ))
      {
         /* Handle common case quickly: a is suitably aligned, */
         /* is mapped, and is addressible. */
         // Convert full V-bits in register to compact 2-bit form.
         if (V_BITS16_DEFINED == vbits16) {
            insert_vabits4_into_vabits8( a, VA_BITS4_DEFINED ,
                                         &(sm->vabits8[sm_off]) );
         } else if (V_BITS16_UNDEFINED == vbits16) {
            insert_vabits4_into_vabits8( a, VA_BITS4_UNDEFINED,
                                         &(sm->vabits8[sm_off]) );
         } else {
            /* Slow but general case -- writing partially defined bytes. */
            PROF_EVENT(252, "mc_STOREV16-slow2");
            mc_STOREVn_slow( a, 16, (ULong)vbits16, isBigEndian );
         }
      } else {
         /* Slow but general case. */
         PROF_EVENT(253, "mc_STOREV16-slow3");
         mc_STOREVn_slow( a, 16, (ULong)vbits16, isBigEndian );
      }
   }
#endif
}

VG_REGPARM(2) void MC_(helperc_STOREV16be) ( Addr a, UWord vbits16 )
{
   mc_STOREV16(a, vbits16, True);
}
VG_REGPARM(2) void MC_(helperc_STOREV16le) ( Addr a, UWord vbits16 )
{
   mc_STOREV16(a, vbits16, False);
}


/* ------------------------ Size = 1 ------------------------ */
/* Note: endianness is irrelevant for size == 1 */

VG_REGPARM(1)
UWord MC_(helperc_LOADV8) ( Addr a )
{
   PROF_EVENT(260, "mc_LOADV8");

#ifndef PERF_FAST_LOADV
   return (UWord)mc_LOADVn_slow( a, 8, False/*irrelevant*/ );
#else
   {
      UWord   sm_off, vabits8;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,8) )) {
         PROF_EVENT(261, "mc_LOADV8-slow1");
         return (UWord)mc_LOADVn_slow( a, 8, False/*irrelevant*/ );
      }

      sm      = get_secmap_for_reading_low(a);
      sm_off  = SM_OFF(a);
      vabits8 = sm->vabits8[sm_off];
      // Convert V bits from compact memory form to expanded register form
      // Handle common case quickly: a is mapped, and the entire
      // word32 it lives in is addressible.
      if      (vabits8 == VA_BITS8_DEFINED  ) { return V_BITS8_DEFINED;   }
      else if (vabits8 == VA_BITS8_UNDEFINED) { return V_BITS8_UNDEFINED; }
      else {
         // The 4 (yes, 4) bytes are not all-defined or all-undefined, check
         // the single byte.
         UChar vabits2 = extract_vabits2_from_vabits8(a, vabits8);
         if      (vabits2 == VA_BITS2_DEFINED  ) { return V_BITS8_DEFINED;   }
         else if (vabits2 == VA_BITS2_UNDEFINED) { return V_BITS8_UNDEFINED; }
         else {
            /* Slow case: the byte is not all-defined or all-undefined. */
            PROF_EVENT(262, "mc_LOADV8-slow2");
            return (UWord)mc_LOADVn_slow( a, 8, False/*irrelevant*/ );
         }
      }
   }
#endif
}


VG_REGPARM(2)
void MC_(helperc_STOREV8) ( Addr a, UWord vbits8 )
{
   PROF_EVENT(270, "mc_STOREV8");

#ifndef PERF_FAST_STOREV
   mc_STOREVn_slow( a, 8, (ULong)vbits8, False/*irrelevant*/ );
#else
   {
      UWord   sm_off, vabits8;
      SecMap* sm;

      if (UNLIKELY( UNALIGNED_OR_HIGH(a,8) )) {
         PROF_EVENT(271, "mc_STOREV8-slow1");
         mc_STOREVn_slow( a, 8, (ULong)vbits8, False/*irrelevant*/ );
         return;
      }

      sm      = get_secmap_for_reading_low(a);
      sm_off  = SM_OFF(a);
      vabits8 = sm->vabits8[sm_off];
      if (LIKELY
            ( !is_distinguished_sm(sm) &&
              ( (VA_BITS8_DEFINED == vabits8 || VA_BITS8_UNDEFINED == vabits8)
             || (VA_BITS2_NOACCESS != extract_vabits2_from_vabits8(a, vabits8))
              )
            )
         )
      {
         /* Handle common case quickly: a is mapped, the entire word32 it
            lives in is addressible. */
         // Convert full V-bits in register to compact 2-bit form.
         if (V_BITS8_DEFINED == vbits8) {
            insert_vabits2_into_vabits8( a, VA_BITS2_DEFINED,
                                          &(sm->vabits8[sm_off]) );
         } else if (V_BITS8_UNDEFINED == vbits8) {
            insert_vabits2_into_vabits8( a, VA_BITS2_UNDEFINED,
                                          &(sm->vabits8[sm_off]) );
         } else {
            /* Slow but general case -- writing partially defined bytes. */
            PROF_EVENT(272, "mc_STOREV8-slow2");
            mc_STOREVn_slow( a, 8, (ULong)vbits8, False/*irrelevant*/ );
         }
      } else {
         /* Slow but general case. */
         PROF_EVENT(273, "mc_STOREV8-slow3");
         mc_STOREVn_slow( a, 8, (ULong)vbits8, False/*irrelevant*/ );
      }
   }
#endif
}


/*------------------------------------------------------------*/
/*--- Functions called directly from generated code:       ---*/
/*--- Value-check failure handlers.                        ---*/
/*------------------------------------------------------------*/

/* Call these ones when an origin is available ... */
VG_REGPARM(1)
void MC_(helperc_value_check0_fail_w_o) ( UWord origin ) {
   MC_(record_cond_error) ( VG_(get_running_tid)(), (UInt)origin );
}

VG_REGPARM(1)
void MC_(helperc_value_check1_fail_w_o) ( UWord origin ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), 1, (UInt)origin );
}

VG_REGPARM(1)
void MC_(helperc_value_check4_fail_w_o) ( UWord origin ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), 4, (UInt)origin );
}

VG_REGPARM(1)
void MC_(helperc_value_check8_fail_w_o) ( UWord origin ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), 8, (UInt)origin );
}

VG_REGPARM(2) 
void MC_(helperc_value_checkN_fail_w_o) ( HWord sz, UWord origin ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), (Int)sz, (UInt)origin );
}

/* ... and these when an origin isn't available. */

VG_REGPARM(0)
void MC_(helperc_value_check0_fail_no_o) ( void ) {
   MC_(record_cond_error) ( VG_(get_running_tid)(), 0/*origin*/ );
}

VG_REGPARM(0)
void MC_(helperc_value_check1_fail_no_o) ( void ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), 1, 0/*origin*/ );
}

VG_REGPARM(0)
void MC_(helperc_value_check4_fail_no_o) ( void ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), 4, 0/*origin*/ );
}

VG_REGPARM(0)
void MC_(helperc_value_check8_fail_no_o) ( void ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), 8, 0/*origin*/ );
}

VG_REGPARM(1) 
void MC_(helperc_value_checkN_fail_no_o) ( HWord sz ) {
   MC_(record_value_error) ( VG_(get_running_tid)(), (Int)sz, 0/*origin*/ );
}


/*------------------------------------------------------------*/
/*--- Metadata get/set functions, for client requests.     ---*/
/*------------------------------------------------------------*/

// Nb: this expands the V+A bits out into register-form V bits, even though
// they're in memory.  This is for backward compatibility, and because it's
// probably what the user wants.

/* Copy Vbits from/to address 'a'. Returns: 1 == OK, 2 == alignment
   error [no longer used], 3 == addressing error. */
/* Nb: We used to issue various definedness/addressability errors from here,
   but we took them out because they ranged from not-very-helpful to
   downright annoying, and they complicated the error data structures. */
static Int mc_get_or_set_vbits_for_client ( 
   Addr a, 
   Addr vbits, 
   SizeT szB, 
   Bool setting /* True <=> set vbits,  False <=> get vbits */ 
)
{
   SizeT i;
   Bool  ok;
   UChar vbits8;

   /* Check that arrays are addressible before doing any getting/setting. */
   for (i = 0; i < szB; i++) {
      if (VA_BITS2_NOACCESS == get_vabits2(a + i) ||
          VA_BITS2_NOACCESS == get_vabits2(vbits + i)) {
         return 3;
      }
   }

   /* Do the copy */
   if (setting) {
      /* setting */
      for (i = 0; i < szB; i++) {
         ok = set_vbits8(a + i, ((UChar*)vbits)[i]);
         tl_assert(ok);
      }
   } else {
      /* getting */
      for (i = 0; i < szB; i++) {
         ok = get_vbits8(a + i, &vbits8);
         tl_assert(ok);
         ((UChar*)vbits)[i] = vbits8;
      }
      // The bytes in vbits[] have now been set, so mark them as such.
      MC_(make_mem_defined)(vbits, szB);
   }

   return 1;
}


/*------------------------------------------------------------*/
/*--- Detecting leaked (unreachable) malloc'd blocks.      ---*/
/*------------------------------------------------------------*/

/* For the memory leak detector, say whether an entire 64k chunk of
   address space is possibly in use, or not.  If in doubt return
   True.
*/
Bool MC_(is_within_valid_secondary) ( Addr a )
{
   SecMap* sm = maybe_get_secmap_for ( a );
   if (sm == NULL || sm == &sm_distinguished[SM_DIST_NOACCESS]
       || MC_(in_ignored_range)(a)) {
      /* Definitely not in use. */
      return False;
   } else {
      return True;
   }
}


/* For the memory leak detector, say whether or not a given word
   address is to be regarded as valid. */
Bool MC_(is_valid_aligned_word) ( Addr a )
{
   tl_assert(sizeof(UWord) == 4 || sizeof(UWord) == 8);
   tl_assert(VG_IS_WORD_ALIGNED(a));
   if (is_mem_defined( a, sizeof(UWord), NULL, NULL) == MC_Ok
       && !MC_(in_ignored_range)(a)) {
      return True;
   } else {
      return False;
   }
}


/*------------------------------------------------------------*/
/*--- Initialisation                                       ---*/
/*------------------------------------------------------------*/

static void init_shadow_memory ( void )
{
   Int     i;
   SecMap* sm;

   tl_assert(V_BIT_UNDEFINED   == 1);
   tl_assert(V_BIT_DEFINED     == 0);
   tl_assert(V_BITS8_UNDEFINED == 0xFF);
   tl_assert(V_BITS8_DEFINED   == 0);

   /* Build the 3 distinguished secondaries */
   sm = &sm_distinguished[SM_DIST_NOACCESS];
   for (i = 0; i < SM_CHUNKS; i++) sm->vabits8[i] = VA_BITS8_NOACCESS;

   sm = &sm_distinguished[SM_DIST_UNDEFINED];
   for (i = 0; i < SM_CHUNKS; i++) sm->vabits8[i] = VA_BITS8_UNDEFINED;

   sm = &sm_distinguished[SM_DIST_DEFINED];
   for (i = 0; i < SM_CHUNKS; i++) sm->vabits8[i] = VA_BITS8_DEFINED;

   /* Set up the primary map. */
   /* These entries gradually get overwritten as the used address
      space expands. */
   for (i = 0; i < N_PRIMARY_MAP; i++)
      primary_map[i] = &sm_distinguished[SM_DIST_NOACCESS];

   /* Auxiliary primary maps */
   init_auxmap_L1_L2();

   /* auxmap_size = auxmap_used = 0; 
      no ... these are statically initialised */

   /* Secondary V bit table */
   secVBitTable = createSecVBitTable();
}


/*------------------------------------------------------------*/
/*--- Sanity check machinery (permanently engaged)         ---*/
/*------------------------------------------------------------*/

static Bool mc_cheap_sanity_check ( void )
{
   n_sanity_cheap++;
   PROF_EVENT(490, "cheap_sanity_check");
   /* Check for sane operating level */
   if (MC_(clo_mc_level) < 1 || MC_(clo_mc_level) > 3)
      return False;
   /* nothing else useful we can rapidly check */
   return True;
}

static Bool mc_expensive_sanity_check ( void )
{
   Int     i;
   Word    n_secmaps_found;
   SecMap* sm;
   HChar*  errmsg;
   Bool    bad = False;

   if (0) VG_(printf)("expensive sanity check\n");
   if (0) return True;

   n_sanity_expensive++;
   PROF_EVENT(491, "expensive_sanity_check");

   /* Check for sane operating level */
   if (MC_(clo_mc_level) < 1 || MC_(clo_mc_level) > 3)
      return False;

   /* Check that the 3 distinguished SMs are still as they should be. */

   /* Check noaccess DSM. */
   sm = &sm_distinguished[SM_DIST_NOACCESS];
   for (i = 0; i < SM_CHUNKS; i++)
      if (sm->vabits8[i] != VA_BITS8_NOACCESS)
         bad = True;

   /* Check undefined DSM. */
   sm = &sm_distinguished[SM_DIST_UNDEFINED];
   for (i = 0; i < SM_CHUNKS; i++)
      if (sm->vabits8[i] != VA_BITS8_UNDEFINED)
         bad = True;

   /* Check defined DSM. */
   sm = &sm_distinguished[SM_DIST_DEFINED];
   for (i = 0; i < SM_CHUNKS; i++)
      if (sm->vabits8[i] != VA_BITS8_DEFINED)
         bad = True;

   if (bad) {
      VG_(printf)("memcheck expensive sanity: "
                  "distinguished_secondaries have changed\n");
      return False;
   }

   /* If we're not checking for undefined value errors, the secondary V bit
    * table should be empty. */
   if (MC_(clo_mc_level) == 1) {
      if (0 != VG_(OSetGen_Size)(secVBitTable))
         return False;
   }

   /* check the auxiliary maps, very thoroughly */
   n_secmaps_found = 0;
   errmsg = check_auxmap_L1_L2_sanity( &n_secmaps_found );
   if (errmsg) {
      VG_(printf)("memcheck expensive sanity, auxmaps:\n\t%s", errmsg);
      return False;
   }

   /* n_secmaps_found is now the number referred to by the auxiliary
      primary map.  Now add on the ones referred to by the main
      primary map. */
   for (i = 0; i < N_PRIMARY_MAP; i++) {
      if (primary_map[i] == NULL) {
         bad = True;
      } else {
         if (!is_distinguished_sm(primary_map[i]))
            n_secmaps_found++;
      }
   }

   /* check that the number of secmaps issued matches the number that
      are reachable (iow, no secmap leaks) */
   if (n_secmaps_found != (n_issued_SMs - n_deissued_SMs))
      bad = True;

   if (bad) {
      VG_(printf)("memcheck expensive sanity: "
                  "apparent secmap leakage\n");
      return False;
   }

   if (bad) {
      VG_(printf)("memcheck expensive sanity: "
                  "auxmap covers wrong address space\n");
      return False;
   }

   /* there is only one pointer to each secmap (expensive) */

   return True;
}

/*------------------------------------------------------------*/
/*--- Command line args                                    ---*/
/*------------------------------------------------------------*/

Bool          MC_(clo_partial_loads_ok)       = False;
Long          MC_(clo_freelist_vol)           = 10*1000*1000LL;
LeakCheckMode MC_(clo_leak_check)             = LC_Summary;
VgRes         MC_(clo_leak_resolution)        = Vg_LowRes;
Bool          MC_(clo_show_reachable)         = False;
Bool          MC_(clo_workaround_gcc296_bugs) = False;
Int           MC_(clo_malloc_fill)            = -1;
Int           MC_(clo_free_fill)              = -1;
Int           MC_(clo_mc_level)               = 2;

static Bool mc_process_cmd_line_options(Char* arg)
{
   Char* tmp_str;
   Char* bad_level_msg =
      "ERROR: --track-origins=yes has no effect when --undef-value-errors=no";

   tl_assert( MC_(clo_mc_level) >= 1 && MC_(clo_mc_level) <= 3 );

   /* Set MC_(clo_mc_level):
         1 = A bit tracking only
         2 = A and V bit tracking, but no V bit origins
         3 = A and V bit tracking, and V bit origins

      Do this by inspecting --undef-value-errors= and
      --track-origins=.  Reject the case --undef-value-errors=no
      --track-origins=yes as meaningless.
   */
   if (0 == VG_(strcmp)(arg, "--undef-value-errors=no")) {
      if (MC_(clo_mc_level) == 3) {
         VG_(message)(Vg_DebugMsg, "%s", bad_level_msg);
         return False;
      } else {
         MC_(clo_mc_level) = 1;
         return True;
      }
   }
   if (0 == VG_(strcmp)(arg, "--undef-value-errors=yes")) {
      if (MC_(clo_mc_level) == 1)
         MC_(clo_mc_level) = 2;
      return True;
   }
   if (0 == VG_(strcmp)(arg, "--track-origins=no")) {
      if (MC_(clo_mc_level) == 3)
         MC_(clo_mc_level) = 2;
      return True;
   }
   if (0 == VG_(strcmp)(arg, "--track-origins=yes")) {
      if (MC_(clo_mc_level) == 1) {
         VG_(message)(Vg_DebugMsg, "%s", bad_level_msg);
         return False;
      } else {
         MC_(clo_mc_level) = 3;
         return True;
      }
   }

	if VG_BOOL_CLO(arg, "--partial-loads-ok", MC_(clo_partial_loads_ok)) {}
   else if VG_BOOL_CLO(arg, "--show-reachable",   MC_(clo_show_reachable))   {}
   else if VG_BOOL_CLO(arg, "--workaround-gcc296-bugs",
                                            MC_(clo_workaround_gcc296_bugs)) {}

   else if VG_BINT_CLO(arg, "--freelist-vol",  MC_(clo_freelist_vol), 
                                               0, 10*1000*1000*1000LL) {}
   
   else if VG_XACT_CLO(arg, "--leak-check=no",
                            MC_(clo_leak_check), LC_Off) {}
   else if VG_XACT_CLO(arg, "--leak-check=summary",
                            MC_(clo_leak_check), LC_Summary) {}
   else if VG_XACT_CLO(arg, "--leak-check=yes",
                            MC_(clo_leak_check), LC_Full) {}
   else if VG_XACT_CLO(arg, "--leak-check=full",
                            MC_(clo_leak_check), LC_Full) {}

   else if VG_XACT_CLO(arg, "--leak-resolution=low",
                            MC_(clo_leak_resolution), Vg_LowRes) {}
   else if VG_XACT_CLO(arg, "--leak-resolution=med",
                            MC_(clo_leak_resolution), Vg_MedRes) {}
   else if VG_XACT_CLO(arg, "--leak-resolution=high",
                            MC_(clo_leak_resolution), Vg_HighRes) {}

   else if VG_STR_CLO(arg, "--ignore-ranges", tmp_str) {
      Int  i;
      Bool ok  = parse_ignore_ranges(tmp_str);
      if (!ok)
        return False;
      tl_assert(ignoreRanges.used >= 0);
      tl_assert(ignoreRanges.used < M_IGNORE_RANGES);
      for (i = 0; i < ignoreRanges.used; i++) {
         Addr s = ignoreRanges.start[i];
         Addr e = ignoreRanges.end[i];
         Addr limit = 0x4000000; /* 64M - entirely arbitrary limit */
         if (e <= s) {
            VG_(message)(Vg_DebugMsg, 
               "ERROR: --ignore-ranges: end <= start in range:");
            VG_(message)(Vg_DebugMsg, 
               "       0x%lx-0x%lx", s, e);
            return False;
         }
         if (e - s > limit) {
            VG_(message)(Vg_DebugMsg, 
               "ERROR: --ignore-ranges: suspiciously large range:");
            VG_(message)(Vg_DebugMsg, 
               "       0x%lx-0x%lx (size %ld)", s, e, (UWord)(e-s));
            return False;
	 }
      }
   }

   else if VG_BHEX_CLO(arg, "--malloc-fill", MC_(clo_malloc_fill), 0x00,0xFF) {}
   else if VG_BHEX_CLO(arg, "--free-fill",   MC_(clo_free_fill),   0x00,0xFF) {}

   else
      return VG_(replacement_malloc_process_cmd_line_option)(arg);

   return True;
}

static void mc_print_usage(void)
{  
   VG_(printf)(
"    --leak-check=no|summary|full     search for memory leaks at exit?  [summary]\n"
"    --leak-resolution=low|med|high   how much bt merging in leak check [low]\n"
"    --show-reachable=no|yes          show reachable blocks in leak check? [no]\n"
"    --undef-value-errors=no|yes      check for undefined value errors [yes]\n"
"    --track-origins=no|yes           show origins of undefined values? [no]\n"
"    --partial-loads-ok=no|yes        too hard to explain here; see manual [no]\n"
"    --freelist-vol=<number>          volume of freed blocks queue [10000000]\n"
"    --workaround-gcc296-bugs=no|yes  self explanatory [no]\n"
"    --ignore-ranges=0xPP-0xQQ[,0xRR-0xSS]   assume given addresses are OK\n"
"    --malloc-fill=<hexnumber>        fill malloc'd areas with given value\n"
"    --free-fill=<hexnumber>          fill free'd areas with given value\n"
   );
   VG_(replacement_malloc_print_usage)();
}

static void mc_print_debug_usage(void)
{  
   VG_(replacement_malloc_print_debug_usage)();
}


/*------------------------------------------------------------*/
/*--- Client blocks                                        ---*/
/*------------------------------------------------------------*/

/* Client block management:
  
   This is managed as an expanding array of client block descriptors.
   Indices of live descriptors are issued to the client, so it can ask
   to free them later.  Therefore we cannot slide live entries down
   over dead ones.  Instead we must use free/inuse flags and scan for
   an empty slot at allocation time.  This in turn means allocation is
   relatively expensive, so we hope this does not happen too often. 

   An unused block has start == size == 0
*/

/* type CGenBlock is defined in mc_include.h */

/* This subsystem is self-initialising. */
static UWord      cgb_size = 0;
static UWord      cgb_used = 0;
static CGenBlock* cgbs     = NULL;

/* Stats for this subsystem. */
static ULong cgb_used_MAX = 0;   /* Max in use. */
static ULong cgb_allocs   = 0;   /* Number of allocs. */
static ULong cgb_discards = 0;   /* Number of discards. */
static ULong cgb_search   = 0;   /* Number of searches. */


/* Get access to the client block array. */
void MC_(get_ClientBlock_array)( /*OUT*/CGenBlock** blocks,
                                 /*OUT*/UWord* nBlocks )
{
   *blocks  = cgbs;
   *nBlocks = cgb_used;
}


static
Int alloc_client_block ( void )
{
   UWord      i, sz_new;
   CGenBlock* cgbs_new;

   cgb_allocs++;

   for (i = 0; i < cgb_used; i++) {
      cgb_search++;
      if (cgbs[i].start == 0 && cgbs[i].size == 0)
         return i;
   }

   /* Not found.  Try to allocate one at the end. */
   if (cgb_used < cgb_size) {
      cgb_used++;
      return cgb_used-1;
   }

   /* Ok, we have to allocate a new one. */
   tl_assert(cgb_used == cgb_size);
   sz_new = (cgbs == NULL) ? 10 : (2 * cgb_size);

   cgbs_new = VG_(malloc)( "mc.acb.1", sz_new * sizeof(CGenBlock) );
   for (i = 0; i < cgb_used; i++) 
      cgbs_new[i] = cgbs[i];

   if (cgbs != NULL)
      VG_(free)( cgbs );
   cgbs = cgbs_new;

   cgb_size = sz_new;
   cgb_used++;
   if (cgb_used > cgb_used_MAX)
      cgb_used_MAX = cgb_used;
   return cgb_used-1;
}


static void show_client_block_stats ( void )
{
   VG_(message)(Vg_DebugMsg, 
      "general CBs: %llu allocs, %llu discards, %llu maxinuse, %llu search",
      cgb_allocs, cgb_discards, cgb_used_MAX, cgb_search 
   );
}


/*------------------------------------------------------------*/
/*--- Client requests                                      ---*/
/*------------------------------------------------------------*/

static Bool mc_handle_client_request ( ThreadId tid, UWord* arg, UWord* ret )
{
   Int   i;
   Bool  ok;
   Addr  bad_addr;

   if (!VG_IS_TOOL_USERREQ('M','C',arg[0])
       && VG_USERREQ__MALLOCLIKE_BLOCK != arg[0]
       && VG_USERREQ__FREELIKE_BLOCK   != arg[0]
       && VG_USERREQ__CREATE_MEMPOOL   != arg[0]
       && VG_USERREQ__DESTROY_MEMPOOL  != arg[0]
       && VG_USERREQ__MEMPOOL_ALLOC    != arg[0]
       && VG_USERREQ__MEMPOOL_FREE     != arg[0]
       && VG_USERREQ__MEMPOOL_TRIM     != arg[0]
       && VG_USERREQ__MOVE_MEMPOOL     != arg[0]
       && VG_USERREQ__MEMPOOL_CHANGE   != arg[0]
       && VG_USERREQ__MEMPOOL_EXISTS   != arg[0])
      return False;

   switch (arg[0]) {
      case VG_USERREQ__CHECK_MEM_IS_ADDRESSABLE:
         ok = is_mem_addressable ( arg[1], arg[2], &bad_addr );
         if (!ok)
            MC_(record_user_error) ( tid, bad_addr, /*isAddrErr*/True, 0 );
         *ret = ok ? (UWord)NULL : bad_addr;
         break;

      case VG_USERREQ__CHECK_MEM_IS_DEFINED: {
         MC_ReadResult res;
         UInt otag = 0;
         res = is_mem_defined ( arg[1], arg[2], &bad_addr, &otag );
         if (MC_AddrErr == res)
            MC_(record_user_error) ( tid, bad_addr, /*isAddrErr*/True, 0 );
         else if (MC_ValueErr == res)
            MC_(record_user_error) ( tid, bad_addr, /*isAddrErr*/False, otag );
         *ret = ( res==MC_Ok ? (UWord)NULL : bad_addr );
         break;
      }

      case VG_USERREQ__DO_LEAK_CHECK:
         MC_(detect_memory_leaks)(tid, arg[1] ? LC_Summary : LC_Full);
         *ret = 0; /* return value is meaningless */
         break;

      case VG_USERREQ__MAKE_MEM_NOACCESS:
         MC_(make_mem_noaccess) ( arg[1], arg[2] );
         *ret = -1;
         break;

      case VG_USERREQ__MAKE_MEM_UNDEFINED:
         make_mem_undefined_w_tid_and_okind ( arg[1], arg[2], tid, 
                                              MC_OKIND_USER );
         *ret = -1;
         break;

      case VG_USERREQ__MAKE_MEM_DEFINED:
         MC_(make_mem_defined) ( arg[1], arg[2] );
         *ret = -1;
         break;

      case VG_USERREQ__MAKE_MEM_DEFINED_IF_ADDRESSABLE:
         make_mem_defined_if_addressable ( arg[1], arg[2] );
         *ret = -1;
         break;

      case VG_USERREQ__CREATE_BLOCK: /* describe a block */
         if (arg[1] != 0 && arg[2] != 0) {
            i = alloc_client_block();
            /* VG_(printf)("allocated %d %p\n", i, cgbs); */
            cgbs[i].start = arg[1];
            cgbs[i].size  = arg[2];
            cgbs[i].desc  = VG_(strdup)("mc.mhcr.1", (Char *)arg[3]);
            cgbs[i].where = VG_(record_ExeContext) ( tid, 0/*first_ip_delta*/ );
            *ret = i;
         } else
            *ret = -1;
         break;

      case VG_USERREQ__DISCARD: /* discard */
         if (cgbs == NULL 
             || arg[2] >= cgb_used ||
             (cgbs[arg[2]].start == 0 && cgbs[arg[2]].size == 0)) {
            *ret = 1;
         } else {
            tl_assert(arg[2] >= 0 && arg[2] < cgb_used);
            cgbs[arg[2]].start = cgbs[arg[2]].size = 0;
            VG_(free)(cgbs[arg[2]].desc);
            cgb_discards++;
            *ret = 0;
         }
         break;

      case VG_USERREQ__GET_VBITS:
         *ret = mc_get_or_set_vbits_for_client
                   ( arg[1], arg[2], arg[3], False /* get them */ );
         break;

      case VG_USERREQ__SET_VBITS:
         *ret = mc_get_or_set_vbits_for_client
                   ( arg[1], arg[2], arg[3], True /* set them */ );
         break;

      case VG_USERREQ__COUNT_LEAKS: { /* count leaked bytes */
         UWord** argp = (UWord**)arg;
         // MC_(bytes_leaked) et al were set by the last leak check (or zero
         // if no prior leak checks performed).
         *argp[1] = MC_(bytes_leaked) + MC_(bytes_indirect);
         *argp[2] = MC_(bytes_dubious);
         *argp[3] = MC_(bytes_reachable);
         *argp[4] = MC_(bytes_suppressed);
         // there is no argp[5]
         //*argp[5] = MC_(bytes_indirect);
         // XXX need to make *argp[1-4] defined;  currently done in the
         // VALGRIND_COUNT_LEAKS_MACRO by initialising them to zero.
         *ret = 0;
         return True;
      }
      case VG_USERREQ__COUNT_LEAK_BLOCKS: { /* count leaked blocks */
         UWord** argp = (UWord**)arg;
         // MC_(blocks_leaked) et al were set by the last leak check (or zero
         // if no prior leak checks performed).
         *argp[1] = MC_(blocks_leaked) + MC_(blocks_indirect);
         *argp[2] = MC_(blocks_dubious);
         *argp[3] = MC_(blocks_reachable);
         *argp[4] = MC_(blocks_suppressed);
         // there is no argp[5]
         //*argp[5] = MC_(blocks_indirect);
         // XXX need to make *argp[1-4] defined;  currently done in the
         // VALGRIND_COUNT_LEAK_BLOCKS_MACRO by initialising them to zero.
         *ret = 0;
         return True;
      }
      case VG_USERREQ__MALLOCLIKE_BLOCK: {
         Addr p         = (Addr)arg[1];
         SizeT sizeB    =       arg[2];
         //UInt rzB       =       arg[3];    XXX: unused!
         Bool is_zeroed = (Bool)arg[4];

         MC_(new_block) ( tid, p, sizeB, /*ignored*/0, is_zeroed, 
                          MC_AllocCustom, MC_(malloc_list) );
         return True;
      }
      case VG_USERREQ__FREELIKE_BLOCK: {
         Addr p         = (Addr)arg[1];
         UInt rzB       =       arg[2];

         MC_(handle_free) ( tid, p, rzB, MC_AllocCustom );
         return True;
      }

      case _VG_USERREQ__MEMCHECK_RECORD_OVERLAP_ERROR: {
         Char* s   = (Char*)arg[1];
         Addr  dst = (Addr) arg[2];
         Addr  src = (Addr) arg[3];
         SizeT len = (SizeT)arg[4];
         MC_(record_overlap_error)(tid, s, src, dst, len);
         return True;
      }

      case VG_USERREQ__CREATE_MEMPOOL: {
         Addr pool      = (Addr)arg[1];
         UInt rzB       =       arg[2];
         Bool is_zeroed = (Bool)arg[3];

         MC_(create_mempool) ( pool, rzB, is_zeroed );
         return True;
      }

      case VG_USERREQ__DESTROY_MEMPOOL: {
         Addr pool      = (Addr)arg[1];

         MC_(destroy_mempool) ( pool );
         return True;
      }

      case VG_USERREQ__MEMPOOL_ALLOC: {
         Addr pool      = (Addr)arg[1];
         Addr addr      = (Addr)arg[2];
         UInt size      =       arg[3];

         MC_(mempool_alloc) ( tid, pool, addr, size );
         return True;
      }

      case VG_USERREQ__MEMPOOL_FREE: {
         Addr pool      = (Addr)arg[1];
         Addr addr      = (Addr)arg[2];

         MC_(mempool_free) ( pool, addr );
         return True;
      }

      case VG_USERREQ__MEMPOOL_TRIM: {
         Addr pool      = (Addr)arg[1];
         Addr addr      = (Addr)arg[2];
         UInt size      =       arg[3];

         MC_(mempool_trim) ( pool, addr, size );
         return True;
      }

      case VG_USERREQ__MOVE_MEMPOOL: {
         Addr poolA     = (Addr)arg[1];
         Addr poolB     = (Addr)arg[2];

         MC_(move_mempool) ( poolA, poolB );
         return True;
      }

      case VG_USERREQ__MEMPOOL_CHANGE: {
         Addr pool      = (Addr)arg[1];
         Addr addrA     = (Addr)arg[2];
         Addr addrB     = (Addr)arg[3];
         UInt size      =       arg[4];

         MC_(mempool_change) ( pool, addrA, addrB, size );
         return True;
      }

      case VG_USERREQ__MEMPOOL_EXISTS: {
         Addr pool      = (Addr)arg[1];

         *ret = (UWord) MC_(mempool_exists) ( pool );
	 return True;
      }


      default:
         VG_(message)(Vg_UserMsg, 
                      "Warning: unknown memcheck client request code %llx",
                      (ULong)arg[0]);
         return False;
   }
   return True;
}


/*------------------------------------------------------------*/
/*--- Crude profiling machinery.                           ---*/
/*------------------------------------------------------------*/

// We track a number of interesting events (using PROF_EVENT)
// if MC_PROFILE_MEMORY is defined.

#ifdef MC_PROFILE_MEMORY

UInt   MC_(event_ctr)[N_PROF_EVENTS];
HChar* MC_(event_ctr_name)[N_PROF_EVENTS];

static void init_prof_mem ( void )
{
   Int i;
   for (i = 0; i < N_PROF_EVENTS; i++) {
      MC_(event_ctr)[i] = 0;
      MC_(event_ctr_name)[i] = NULL;
   }
}

static void done_prof_mem ( void )
{
   Int  i;
   Bool spaced = False;
   for (i = 0; i < N_PROF_EVENTS; i++) {
      if (!spaced && (i % 10) == 0) {
         VG_(printf)("\n");
         spaced = True;
      }
      if (MC_(event_ctr)[i] > 0) {
         spaced = False;
         VG_(printf)( "prof mem event %3d: %9d   %s\n", 
                      i, MC_(event_ctr)[i],
                      MC_(event_ctr_name)[i] 
                         ? MC_(event_ctr_name)[i] : "unnamed");
      }
   }
}

#else

static void init_prof_mem ( void ) { }
static void done_prof_mem ( void ) { }

#endif


/*------------------------------------------------------------*/
/*--- Origin tracking stuff                                ---*/
/*------------------------------------------------------------*/

/*--------------------------------------------*/
/*--- Origin tracking: load handlers       ---*/
/*--------------------------------------------*/

static INLINE UInt merge_origins ( UInt or1, UInt or2 ) {
   return or1 > or2 ? or1 : or2;
}

UWord VG_REGPARM(1) MC_(helperc_b_load1)( Addr a ) {
   OCacheLine* line;
   UChar descr;
   UWord lineoff = oc_line_offset(a);
   UWord byteoff = a & 3; /* 0, 1, 2 or 3 */

   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
   }

   line = find_OCacheLine( a );

   descr = line->descr[lineoff];
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(descr < 0x10);
   }

   if (LIKELY(0 == (descr & (1 << byteoff))))  {
      return 0;
   } else {
      return line->w32[lineoff];
   }
}

UWord VG_REGPARM(1) MC_(helperc_b_load2)( Addr a ) {
   OCacheLine* line;
   UChar descr;
   UWord lineoff, byteoff;

   if (UNLIKELY(a & 1)) {
      /* Handle misaligned case, slowly. */
      UInt oLo   = (UInt)MC_(helperc_b_load1)( a + 0 );
      UInt oHi   = (UInt)MC_(helperc_b_load1)( a + 1 );
      return merge_origins(oLo, oHi);
   }

   lineoff = oc_line_offset(a);
   byteoff = a & 3; /* 0 or 2 */

   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
   }
   line = find_OCacheLine( a );

   descr = line->descr[lineoff];
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(descr < 0x10);
   }

   if (LIKELY(0 == (descr & (3 << byteoff)))) {
      return 0;
   } else {
      return line->w32[lineoff];
   }
}

UWord VG_REGPARM(1) MC_(helperc_b_load4)( Addr a ) {
   OCacheLine* line;
   UChar descr;
   UWord lineoff;

   if (UNLIKELY(a & 3)) {
      /* Handle misaligned case, slowly. */
      UInt oLo   = (UInt)MC_(helperc_b_load2)( a + 0 );
      UInt oHi   = (UInt)MC_(helperc_b_load2)( a + 2 );
      return merge_origins(oLo, oHi);
   }

   lineoff = oc_line_offset(a);
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
   }

   line = find_OCacheLine( a );

   descr = line->descr[lineoff];
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(descr < 0x10);
   }

   if (LIKELY(0 == descr)) {
      return 0;
   } else {
      return line->w32[lineoff];
   }
}

UWord VG_REGPARM(1) MC_(helperc_b_load8)( Addr a ) {
   OCacheLine* line;
   UChar descrLo, descrHi, descr;
   UWord lineoff;

   if (UNLIKELY(a & 7)) {
      /* Handle misaligned case, slowly. */
      UInt oLo   = (UInt)MC_(helperc_b_load4)( a + 0 );
      UInt oHi   = (UInt)MC_(helperc_b_load4)( a + 4 );
      return merge_origins(oLo, oHi);
   }

   lineoff = oc_line_offset(a);
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff == (lineoff & 6)); /*0,2,4,6*//*since 8-aligned*/
   }

   line = find_OCacheLine( a );

   descrLo = line->descr[lineoff + 0];
   descrHi = line->descr[lineoff + 1];
   descr   = descrLo | descrHi;
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(descr < 0x10);
   }

   if (LIKELY(0 == descr)) {
      return 0; /* both 32-bit chunks are defined */
   } else {
      UInt oLo = descrLo == 0 ? 0 : line->w32[lineoff + 0];
      UInt oHi = descrHi == 0 ? 0 : line->w32[lineoff + 1];
      return merge_origins(oLo, oHi);
   }
}

UWord VG_REGPARM(1) MC_(helperc_b_load16)( Addr a ) {
   UInt oLo   = (UInt)MC_(helperc_b_load8)( a + 0 );
   UInt oHi   = (UInt)MC_(helperc_b_load8)( a + 8 );
   UInt oBoth = merge_origins(oLo, oHi);
   return (UWord)oBoth;
}


/*--------------------------------------------*/
/*--- Origin tracking: store handlers      ---*/
/*--------------------------------------------*/

void VG_REGPARM(2) MC_(helperc_b_store1)( Addr a, UWord d32 ) {
   OCacheLine* line;
   UWord lineoff = oc_line_offset(a);
   UWord byteoff = a & 3; /* 0, 1, 2 or 3 */

   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
   }

   line = find_OCacheLine( a );

   if (d32 == 0) {
      line->descr[lineoff] &= ~(1 << byteoff);
   } else {
      line->descr[lineoff] |= (1 << byteoff);
      line->w32[lineoff] = d32;
   }
}

void VG_REGPARM(2) MC_(helperc_b_store2)( Addr a, UWord d32 ) {
   OCacheLine* line;
   UWord lineoff, byteoff;

   if (UNLIKELY(a & 1)) {
      /* Handle misaligned case, slowly. */
      MC_(helperc_b_store1)( a + 0, d32 );
      MC_(helperc_b_store1)( a + 1, d32 );
      return;
   }

   lineoff = oc_line_offset(a);
   byteoff = a & 3; /* 0 or 2 */

   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
   }

   line = find_OCacheLine( a );

   if (d32 == 0) {
      line->descr[lineoff] &= ~(3 << byteoff);
   } else {
      line->descr[lineoff] |= (3 << byteoff);
      line->w32[lineoff] = d32;
   }
}

void VG_REGPARM(2) MC_(helperc_b_store4)( Addr a, UWord d32 ) {
   OCacheLine* line;
   UWord lineoff;

   if (UNLIKELY(a & 3)) {
      /* Handle misaligned case, slowly. */
      MC_(helperc_b_store2)( a + 0, d32 );
      MC_(helperc_b_store2)( a + 2, d32 );
      return;
   }

   lineoff = oc_line_offset(a);
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff >= 0 && lineoff < OC_W32S_PER_LINE);
   }

   line = find_OCacheLine( a );

   if (d32 == 0) {
      line->descr[lineoff] = 0;
   } else {
      line->descr[lineoff] = 0xF;
      line->w32[lineoff] = d32;
   }
}

void VG_REGPARM(2) MC_(helperc_b_store8)( Addr a, UWord d32 ) {
   OCacheLine* line;
   UWord lineoff;

   if (UNLIKELY(a & 7)) {
      /* Handle misaligned case, slowly. */
      MC_(helperc_b_store4)( a + 0, d32 );
      MC_(helperc_b_store4)( a + 4, d32 );
      return;
   }

   lineoff = oc_line_offset(a);
   if (OC_ENABLE_ASSERTIONS) {
      tl_assert(lineoff == (lineoff & 6)); /*0,2,4,6*//*since 8-aligned*/
   }

   line = find_OCacheLine( a );

   if (d32 == 0) {
      line->descr[lineoff + 0] = 0;
      line->descr[lineoff + 1] = 0;
   } else {
      line->descr[lineoff + 0] = 0xF;
      line->descr[lineoff + 1] = 0xF;
      line->w32[lineoff + 0] = d32;
      line->w32[lineoff + 1] = d32;
   }
}

void VG_REGPARM(2) MC_(helperc_b_store16)( Addr a, UWord d32 ) {
   MC_(helperc_b_store8)( a + 0, d32 );
   MC_(helperc_b_store8)( a + 8, d32 );
}


/*--------------------------------------------*/
/*--- Origin tracking: sarp handlers       ---*/
/*--------------------------------------------*/

__attribute__((noinline))
static void ocache_sarp_Set_Origins ( Addr a, UWord len, UInt otag ) {
   if ((a & 1) && len >= 1) {
      MC_(helperc_b_store1)( a, otag );
      a++;
      len--;
   }
   if ((a & 2) && len >= 2) {
      MC_(helperc_b_store2)( a, otag );
      a += 2;
      len -= 2;
   }
   if (len >= 4) 
      tl_assert(0 == (a & 3));
   while (len >= 4) {
      MC_(helperc_b_store4)( a, otag );
      a += 4;
      len -= 4;
   }
   if (len >= 2) {
      MC_(helperc_b_store2)( a, otag );
      a += 2;
      len -= 2;
   }
   if (len >= 1) {
      MC_(helperc_b_store1)( a, otag );
      //a++;
      len--;
   }
   tl_assert(len == 0);
}

__attribute__((noinline))
static void ocache_sarp_Clear_Origins ( Addr a, UWord len ) {
   if ((a & 1) && len >= 1) {
      MC_(helperc_b_store1)( a, 0 );
      a++;
      len--;
   }
   if ((a & 2) && len >= 2) {
      MC_(helperc_b_store2)( a, 0 );
      a += 2;
      len -= 2;
   }
   if (len >= 4) 
      tl_assert(0 == (a & 3));
   while (len >= 4) {
      MC_(helperc_b_store4)( a, 0 );
      a += 4;
      len -= 4;
   }
   if (len >= 2) {
      MC_(helperc_b_store2)( a, 0 );
      a += 2;
      len -= 2;
   }
   if (len >= 1) {
      MC_(helperc_b_store1)( a, 0 );
      //a++;
      len--;
   }
   tl_assert(len == 0);
}


/*------------------------------------------------------------*/
/*--- Setup and finalisation                               ---*/
/*------------------------------------------------------------*/

static void mc_post_clo_init ( void )
{
   /* If we've been asked to emit XML, mash around various other
      options so as to constrain the output somewhat. */
   if (VG_(clo_xml)) {
      /* Extract as much info as possible from the leak checker. */
      /* MC_(clo_show_reachable) = True; */
      MC_(clo_leak_check) = LC_Full;
   }

   tl_assert( MC_(clo_mc_level) >= 1 && MC_(clo_mc_level) <= 3 );

   if (MC_(clo_mc_level) == 3) {
      /* We're doing origin tracking. */
#     ifdef PERF_FAST_STACK
      VG_(track_new_mem_stack_4_w_ECU)   ( mc_new_mem_stack_4_w_ECU   );
      VG_(track_new_mem_stack_8_w_ECU)   ( mc_new_mem_stack_8_w_ECU   );
      VG_(track_new_mem_stack_12_w_ECU)  ( mc_new_mem_stack_12_w_ECU  );
      VG_(track_new_mem_stack_16_w_ECU)  ( mc_new_mem_stack_16_w_ECU  );
      VG_(track_new_mem_stack_32_w_ECU)  ( mc_new_mem_stack_32_w_ECU  );
      VG_(track_new_mem_stack_112_w_ECU) ( mc_new_mem_stack_112_w_ECU );
      VG_(track_new_mem_stack_128_w_ECU) ( mc_new_mem_stack_128_w_ECU );
      VG_(track_new_mem_stack_144_w_ECU) ( mc_new_mem_stack_144_w_ECU );
      VG_(track_new_mem_stack_160_w_ECU) ( mc_new_mem_stack_160_w_ECU );
#     endif
      VG_(track_new_mem_stack_w_ECU)     ( mc_new_mem_stack_w_ECU     );
   } else {
      /* Not doing origin tracking */
#     ifdef PERF_FAST_STACK
      VG_(track_new_mem_stack_4)   ( mc_new_mem_stack_4   );
      VG_(track_new_mem_stack_8)   ( mc_new_mem_stack_8   );
      VG_(track_new_mem_stack_12)  ( mc_new_mem_stack_12  );
      VG_(track_new_mem_stack_16)  ( mc_new_mem_stack_16  );
      VG_(track_new_mem_stack_32)  ( mc_new_mem_stack_32  );
      VG_(track_new_mem_stack_112) ( mc_new_mem_stack_112 );
      VG_(track_new_mem_stack_128) ( mc_new_mem_stack_128 );
      VG_(track_new_mem_stack_144) ( mc_new_mem_stack_144 );
      VG_(track_new_mem_stack_160) ( mc_new_mem_stack_160 );
#     endif
      VG_(track_new_mem_stack)     ( mc_new_mem_stack     );
   }

   /* This origin tracking cache is huge (~100M), so only initialise
      if we need it. */
   if (MC_(clo_mc_level) >= 3) {
      init_OCache();
      tl_assert(ocacheL1 != NULL);
      tl_assert(ocacheL2 != NULL);
   } else {
      tl_assert(ocacheL1 == NULL);
      tl_assert(ocacheL2 == NULL);
   }
}

static void print_SM_info(char* type, int n_SMs)
{
   VG_(message)(Vg_DebugMsg,
      " memcheck: SMs: %s = %d (%ldk, %ldM)",
      type,
      n_SMs,
      n_SMs * sizeof(SecMap) / 1024UL,
      n_SMs * sizeof(SecMap) / (1024 * 1024UL) );
}

static void mc_fini ( Int exitcode )
{
   MC_(print_malloc_stats)();

   if (VG_(clo_verbosity) == 1 && !VG_(clo_xml)) {
      if (MC_(clo_leak_check) == LC_Off)
         VG_(message)(Vg_UserMsg, 
             "For a detailed leak analysis,  rerun with: --leak-check=yes");

      VG_(message)(Vg_UserMsg, 
                   "For counts of detected errors, rerun with: -v");
   }


   if (MC_(any_value_errors) && !VG_(clo_xml) && VG_(clo_verbosity) >= 1
       && MC_(clo_mc_level) == 2) {
      VG_(message)(Vg_UserMsg,
                   "Use --track-origins=yes to see where "
                   "uninitialised values come from");
   }

   if (MC_(clo_leak_check) != LC_Off)
      MC_(detect_memory_leaks)(1/*bogus ThreadId*/, MC_(clo_leak_check));

   done_prof_mem();

   if (VG_(clo_verbosity) > 1) {
      SizeT max_secVBit_szB, max_SMs_szB, max_shmem_szB;
      
      VG_(message)(Vg_DebugMsg,
         " memcheck: sanity checks: %d cheap, %d expensive",
         n_sanity_cheap, n_sanity_expensive );
      VG_(message)(Vg_DebugMsg,
         " memcheck: auxmaps: %lld auxmap entries (%lldk, %lldM) in use",
         n_auxmap_L2_nodes, 
         n_auxmap_L2_nodes * 64, 
         n_auxmap_L2_nodes / 16 );
      VG_(message)(Vg_DebugMsg,
         " memcheck: auxmaps_L1: %lld searches, %lld cmps, ratio %lld:10",
         n_auxmap_L1_searches, n_auxmap_L1_cmps,
         (10ULL * n_auxmap_L1_cmps) 
            / (n_auxmap_L1_searches ? n_auxmap_L1_searches : 1) 
      );   
      VG_(message)(Vg_DebugMsg,
         " memcheck: auxmaps_L2: %lld searches, %lld nodes",
         n_auxmap_L2_searches, n_auxmap_L2_nodes
      );   

      print_SM_info("n_issued     ", n_issued_SMs);
      print_SM_info("n_deissued   ", n_deissued_SMs);
      print_SM_info("max_noaccess ", max_noaccess_SMs);
      print_SM_info("max_undefined", max_undefined_SMs);
      print_SM_info("max_defined  ", max_defined_SMs);
      print_SM_info("max_non_DSM  ", max_non_DSM_SMs);

      // Three DSMs, plus the non-DSM ones
      max_SMs_szB = (3 + max_non_DSM_SMs) * sizeof(SecMap);
      // The 3*sizeof(Word) bytes is the AVL node metadata size.
      // The 4*sizeof(Word) bytes is the malloc metadata size.
      // Hardwiring these sizes in sucks, but I don't see how else to do it.
      max_secVBit_szB = max_secVBit_nodes * 
            (sizeof(SecVBitNode) + 3*sizeof(Word) + 4*sizeof(Word));
      max_shmem_szB   = sizeof(primary_map) + max_SMs_szB + max_secVBit_szB;

      VG_(message)(Vg_DebugMsg,
         " memcheck: max sec V bit nodes:    %d (%ldk, %ldM)",
         max_secVBit_nodes, max_secVBit_szB / 1024,
                            max_secVBit_szB / (1024 * 1024));
      VG_(message)(Vg_DebugMsg,
         " memcheck: set_sec_vbits8 calls: %llu (new: %llu, updates: %llu)",
         sec_vbits_new_nodes + sec_vbits_updates,
         sec_vbits_new_nodes, sec_vbits_updates );
      VG_(message)(Vg_DebugMsg,
         " memcheck: max shadow mem size:   %ldk, %ldM",
         max_shmem_szB / 1024, max_shmem_szB / (1024 * 1024));

      if (MC_(clo_mc_level) >= 3) {
         VG_(message)(Vg_DebugMsg,
                      " ocacheL1: %'12lu refs   %'12lu misses (%'lu lossage)",
                      stats_ocacheL1_find, 
                      stats_ocacheL1_misses,
                      stats_ocacheL1_lossage );
         VG_(message)(Vg_DebugMsg,
                      " ocacheL1: %'12lu at 0   %'12lu at 1",
                      stats_ocacheL1_find - stats_ocacheL1_misses 
                         - stats_ocacheL1_found_at_1 
                         - stats_ocacheL1_found_at_N,
                      stats_ocacheL1_found_at_1 );
         VG_(message)(Vg_DebugMsg,
                      " ocacheL1: %'12lu at 2+  %'12lu move-fwds",
                      stats_ocacheL1_found_at_N,
                      stats_ocacheL1_movefwds );
         VG_(message)(Vg_DebugMsg,
                      " ocacheL1: %'12lu sizeB  %'12u useful",
                      (UWord)sizeof(OCache),
                      4 * OC_W32S_PER_LINE * OC_LINES_PER_SET * OC_N_SETS );
         VG_(message)(Vg_DebugMsg,
                      " ocacheL2: %'12lu refs   %'12lu misses",
                      stats__ocacheL2_refs, 
                      stats__ocacheL2_misses );
         VG_(message)(Vg_DebugMsg,
                      " ocacheL2:    %'9lu max nodes %'9lu curr nodes",
                      stats__ocacheL2_n_nodes_max,
                      stats__ocacheL2_n_nodes );
         VG_(message)(Vg_DebugMsg,
                      " niacache: %'12lu refs   %'12lu misses",
                      stats__nia_cache_queries, stats__nia_cache_misses);
      } else {
         tl_assert(ocacheL1 == NULL);
         tl_assert(ocacheL2 == NULL);
      }
   }

   if (0) {
      VG_(message)(Vg_DebugMsg, 
        "------ Valgrind's client block stats follow ---------------" );
      show_client_block_stats();
   }
}

static void mc_pre_clo_init(void)
{
   VG_(details_name)            ("Memcheck");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("a memory error detector");
   VG_(details_copyright_author)(
      "Copyright (C) 2002-2009, and GNU GPL'd, by Julian Seward et al.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);
   VG_(details_avg_translation_sizeB) ( 556 );

   VG_(basic_tool_funcs)          (mc_post_clo_init,
                                   MC_(instrument),
                                   mc_fini);

   VG_(needs_final_IR_tidy_pass)  ( MC_(final_tidy) );


   VG_(needs_core_errors)         ();
   VG_(needs_tool_errors)         (MC_(eq_Error),
                                   MC_(pp_Error),
                                   True,/*show TIDs for errors*/
                                   MC_(update_Error_extra),
                                   MC_(is_recognised_suppression),
                                   MC_(read_extra_suppression_info),
                                   MC_(error_matches_suppression),
                                   MC_(get_error_name),
                                   MC_(print_extra_suppression_info));
   VG_(needs_libc_freeres)        ();
   VG_(needs_command_line_options)(mc_process_cmd_line_options,
                                   mc_print_usage,
                                   mc_print_debug_usage);
   VG_(needs_client_requests)     (mc_handle_client_request);
   VG_(needs_sanity_checks)       (mc_cheap_sanity_check,
                                   mc_expensive_sanity_check);
   VG_(needs_malloc_replacement)  (MC_(malloc),
                                   MC_(__builtin_new),
                                   MC_(__builtin_vec_new),
                                   MC_(memalign),
                                   MC_(calloc),
                                   MC_(free),
                                   MC_(__builtin_delete),
                                   MC_(__builtin_vec_delete),
                                   MC_(realloc),
                                   MC_(malloc_usable_size), 
                                   MC_MALLOC_REDZONE_SZB );
   VG_(needs_xml_output)          ();

   VG_(track_new_mem_startup)     ( mc_new_mem_startup );
   VG_(track_new_mem_stack_signal)( make_mem_undefined_w_tid );
   VG_(track_new_mem_brk)         ( make_mem_undefined_w_tid );
   VG_(track_new_mem_mmap)        ( mc_new_mem_mmap );
   
   VG_(track_copy_mem_remap)      ( MC_(copy_address_range_state) );

   // Nb: we don't do anything with mprotect.  This means that V bits are
   // preserved if a program, for example, marks some memory as inaccessible
   // and then later marks it as accessible again.
   // 
   // If an access violation occurs (eg. writing to read-only memory) we let
   // it fault and print an informative termination message.  This doesn't
   // happen if the program catches the signal, though, which is bad.  If we
   // had two A bits (for readability and writability) that were completely
   // distinct from V bits, then we could handle all this properly.
   VG_(track_change_mem_mprotect) ( NULL );
      
   VG_(track_die_mem_stack_signal)( MC_(make_mem_noaccess) ); 
   VG_(track_die_mem_brk)         ( MC_(make_mem_noaccess) );
   VG_(track_die_mem_munmap)      ( MC_(make_mem_noaccess) ); 

   /* Defer the specification of the new_mem_stack functions to the
      post_clo_init function, since we need to first parse the command
      line before deciding which set to use. */

#  ifdef PERF_FAST_STACK
   VG_(track_die_mem_stack_4)     ( mc_die_mem_stack_4   );
   VG_(track_die_mem_stack_8)     ( mc_die_mem_stack_8   );
   VG_(track_die_mem_stack_12)    ( mc_die_mem_stack_12  );
   VG_(track_die_mem_stack_16)    ( mc_die_mem_stack_16  );
   VG_(track_die_mem_stack_32)    ( mc_die_mem_stack_32  );
   VG_(track_die_mem_stack_112)   ( mc_die_mem_stack_112 );
   VG_(track_die_mem_stack_128)   ( mc_die_mem_stack_128 );
   VG_(track_die_mem_stack_144)   ( mc_die_mem_stack_144 );
   VG_(track_die_mem_stack_160)   ( mc_die_mem_stack_160 );
#  endif
   VG_(track_die_mem_stack)       ( mc_die_mem_stack     );
   
   VG_(track_ban_mem_stack)       ( MC_(make_mem_noaccess) );

   VG_(track_pre_mem_read)        ( check_mem_is_defined );
   VG_(track_pre_mem_read_asciiz) ( check_mem_is_defined_asciiz );
   VG_(track_pre_mem_write)       ( check_mem_is_addressable );
   VG_(track_post_mem_write)      ( mc_post_mem_write );

   if (MC_(clo_mc_level) >= 2)
      VG_(track_pre_reg_read)     ( mc_pre_reg_read );

   VG_(track_post_reg_write)                  ( mc_post_reg_write );
   VG_(track_post_reg_write_clientcall_return)( mc_post_reg_write_clientcall );

   init_shadow_memory();
   MC_(malloc_list)  = VG_(HT_construct)( "MC_(malloc_list)" );
   MC_(mempool_list) = VG_(HT_construct)( "MC_(mempool_list)" );
   init_prof_mem();

   tl_assert( mc_expensive_sanity_check() );

   // {LOADV,STOREV}[8421] will all fail horribly if this isn't true.
   tl_assert(sizeof(UWord) == sizeof(Addr));
   // Call me paranoid.  I don't care.
   tl_assert(sizeof(void*) == sizeof(Addr));

   // BYTES_PER_SEC_VBIT_NODE must be a power of two.
   tl_assert(-1 != VG_(log2)(BYTES_PER_SEC_VBIT_NODE));

   /* This is small.  Always initialise it. */
   init_nia_to_ecu_cache();

   /* We can't initialise ocacheL1/ocacheL2 yet, since we don't know
      if we need to, since the command line args haven't been
      processed yet.  Hence defer it to mc_post_clo_init. */
   tl_assert(ocacheL1 == NULL);
   tl_assert(ocacheL2 == NULL);

   /* Check some important stuff.  See extensive comments above
      re UNALIGNED_OR_HIGH for background. */
#  if VG_WORDSIZE == 4
   tl_assert(sizeof(void*) == 4);
   tl_assert(sizeof(Addr)  == 4);
   tl_assert(sizeof(UWord) == 4);
   tl_assert(sizeof(Word)  == 4);
   tl_assert(MAX_PRIMARY_ADDRESS == 0xFFFFFFFFUL);
   tl_assert(MASK(1) == 0UL);
   tl_assert(MASK(2) == 1UL);
   tl_assert(MASK(4) == 3UL);
   tl_assert(MASK(8) == 7UL);
#  else
   tl_assert(VG_WORDSIZE == 8);
   tl_assert(sizeof(void*) == 8);
   tl_assert(sizeof(Addr)  == 8);
   tl_assert(sizeof(UWord) == 8);
   tl_assert(sizeof(Word)  == 8);
   tl_assert(MAX_PRIMARY_ADDRESS == 0x7FFFFFFFFULL);
   tl_assert(MASK(1) == 0xFFFFFFF800000000ULL);
   tl_assert(MASK(2) == 0xFFFFFFF800000001ULL);
   tl_assert(MASK(4) == 0xFFFFFFF800000003ULL);
   tl_assert(MASK(8) == 0xFFFFFFF800000007ULL);
#  endif
}

VG_DETERMINE_INTERFACE_VERSION(mc_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                mc_main.c ---*/
/*--------------------------------------------------------------------*/
