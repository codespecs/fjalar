
/*--------------------------------------------------------------------*/
/*--- The main DynComp file (analogous to mc_main.c)               ---*/
/*---                                               dyncomp_main.c ---*/
/*--------------------------------------------------------------------*/

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

  Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

#include "mc_include.h"
#include "dyncomp_main.h"
#include <limits.h>
#include "union_find.h"

//#define DYNCOMP_DEBUG
//#define CREATE_TAG_VERBOSE
//#define STORE_TAG_VERBOSE
//#define LOAD_TAG_VERBOSE
//#define MERGE_TAGS_VERBOSE

/*------------------------------------------------------------------*/
/*--- Tags and the value comparability union-find data structure ---*/
/*------------------------------------------------------------------*/

// This is a serial number which increases every time a new tag
// is assigned in order to ensure that all tags are unique.
// (More sophisticated machinery is needed later when we add
//  garbage collection of tags.)
// The tag of 0 for a byte of memory means NO tag associated
// with it.  That's why nextTag starts at 1 and NOT 0.
UInt nextTag = 1;

// Prototypes:
static void val_uf_make_set_for_tag(UInt tag);

/* The two-level tag map works almost like the memory map.  Its
   purpose is to implement a sparse array which can hold up to 2^32
   UInts.  The primary map holds 2^16 references to secondary maps.
   Each secondary map holds 2^16 UInt entries, each of which is 4
   bytes total.  Thus, each secondary map takes up 262,144 bytes.
   Each byte of memory should be shadowed with a corresponding tag.  A
   tag value of 0 means that there is NO tag associated with the byte.
*/
static UInt* primary_tag_map[PRIMARY_SIZE];

#define IS_SECONDARY_TAG_MAP_NULL(a) (primary_tag_map[PM_IDX(a)] == NULL)

__inline__ UInt get_tag ( Addr a )
{
  if (IS_SECONDARY_TAG_MAP_NULL(a))
    return 0; // 0 means NO tag for that byte
  else
    return primary_tag_map[PM_IDX(a)][SM_OFF(a)];
}

__inline__ void set_tag ( Addr a, UInt tag )
{
  if (IS_SECONDARY_TAG_MAP_NULL(a)) {
    UInt* new_tag_array =
      (UInt*)VG_(shadow_alloc)(SECONDARY_SIZE * sizeof(*new_tag_array));
    VG_(memset)(new_tag_array, 0, (SECONDARY_SIZE * sizeof(*new_tag_array)));
    primary_tag_map[PM_IDX(a)] = new_tag_array;
  }
  primary_tag_map[PM_IDX(a)][SM_OFF(a)] = tag;
}

// Sets tag of address 'a' to a fresh tag and initialize a new uf_object
// (This will have to be modified when we implement garbage collection)
static __inline__ void assign_new_tag(Addr a) {
  set_tag(a, nextTag);
  val_uf_make_set_for_tag(nextTag);
  if (nextTag == UINT_MAX) {
    VG_(printf)("Error! Maximum tag has been used. We need garbage collection of tags!\n");
  }
  else {
    nextTag++;
  }
}

// Doesn't do set_tag(); instead, return the new tag
static __inline__ UInt assign_new_tag_no_addr() {
  UInt newTag = nextTag;
  val_uf_make_set_for_tag(newTag);
  if (nextTag == UINT_MAX) {
    VG_(printf)("Error! Maximum tag has been used. We need garbage collection of tags!\n");
  }
  else {
    nextTag++;
  }

  return newTag;
}


// Allocate a new unique tag for all bytes in range [a, a + len)
__inline__ void allocate_new_unique_tags ( Addr a, SizeT len ) {
  Addr curAddr;
  for (curAddr = a; curAddr < (a+len); curAddr++) {
    assign_new_tag(curAddr);
  }

#ifdef DYNCOMP_DEBUG
  VG_(printf)("After allocate_new_unique_tags(a=0x%x, len=%d): nextTag=%u\n",
              a, len, nextTag);
#endif
}

// Clear all tags for all bytes in range [a, a + len)
// TODO: We need to do something with their corresponding
// uf_objects in order to prepare them for garbage collection
// (when it's implemented)
__inline__ void clear_all_tags_in_range( Addr a, SizeT len ) {
  Addr curAddr;
  for (curAddr = a; curAddr < (a+len); curAddr++) {
    set_tag(curAddr, 0);
    // TODO: Do something with uf_objects (maybe put them on a to-be-freed
    // list) to prepare them for garbage collection
  }

#ifdef DYNCOMP_DEBUG
  VG_(printf)("After clear_all_tags_in_range(a=0x%x, len=%d): nextTag=%u\n",
              a, len, nextTag);
#endif
}

// Copies tags of len bytes from src to dst
__inline__ void copy_tags(  Addr src, Addr dst, SizeT len ) {
   SizeT i;

   for (i = 0; i < len; i++) {
      UInt tag  = get_tag ( src+i );
      set_tag ( dst+i, tag );
   }

#ifdef DYNCOMP_DEBUG
  VG_(printf)("After copy_tags(src=0x%x, dst=0x%x, len=%d): nextTag=%u\n",
              src, dst, len, nextTag);
#endif
}

/* The two-level value uf_object map works almost like the memory map.
   Its purpose is to implement a sparse array which can hold
   up to 2^32 uf_object entries.  The primary map holds 2^16
   references to secondary maps.  Each secondary map holds 2^16
   uf_object entries, each of which is 12 bytes total.  Thus,
   each secondary map takes up 786,432 bytes.
   The main difference between this sparse array structure and
   the tag map is that this one fills up sequentially from
   lower indices to higher indices because tags are assigned
   (more or less) sequentially using nextTag and tag serial
   numbers are used as indices into the uf_object map
*/

// val_uf_object_map: A map from tag (32-bit int) to uf_objects
// Each entry either points to NULL or to a dynamically-allocated
// array (of size SECONDARY_SIZE) of uf_object objects
static uf_object* primary_val_uf_object_map[PRIMARY_SIZE];

#define IS_SECONDARY_UF_NULL(tag) (primary_val_uf_object_map[PM_IDX(tag)] == NULL)

// Make sure to check that !IS_SECONDARY_UF_NULL(tag) before
// calling this macro or else you may segfault
#define GET_UF_OBJECT_PTR(tag) (&(primary_val_uf_object_map[PM_IDX(tag)][SM_OFF(tag)]))

static void val_uf_make_set_for_tag(UInt tag) {
  //  VG_(printf)("val_uf_make_set_for_tag(%u);\n", tag);

  if (IS_ZERO_TAG(tag))
    return;

  if (IS_SECONDARY_UF_NULL(tag)) {
    uf_object* new_uf_obj_array =
      (uf_object*)VG_(shadow_alloc)(SECONDARY_SIZE * sizeof(*new_uf_obj_array));

    // PG - We can skip this step and leave them uninitialized
    //      until somebody explicitly calls val_uf_make_set_for_tag() on
    //      that particular tag

    // Each new uf_object should be initialized using uf_make_set()
    //    UInt i;
    //    UInt curTag; // Set to upper 16-bits of the tag
    //    for (i = 0, curTag = ((PM_IDX(tag)) << SECONDARY_SHIFT);
    //         i < SECONDARY_SIZE;
    //         i++, curTag++) {
    //      uf_make_set(new_uf_obj_array + i, curTag);
    //      //      VG_(printf)("      uf_make_set(%u, %u);\n",
    //      //                  new_uf_obj_array + i, curTag);
    //    }
    primary_val_uf_object_map[PM_IDX(tag)] = new_uf_obj_array;
  }
  //  else {
  //    uf_make_set(GET_UF_OBJECT_PTR(tag), tag);
  //  }

  // Do this unconditionally now:
  uf_make_set(GET_UF_OBJECT_PTR(tag), tag);
}

static __inline__ void val_uf_tag_union(UInt tag1, UInt tag2) {
  if (!IS_ZERO_TAG(tag1) && !IS_SECONDARY_UF_NULL(tag1) &&
      !IS_ZERO_TAG(tag2) && !IS_SECONDARY_UF_NULL(tag2)) {
        uf_union(GET_UF_OBJECT_PTR(tag1),
                 GET_UF_OBJECT_PTR(tag2));
  }
}

static  __inline__ uf_name val_uf_tag_find(UInt tag) {
  if (IS_ZERO_TAG(tag) || IS_SECONDARY_UF_NULL(tag)) {
    return NULL;
  }
  else {
    return uf_find(GET_UF_OBJECT_PTR(tag));
  }
}

// Be careful not to bust a false positive by naively
// comparing val_uf_tag_find(tag1) and val_uf_tag_find(tag2)
// because you could be comparing 0 == 0 if both satisfy
// IS_SECONDARY_UF_NULL
static UChar val_uf_tags_in_same_set(UInt tag1, UInt tag2) {
  if (!IS_ZERO_TAG(tag1) && !IS_SECONDARY_UF_NULL(tag1) &&
      !IS_ZERO_TAG(tag2) && !IS_SECONDARY_UF_NULL(tag2)) {
    return (val_uf_tag_find(tag1) == val_uf_tag_find(tag2));
  }
  else {
    return 0;
  }
}

// Helper functions called from mc_translate.c:

// Write tag into all addresses in the range [a, a+len)
static __inline__ void set_tag_for_range(Addr a, SizeT len, UInt tag) {
  Addr curAddr;
  for (curAddr = a; curAddr < (a+len); curAddr++) {
    set_tag(curAddr, tag);
  }
}

// Only used for 'anchoring' the IR tree branch generated by Mux and
// conditional exit expressions so that the optimizer doesn't delete
// them
VGA_REGPARM(1)
UInt MC_(helperc_TAG_NOP) ( UInt tag ) {
   return tag;
}

// When we're requesting to store tags for X bytes,
// we will write the tag into all X bytes.
// We don't do a val_uf_make_set_for_tag for the tag we have just
// written because we assume that it has been initialized
// somewhere else (is that a safe assumption???)

// For some reason, 64-bit stuff needs REGPARM(1)
// (Look in mc_translate.c)
VGA_REGPARM(1)
void MC_(helperc_STORE_TAG_8) ( Addr a, UInt tag ) {
  set_tag_for_range(a, 8, tag);
#ifdef STORE_TAG_VERBOSE
  VG_(printf)("helperc_STORE_TAG_8(0x%x, %u) [nextTag=%u]\n",
              a, tag, nextTag);
#endif
}

VGA_REGPARM(2)
void MC_(helperc_STORE_TAG_4) ( Addr a, UInt tag ) {
  set_tag_for_range(a, 4, tag);
#ifdef STORE_TAG_VERBOSE
  VG_(printf)("helperc_STORE_TAG_4(0x%x, %u) [nextTag=%u]\n",
              a, tag, nextTag);
#endif
}

VGA_REGPARM(2)
void MC_(helperc_STORE_TAG_2) ( Addr a, UInt tag ) {
  set_tag_for_range(a, 2, tag);
#ifdef STORE_TAG_VERBOSE
  VG_(printf)("helperc_STORE_TAG_2(0x%x, %u) [nextTag=%u]\n",
              a, tag, nextTag);
#endif
}

VGA_REGPARM(2)
void MC_(helperc_STORE_TAG_1) ( Addr a, UInt tag ) {
  set_tag_for_range(a, 1, tag);
#ifdef STORE_TAG_VERBOSE
  VG_(printf)("helperc_STORE_TAG_1(0x%x, %u) [nextTag=%u]\n",
              a, tag, nextTag);
#endif
}

// Return the leader (canonical tag) of the set which 'tag' belongs to
__inline__ UInt val_uf_find_leader(UInt tag) {
  uf_name canonical = val_uf_tag_find(tag);
  if (canonical) {
    return canonical->tag;
  }
  else {
    return 0;
  }
}

// Unions the tags belonging to these addresses and set
// the tags of both to the canonical tag (for efficiency)
__inline__ void val_uf_union_tags_at_addr(Addr a1, Addr a2) {
  UInt canonicalTag;
  UInt tag1 = get_tag(a1);

  val_uf_tag_union(tag1, get_tag(a2));

  canonicalTag = val_uf_find_leader(tag1);
  set_tag(a1, canonicalTag);
  set_tag(a2, canonicalTag);
}

// Union the tags of all addresses in the range [a, a+max)
// and sets them all equal to the canonical tag of the merged set
// (An optimization which could help out with garbage collection
//  because we want to have as few tags 'in play' at one time
//  as possible)
void val_uf_union_tags_in_range(Addr a, SizeT len) {
  Addr curAddr;
  UInt aTag = get_tag(a);
  UInt canonicalTag;

  for (curAddr = (a + 1); curAddr < (a + len); curAddr++) {
    val_uf_tag_union(aTag, get_tag(curAddr));
  }

  // Find out the canonical tag
  canonicalTag = val_uf_find_leader(aTag);
  if (canonicalTag > 0) {
    // Set all the tags in this range to the canonical tag
    // (as inferred from a reverse map lookup)
    for (curAddr = a; curAddr < (a + len); curAddr++) {
      set_tag(curAddr, canonicalTag);
    }
  }
}

// Create a new tag but don't put it anywhere
VGA_REGPARM(0)
UInt MC_(helperc_CREATE_TAG) () {
  UInt newTag = assign_new_tag_no_addr();
#ifdef CREATE_TAG_VERBOSE
  VG_(printf)("helperc_CREATE_TAG() = %u [nextTag=%u]\n",
              newTag, nextTag);
#endif
  return newTag;
}

// Whenever we're requesting to load tags for X bytes,
// we merge the tags for those X bytes and return the tag
// of the first byte.  This may potentially lose details
// but is much easier to implement.
VGA_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_8) ( Addr a ) {
  val_uf_union_tags_in_range(a, 8);
#ifdef LOAD_TAG_VERBOSE
  VG_(printf)("helperc_LOAD_TAG_8(0x%x) = %u [nextTag=%u]\n",
              a, get_tag(a), nextTag);
#endif
  return get_tag(a);
}

VGA_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_4) ( Addr a ) {
  val_uf_union_tags_in_range(a, 4);
#ifdef LOAD_TAG_VERBOSE
  VG_(printf)("helperc_LOAD_TAG_4(0x%x) = %u [nextTag=%u]\n",
              a, get_tag(a), nextTag);
#endif
  return get_tag(a);
}

VGA_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_2) ( Addr a ) {
  val_uf_union_tags_in_range(a, 2);
#ifdef LOAD_TAG_VERBOSE
  VG_(printf)("helperc_LOAD_TAG_2(0x%x) = %u  [nextTag=%u]\n",
              a, get_tag(a), nextTag);
#endif
  return get_tag(a);
}

VGA_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_1) ( Addr a ) {
#ifdef LOAD_TAG_VERBOSE
  VG_(printf)("helperc_LOAD_TAG_1(0x%x) = %u [nextTag=%u]\n",
              a, get_tag(a), nextTag);
#endif
  return get_tag(a);
}


// Merge tags during any binary operation which
// qualifies as an interaction and returns the first tag
VGA_REGPARM(2)
UInt MC_(helperc_MERGE_TAGS) ( UInt tag1, UInt tag2 ) {
  val_uf_tag_union(tag1, tag2);
#ifdef MERGE_TAGS_VERBOSE
  VG_(printf)("helperc_MERGE_TAGS(%u, %u) [nextTag=%u]\n",
              tag1, tag2, nextTag);
#endif
  return tag1;
}
