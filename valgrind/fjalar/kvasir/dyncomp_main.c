/*
   This file is part of DynComp, a dynamic comparability analysis tool
   for C/C++ based upon the Valgrind binary instrumentation framework
   and the Valgrind MemCheck tool.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/*--------------------------------------------------------------------*/
/*--- MemCheck: Maintain bitmaps of memory, tracking the           ---*/
/*--- accessibility (A) and validity (V) status of each byte.      ---*/
/*---                                                    mc_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is derived from MemCheck, a heavyweight Valgrind tool for
   detecting memory errors.

   Copyright (C) 2000-2013 Julian Seward 
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
*/

#include "../my_libc.h"

#include "kvasir_main.h"
#include "dyncomp_main.h"
#include "dyncomp_runtime.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_machine.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "mc_include.h"
#include "memcheck.h"

// Special reserved tags
#define MY_UINT_MAX 0xffffffffU
const UInt WEAK_FRESH_TAG   =  MY_UINT_MAX;
const UInt LARGEST_REAL_TAG = (MY_UINT_MAX - 1);

int print_merge = 1;

/* WEAK_FRESH_TAG unifies and replaces the previous special
   LITERAL_TAG and ESP_TAG values. When you merge it with a real tag,
   the real tag is the result (that's the weak part). When you store
   it to memory, a fresh tag is stored instead, and when you load it
   from memory, you get a fresh tag instead (those are the fresh
   part). This tag is used for the stack pointer, the frame pointer,
   the contents of the GOT, and literals when
   dyncomp-approximate-literals is enabled. */
/* The tag valued 0 is also special; if you wanted to give it a
   symbolic name, it would be something like "NO_TAG". It's even
   weaker than WEAK_FRESH_TAG, but otherwise propagates freely, and
   every instance of 0 turns into a fresh variable comparability type
   at the end. It's used for the result of comparisons, function
   return pointers, and the GOT table pointer, among other things. */

// For debug printouts
//extern char within_main_program;

/*------------------------------------------------------------------*/
/*--- Tags and the value comparability union-find data structure ---*/
/*------------------------------------------------------------------*/

// This is a serial number which increases every time a new tag
// The tag of 0 for a byte of memory means NO tag associated
// with it.  That's why nextTag starts at 1 and NOT 0.
// After garbage collection, this will hopefully decrease.
UInt nextTag = 1;

// The total number of tags that have ever been assigned throughout the
// duration of the program.  This is non-decreasing throughout the
// execution of the program
UInt totalNumTagsAssigned = 0;


/* The two-level tag map works almost like the memory map.  Its
   purpose is to implement a sparse array which can hold up to 2^32
   UInts.  The primary map holds 2^16 references to secondary maps.
   Each secondary map holds 2^16 UInt entries, each of which is 4
   bytes total.  Thus, each secondary map takes up 262,144 bytes.
   Each byte of memory should be shadowed with a corresponding tag.  A
   tag value of 0 means that there is NO tag associated with the byte.
*/
UInt* primary_tag_map[PRIMARY_SIZE];

// The number of entries in primary_tag_map that are initialized
// Range is [0, PRIMARY_SIZE]
UInt n_primary_tag_map_init_entries = 0;

UInt val_uf_tag_union(UInt tag1, UInt tag2);

// Copies tags of len bytes from src to dst
// Set both the tags of 'src' and 'dst' to their
// respective leaders for every byte
void copy_tags(  Addr src, Addr dst, SizeT len ) {
  SizeT i;
  for (i = 0; i < len; i++) {
    UInt leader = val_uf_find_leader(get_tag(src + i));
    set_tag (src + i, leader);
    set_tag (dst + i, leader);
  }
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
uf_object* primary_val_uf_object_map[PRIMARY_SIZE];

// The number of entries that are initialized in primary_val_uf_object_map
// Range is [0, PRIMARY_SIZE]
UInt n_primary_val_uf_object_map_init_entries = 0;

void val_uf_make_set_for_tag(UInt tag) {
  if (IS_ZERO_TAG(tag))
    return;

  if (IS_SECONDARY_UF_NULL(tag)) {
    uf_object* new_uf_obj_array =
      (uf_object*)VG_(am_shadow_alloc)(SECONDARY_SIZE * sizeof(*new_uf_obj_array));

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
    //      //      printf("      uf_make_set(%u, %u);\n",
    //      //                  new_uf_obj_array + i, curTag);
    //    }
    primary_val_uf_object_map[PM_IDX(tag)] = new_uf_obj_array;
    n_primary_val_uf_object_map_init_entries++;

  }

  // Do this unconditionally now:
  uf_make_set(GET_UF_OBJECT_PTR(tag), tag);
}

// Merge the sets of tag1 and tag2 and return the leader
UInt val_uf_tag_union(UInt tag1, UInt tag2) {
  if (!IS_ZERO_TAG(tag1) && !IS_SECONDARY_UF_NULL(tag1) &&
      !IS_ZERO_TAG(tag2) && !IS_SECONDARY_UF_NULL(tag2)) {
    Addr eip = VG_(get_IP)(VG_(get_running_tid)());
    const HChar *eip_info;
    uf_object* tag1_obj, *tag2_obj;
    uf_object* leader;
    tag1_obj = GET_UF_OBJECT_PTR(tag1);
    tag2_obj = GET_UF_OBJECT_PTR(tag2);
    leader = uf_union(tag1_obj, tag2_obj);
    // Describe this (probably live) address with current epoch
    eip_info = VG_(describe_IP)(VG_(current_DiEpoch)(), eip, NULL);

    DYNCOMP_TPRINTF("[DynComp-v1] Merging %u with %u to get %u at %s\n",
                    tag1, tag2, leader->tag, eip_info);

    return leader->tag;
  }
  else {
    return 0;
  }
}

// Write tag into all addresses in the range [a, a+len)
static __inline__ void set_tag_for_range(Addr a, SizeT len, UInt tag) {
  Addr curAddr;
  UInt leader = val_uf_find_leader(tag);

  for (curAddr = a; curAddr < (a+len); curAddr++) {
    set_tag(curAddr, leader);
  }
}

// Write the special GOT tag into all addresses in the range [a, a+len)
void set_tag_for_GOT(Addr a, SizeT len) {
  Addr curAddr;
  for (curAddr = a; curAddr < (a+len); curAddr++) {
    set_tag(curAddr, WEAK_FRESH_TAG);
  }
}

// Helper functions called from dyncomp_translate.c:

// Only used for 'anchoring' the IR tree branch generated by Mux and
// conditional exit expressions so that the optimizer doesn't delete
// them
VG_REGPARM(1)
UInt MC_(helperc_TAG_NOP) ( UInt tag ) {
   DYNCOMP_TPRINTF("[DynComp] TAG_NOP: %u \n", tag);
   return tag;
}

// When we're requesting to store tags for X bytes,
// we will write the tag into all X bytes.

// When dyncomp_approximate_literals is on, check whether
// the tag to be stored is WEAK_FRESH_TAG.  If it is, create
// a new tag and store that in memory instead of WEAK_FRESH_TAG.
// (We don't need to do a check for dyncomp_approximate_literals
// because WEAK_FRESH_TAG should never be used for regular real tags
// regardless of whether dyncomp_approximate_literals is on or not.
// Real tags are in the range of [1, LARGEST_REAL_TAG])

// For some reason, 64-bit stuff needs REGPARM(1) (Look in
// mc_translate.c) - this is very important for some reason
VG_REGPARM(1)
void MC_(helperc_STORE_TAG_8) ( Addr a, UInt tag ) {
  UInt tagToWrite;

  if (WEAK_FRESH_TAG == tag) {
    tagToWrite = grab_fresh_tag();
  }
  else {
    tagToWrite = tag;
  }

  set_tag_for_range(a, 8, tagToWrite);
}

VG_REGPARM(2)
void MC_(helperc_STORE_TAG_4) ( Addr a, UInt tag ) {
  UInt tagToWrite;


  if (WEAK_FRESH_TAG == tag) {
    tagToWrite = grab_fresh_tag();
  }
  else {
    tagToWrite = tag;
  }

  set_tag_for_range(a, 4, tagToWrite);
}

VG_REGPARM(2)
void MC_(helperc_STORE_TAG_2) ( Addr a, UInt tag ) {
  UInt tagToWrite;

  if (WEAK_FRESH_TAG == tag) {
    tagToWrite = grab_fresh_tag();
  }
  else {
    tagToWrite = tag;
  }

  set_tag_for_range(a, 2, tagToWrite);
}

VG_REGPARM(2)
void MC_(helperc_STORE_TAG_1) ( Addr a, UInt tag ) {
  UInt tagToWrite;

  if (WEAK_FRESH_TAG == tag) {
    tagToWrite = grab_fresh_tag();
  }
  else {
    tagToWrite = tag;
  }

  set_tag(a, tagToWrite);
}

// Unions the tags belonging to these addresses and set
// the tags of both to the canonical tag (for efficiency)
void val_uf_union_tags_at_addr(Addr a1, Addr a2) {
  UInt canonicalTag;
  UInt tag1 = get_tag(a1);
  UInt tag2 = get_tag(a2);
  print_merge = 0;
  //  printf("val_uf_union_tags_at_addr(0x%x, 0x%x) canonicalTag\n",
  //              a1, a2);
  if ((0 == tag1) ||
      (0 == tag2) ||
      (tag1 == tag2)) {
    print_merge = 1;
    return;
  }

  canonicalTag = val_uf_tag_union(tag1, tag2);

  set_tag(a1, canonicalTag);
  set_tag(a2, canonicalTag);
  //(printf)("val_uf_union_tags_at_addr(0x%x, 0x%x) canonicalTag=%u\n",
  //              a1, a2, canonicalTag);

  print_merge = 1;
  DYNCOMP_TPRINTF("[DynComp] val_uf_union_tags_at_addr(%p, %p) canonicalTag=%u\n",
                  (void *)a1, (void *)a2, canonicalTag);
  }

  // Union the tags of all addresses in the range [a, a+max)
// and sets them all equal to the canonical tag of the merged set
// (An optimization which could help out with garbage collection
//  because we want to have as few tags 'in play' at one time
//  as possible)
// Returns the canonical tag of the merged set as the result
UInt val_uf_union_tags_in_range(Addr a, SizeT len) {
  Addr curAddr;
  UInt canonicalTag = 0;
  UInt tagToMerge = 0;
  UInt curTag;
  print_merge = 0;

  // If dyncomp_approximate_literals is on, then if all of the tags
  // in range are WEAK_FRESH_TAG, then create a new tag and copy
  // it into all of those locations
  // (This is currently turned off because it loses too much precision)
/*   if (dyncomp_approximate_literals) { */
/*     char allLiteralTags = 1; */
/*     for (curAddr = a; curAddr < (a + len); curAddr++) { */
/*       if (get_tag(curAddr) != WEAK_FRESH_TAG) { */
/*         allLiteralTags = 0; */
/*         break; */
/*       } */
/*     } */

/*     if (allLiteralTags) { */
/*       UInt freshTag = grab_fresh_tag(); */
/*       //      printf("val_uf_union_tags_in_range(%u, %u) saw WEAK_FRESH_TAG & created tag %u\n", */
/*       //                  a, len, freshTag); */
/*       set_tag_for_range(a, len, freshTag); */
/*       return freshTag; // Ok, we're done now */
/*     } */
/*   } */

  // Scan the range for the first non-zero tag and use
  // that as the basis for all the mergings:
  // (Hopefully this should only take one iteration
  //  because the tag of address 'a' should be non-zero)
  for (curAddr = a; curAddr < (a + len); curAddr++) {
    curTag = get_tag(curAddr);
    if (curTag) {
DYNCOMP_TPRINTF("MLR debug val_uf_union_tags_in_range addr=%p, tag=%u\n", (void *)curAddr, curTag);
      tagToMerge = curTag;
      break;
    }
  }

  // If they are all zeroes, then we're done;
  // Don't merge anything
  if (0 == tagToMerge) {
    print_merge = 1;
    return 0;
  }
  // Otherwise, merge all the stuff and set them to canonical:
  else {
    for (curAddr = a; curAddr < (a + len); curAddr++) {
      curTag = get_tag(curAddr);
      if (tagToMerge != curTag) {
        val_uf_tag_union(tagToMerge, curTag);
      }
    }
    // Find out the canonical tag
    canonicalTag = val_uf_find_leader(tagToMerge);

    DYNCOMP_TPRINTF("[DynComp] (above) val_uf_union_tags_in_range(%p, %p) canonicalTag=%u\n",
                  (void *)a, (void *)(a+len), canonicalTag);

    // Set all the tags in this range to the canonical tag
    for (curAddr = a; curAddr < (a + len); curAddr++) {
      set_tag(curAddr, canonicalTag);
    }

    print_merge = 1;
    return canonicalTag;
  }
}

// Create a new tag but don't put it anywhere in memory ... just return it
// This is to handle literals in the code.  If somebody actually wants
// to use this literal, then it will get assigned somewhere ... otherwise
// there is no record of it anywhere in memory so that it can get
// garbage-collected.
VG_REGPARM(1)
UInt MC_(helperc_CREATE_TAG)(Addr static_id) {
  DYNCOMP_TPRINTF("[DynComp] CREATE_TAG: %p =>\n", (void *)static_id);
  UInt newTag = grab_fresh_tag();
  (void)static_id;
  return newTag;
}


VG_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_8) ( Addr a ) {
  DYNCOMP_TPRINTF("[DynComp] LOAD_TAG_8: %p\n", (void *)a);
  return val_uf_union_tags_in_range(a, 8);
}

VG_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_4) ( Addr a ) {
  UInt first_tag = get_tag(a);
  if (first_tag == WEAK_FRESH_TAG) {
    DYNCOMP_TPRINTF("[DynComp] helperx_LOAD_ATG_4: %p =>\n", (void *)a);
    return grab_fresh_tag();
  }
  DYNCOMP_TPRINTF("[DynComp] LOAD_TAG_4: %p\n", (void *)a);
  return val_uf_union_tags_in_range(a, 4);
}

VG_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_2) ( Addr a ) {
  DYNCOMP_TPRINTF("[DynComp] LOAD_TAG_2: %p\n", (void *)a);
  return val_uf_union_tags_in_range(a, 2);
}

VG_REGPARM(1)
UInt MC_(helperc_LOAD_TAG_1) ( Addr a ) {
  DYNCOMP_TPRINTF("[DynComp] LOAD_TAG_1: %p => %u\n", (void *)a, get_tag(a));
  return val_uf_union_tags_in_range(a, 1);
}

// Make this const so gcc can eliminate dead code to improve
// performance:
const int dyncomp_profile_tags = 0;

UInt mergeTagsCount = 0;
UInt merge3TagsCount = 0;
UInt merge4TagsCount = 0;
UInt mergeTagsReturn0Count = 0;

VG_REGPARM(2)
UInt tag1_is_new ( UInt tag1, UInt tag2 ) {
  if IS_ZERO_TAG(tag2) {
    return tag1;
  }
  else {
    return tag2;
  }
}

VG_REGPARM(2)
UInt tag2_is_new ( UInt tag1, UInt tag2 ) {
  if IS_ZERO_TAG(tag1) {
    return tag2;
  }
  else {
    return tag1;
  }
}

// Merge tags during any binary operation which
// qualifies as an interaction and returns the leader
// of the merged set
VG_REGPARM(2)
UInt MC_(helperc_MERGE_TAGS) ( UInt tag1, UInt tag2 ) {
  Addr eip = VG_(get_IP)(VG_(get_running_tid)());
  const HChar *eip_info;
  // Describe this (probably live) address with current epoch
  eip_info = VG_(describe_IP)(VG_(current_DiEpoch)(), eip, NULL);

  if (dyncomp_profile_tags) {
    mergeTagsCount++;
  }

  // Important special case - if one of the tags is 0, then
  // simply return the OTHER tag and don't do any merging.
  if IS_ZERO_TAG(tag1) {
    return tag2;
  }
  else if IS_ZERO_TAG(tag2) {
    return tag1;
  }
  // If either tag is WEAK_FRESH_TAG, return the other one.
  // (If both are WEAK_FRESH_TAG's, then return WEAK_FRESH_TAG,
  //  but that's correctly handled)
  else if (WEAK_FRESH_TAG == tag1) {
    DYNCOMP_TPRINTF("[DynComp-m1] Merging %u with %u to get %u at %s\n",
                    tag1, tag2, tag2, eip_info);
    return tag2;
  }
  else if (WEAK_FRESH_TAG == tag2) {
    DYNCOMP_TPRINTF("[DynComp-m2] Merging %u with %u to get %u at %s\n",
                    tag1, tag2, tag1, eip_info);
    return tag1;
  }
  else {
    DYNCOMP_TPRINTF("[DynComp-m3] Calling val_uf_tag_union\n");
    return val_uf_tag_union(tag1, tag2);
  }
}

// We can make this more efficient, but correctness is more important
// right now (as it should be!):
VG_REGPARM(3)
UInt MC_(helperc_MERGE_3_TAGS) (UInt tag1, UInt tag2, UInt tag3) {
  if (dyncomp_profile_tags) {
    merge3TagsCount++;
  }

  return MC_(helperc_MERGE_TAGS)(MC_(helperc_MERGE_TAGS)(tag1, tag2),
                                 tag3);
}

// Uhhh, I can't do VG_REGPARM(4) :(
VG_REGPARM(3)
UInt MC_(helperc_MERGE_4_TAGS) (UInt tag1, UInt tag2, UInt tag3, UInt tag4) {
  if (dyncomp_profile_tags) {
    merge4TagsCount++;
  }

  return MC_(helperc_MERGE_TAGS)(MC_(helperc_MERGE_TAGS)(tag1, tag2),
                                 MC_(helperc_MERGE_TAGS)(tag3, tag4));
}


// Merge tags but return a value of 0.  This simulate interaction of
// the two parameters but not passing along the tag to the result (the
// intended behavior for comparisons, for example).
VG_REGPARM(2)
UInt MC_(helperc_MERGE_TAGS_RETURN_0) ( UInt tag1, UInt tag2 ) {
  if (dyncomp_profile_tags) {
    mergeTagsReturn0Count++;
  }

  // (comment added 2006)  
  // TODO: What do we do about WEAK_FRESH_TAG???

  if (IS_ZERO_TAG(tag1) ||
      IS_ZERO_TAG(tag2)) {
    return 0;
  }
  else {
    DYNCOMP_TPRINTF("[DynComp-m4] Calling val_uf_tag_union but return 0\n");
    val_uf_tag_union(tag1, tag2);
    return 0;
  }
}

/*------------------------------------------------------------------*/
/*--- Linked-lists of tags for garbage collection                ---*/
/*------------------------------------------------------------------*/

// (This is currently not used right now)

// Adds a new tag to the tail of the list
// Pre: (tag != 0)
void enqueue_tag(TagList* listPtr, UInt tag) {
  tl_assert(tag);

  // Special case for no elements
  if (listPtr->numElts == 0) {
    listPtr->first = listPtr->last =
      (TagNode*)VG_(calloc)("dyncomp_main.c: enqueue_tag", 1, sizeof(TagNode));
  }
  else {
    listPtr->last->next = (TagNode*)VG_(calloc)("dyncomp_main.c: enqueue_tag.2", 1, sizeof(TagNode));
    listPtr->last = listPtr->last->next;
  }

  listPtr->last->tag = tag;
  listPtr->numElts++;
}

// Removes and returns tag from head of the list
// Pre: listPtr->numElts > 0
UInt dequeue_tag(TagList* listPtr) {
  UInt retTag = 0;
  TagNode* nodeToKill;

  tl_assert(listPtr->numElts > 0);

  nodeToKill = listPtr->first;

  retTag = listPtr->first->tag;

  listPtr->first = listPtr->first->next;
  VG_(free)(nodeToKill);
  listPtr->numElts--;

  // Special case for no elements
  if (listPtr->numElts == 0) {
    listPtr->last = listPtr->first = NULL;
  }

  return retTag;
}

// Returns 1 if the tag is found in the list, 0 otherwise
// Only searches through the first n elts in *listPtr
// Pre: (tag != 0)
char is_tag_in_list(TagList* listPtr, UInt tag, UInt n) {
  UInt count = 0;

  tl_assert(tag);

  if (listPtr->numElts == 0) {
    return 0;
  }
  else {
    TagNode* i;
    for (i = listPtr->first;
         (i != NULL) && (count < n);
         i = i->next, count++) {
      if (i->tag == tag) {
        return 1;
      }
    }

    return 0;
  }
}

void clear_list(TagList* listPtr) {
  if (listPtr->numElts > 0) {
    TagNode* i = listPtr->first;
    TagNode* next = i->next;
    for (i = listPtr->first; i != NULL; i = next) {
      next = i->next;
      VG_(free)(i);
      listPtr->numElts--;
    }
  }

  tl_assert(listPtr->numElts == 0);
}
