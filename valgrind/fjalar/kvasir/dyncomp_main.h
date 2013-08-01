/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

#ifndef DYNCOMP_MAIN_H
#define DYNCOMP_MAIN_H

//#include "tool.h"
#include "pub_tool_aspacemgr.h"
#include "pub_tool_libcassert.h"

//RUDD-REMOVE
//#include "../mac_shared.h"
#include "../mc_translate.h"
#include "../mc_include.h"
#include "union_find.h"

//RUDD-MERGE, no longer in memcheck

#if VG_WORDSIZE == 4
#define SECONDARY_SHIFT	16
#define SECONDARY_SIZE 65536               /* DO NOT CHANGE */
#define PRIMARY_SIZE	(1 << (32 - SECONDARY_SHIFT))
#else
/* This supports address space sizes up to 2**40 = 1TB, which happens to
   also be the maximum amount of physical RAM supported by current
   x86-64 processors. It would be nice to support 2**48 (the current
   address-space limit) or 2**64 (the architectural limit), but those
   would require a redesign of the table structure to have more levels
   or a different kind of top level (like Memcheck). */
#define SECONDARY_SHIFT	20
#define SECONDARY_SIZE 1048576
#define PRIMARY_SIZE	(1 << (40 - SECONDARY_SHIFT))
#endif

#define SECONDARY_MASK (SECONDARY_SIZE-1)  /* DO NOT CHANGE */

#define SM_OFF(addr)	((addr) & SECONDARY_MASK)
#define PM_IDX(addr)	((addr) >> SECONDARY_SHIFT)


// Special reserved tags
const UInt WEAK_FRESH_TAG;
const UInt LARGEST_REAL_TAG;

UInt nextTag;

// The total number of tags that have ever been assigned throughout the
// duration of the program
UInt totalNumTagsAssigned;

UInt* primary_tag_map[PRIMARY_SIZE];

// The number of entries in primary_tag_map that are initialized
// Range is [0, PRIMARY_SIZE]
UInt n_primary_tag_map_init_entries;

uf_object* primary_val_uf_object_map[PRIMARY_SIZE];

// The number of entries that are initialized in
// primary_val_uf_object_map
// Range is [0, PRIMARY_SIZE]
UInt n_primary_val_uf_object_map_init_entries;


#define IS_SECONDARY_UF_NULL(tag) (primary_val_uf_object_map[PM_IDX(tag)] == NULL)

// Make sure to check that !IS_SECONDARY_UF_NULL(tag) before
// calling this macro or else you may segfault
#define GET_UF_OBJECT_PTR(tag) (&(primary_val_uf_object_map[PM_IDX(tag)][SM_OFF(tag)]))


// Defines a singly-linked list of 32-bit UInt tags
typedef struct _TagNode TagNode;

struct _TagNode {
  UInt tag;
  TagNode* next;
};

typedef struct {
  TagNode* first;
  TagNode* last;
  UInt numElts;
} TagList;

void enqueue_tag(TagList* listPtr, UInt tag);
char enqueue_unique_tag(TagList* listPtr, UInt tag);
UInt dequeue_tag(TagList* listPtr);
char is_tag_in_list(TagList* listPtr, UInt tag, UInt n);
void clear_list(TagList* listPtr);

// Don't do anything with tags equal to 0 because they are invalid
#define IS_ZERO_TAG(tag) (0 == tag)

__inline__ void clear_all_tags_in_range( Addr a, SizeT len );
__inline__ void allocate_new_unique_tags ( Addr a, SizeT len );
void copy_tags(  Addr src, Addr dst, SizeT len );

__inline__ UInt get_tag ( Addr a );
__inline__ void set_tag ( Addr a, UInt tag );

UInt val_uf_union_tags_in_range(Addr a, SizeT len);
void val_uf_union_tags_at_addr(Addr a1, Addr a2);
__inline__ UInt val_uf_find_leader(UInt tag);

void val_uf_make_set_for_tag(UInt tag);

void set_tag_for_GOT(Addr a, SizeT len);

extern VG_REGPARM(1) UInt MC_(helperc_TAG_NOP) ( UInt );

// Remember the special REGPARM(1) for the 64-bit case
// (still dunno why I need it, but it's necessary)
extern VG_REGPARM(1) void MC_(helperc_STORE_TAG_8) ( Addr, UInt );
extern VG_REGPARM(2) void MC_(helperc_STORE_TAG_4) ( Addr, UInt );
extern VG_REGPARM(2) void MC_(helperc_STORE_TAG_2) ( Addr, UInt );
extern VG_REGPARM(2) void MC_(helperc_STORE_TAG_1) ( Addr, UInt );

extern VG_REGPARM(1) UInt MC_(helperc_LOAD_TAG_8) ( Addr );
extern VG_REGPARM(1) UInt MC_(helperc_LOAD_TAG_4) ( Addr );
extern VG_REGPARM(1) UInt MC_(helperc_LOAD_TAG_2) ( Addr );
extern VG_REGPARM(1) UInt MC_(helperc_LOAD_TAG_1) ( Addr );

extern VG_REGPARM(1) UInt MC_(helperc_CREATE_TAG) ( Addr static_id );

extern VG_REGPARM(2) UInt MC_(helperc_MERGE_TAGS) ( UInt, UInt );
extern VG_REGPARM(2) UInt MC_(helperc_MERGE_TAGS_RETURN_0) ( UInt, UInt );

extern VG_REGPARM(3) UInt MC_(helperc_MERGE_3_TAGS) ( UInt, UInt, UInt );
extern VG_REGPARM(3) UInt MC_(helperc_MERGE_4_TAGS) ( UInt, UInt, UInt, UInt );

extern VG_REGPARM(2) UInt tag1_is_new ( UInt, UInt );
extern VG_REGPARM(2) UInt tag2_is_new ( UInt, UInt );

#endif
