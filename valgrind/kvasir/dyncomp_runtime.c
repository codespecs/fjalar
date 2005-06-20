// dyncomp_runtime.c
// Contains the code to perform the run-time processing of variable
// comparability which occurs at every program point

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

#include "generate_daikon_data.h"
#include "decls-output.h"
#include "kvasir_main.h"
#include "dyncomp_runtime.h"
#include "union_find.h"
#include "GenericHashtable.h"
#include <limits.h>

// Initialize hash tables for DynComp
// Pre: kvasir_with_dyncomp is active
// TODO: WARNING!  This hashtable-within-hashtable structure may
// blow up in my face and cause a huge memory overload!!!
// The use of calloc ensures that all tags within var_tags & new_tags are 0
void allocate_ppt_structures(DaikonFunctionInfo* funcPtr,
                             char isEnter,
                             int numDaikonVars) {
  if (isEnter) {
    // no hash function needed because GenericHashtable.h simply mods
    // it by the current size of the table
    funcPtr->ppt_entry_var_uf_map =
      genallocateSMALLhashtable((unsigned int (*)(void *)) 0,
                                (int (*)(void *,void *)) &equivalentTags);

    if (numDaikonVars > 0) {
      funcPtr->ppt_entry_var_tags =
        VG_(calloc)(numDaikonVars,
                    sizeof(*(funcPtr->ppt_entry_var_tags)));

      funcPtr->ppt_entry_new_tags =
        VG_(calloc)(numDaikonVars,
                    sizeof(*(funcPtr->ppt_entry_new_tags)));
    }
  }
  else {
    funcPtr->ppt_exit_var_uf_map =
      genallocateSMALLhashtable((unsigned int (*)(void *)) 0,
                                (int (*)(void *,void *)) &equivalentTags);

    if (numDaikonVars > 0) {
      funcPtr->ppt_exit_var_tags =
        VG_(calloc)(numDaikonVars,
                    sizeof(*(funcPtr->ppt_exit_var_tags)));

      funcPtr->ppt_exit_new_tags =
        VG_(calloc)(numDaikonVars,
                    sizeof(*(funcPtr->ppt_exit_new_tags)));
    }
  }

  funcPtr->num_daikon_vars = numDaikonVars;
}

void destroy_ppt_structures(DaikonFunctionInfo* funcPtr, char isEnter) {
  if (isEnter) {
    genfreehashtable(funcPtr->ppt_entry_var_uf_map);
    VG_(free)(funcPtr->ppt_entry_var_tags);
    VG_(free)(funcPtr->ppt_entry_new_tags);
  }
  else {
    genfreehashtable(funcPtr->ppt_exit_var_uf_map);
    VG_(free)(funcPtr->ppt_exit_var_tags);
    VG_(free)(funcPtr->ppt_exit_new_tags);
  }
}


// Variable comparability set map (var_uf_map) operations:

// Unions the uf_objects corresponding to tags tag1 and tag2 in
// var_uf_map and returns the leader:
static UInt var_uf_map_union(struct genhashtable* var_uf_map,
                             UInt tag1,
                             UInt tag2) {
  uf_object* uf_obj1 = 0;
  uf_object* uf_obj2 = 0;
  uf_object* leader_obj = 0;

  if (IS_ZERO_TAG(tag1) && IS_ZERO_TAG(tag2)) {
    return 0;
  }
  else if (IS_ZERO_TAG(tag2)) { // Only tag 1
    return tag1;
  }
  else if (IS_ZERO_TAG(tag1)) { // Only tag 2
    return tag2;
  }
  else { // Good.  Both are valid.
    uf_obj1 = (uf_object*)gengettable(var_uf_map, (void*)tag1);
    uf_obj2 = (uf_object*)gengettable(var_uf_map, (void*)tag2);
    if (uf_obj1 && uf_obj2) {
      leader_obj = uf_union(uf_obj1, uf_obj2);
      return leader_obj->tag;
    }
    // Ummm ... if one of the tags is NOT in var_uf_map, then
    // just return the other one and don't union anything
    else if (uf_obj1) {
      return tag1;
    }
    else if (uf_obj2) {
      return tag2;
    }
    else {
      return 0;
    }
  }
}

// Pre: tag is not a KEY in var_uf_map, tag is not zero
// Inserts a new entry in var_uf_map with tag as the KEY and a
// freshly-allocated uf_object in a singleton set (instantiated using
// uf_make_set) as the VALUE
static void var_uf_map_insert_and_make_set(struct genhashtable* var_uf_map,
                                           UInt tag) {
  uf_object* new_obj = VG_(malloc)(sizeof(*new_obj));
  uf_make_set(new_obj, tag, 0);
  genputtable(var_uf_map, (void*)tag, (void*)new_obj);
}


// Pre: The variable indexed by daikonVarIndex located at address 'a'
//      has been observed and the proper tags have been merged in memory
//      (handled in dtrace-output.c)
// Performs post-processing after observing a variable's value when
// printing out .dtrace information.  This roughly follows the
// algorithm created by SMcC in the comparability design document.
// Shown in comments are SMcC's current algorithm for propagating
// value comparability to variable comparability sets at each program
// point (annotated by pgbovine).
/*
for each variable indexed by v {
  // Update from any val_uf merges that have occurred for variables on
  // previous executions of this program point.

  // Make sure that the degenerate behavior of this line is that it
  // returns 0 so we don't do anything when there's no previous info.
  // to update
  tag leader = val_uf.find(var_tags[v]);
  if (leader != var_tags[v]) {
    var_tags[v] = var_uf_map.union(leader, var_tags[v]);
  }


  // Make sure that an entry is created in var_uf_map for the tag
  // associated with the new value that we observe from the
  // memory-level layer
  tag new_leader = val_uf.find(new_tags[v]);
  if (!var_uf_map.exists(new_leader)) {
    var_uf_map.insert(new_leader, make_set(new uf_object));
  }

  // Merge the sets of all values that were observed before for this
  // variable at this program point with the new value that we just
  // observed
  var_tags[v] = var_uf_map.union(var_tags[v], new_leader);
}
*/
void DC_post_process_for_variable(DaikonFunctionInfo* funcPtr,
                                  char isEnter,
                                  int daikonVarIndex,
                                  Addr a) {
  UInt leader, new_leader, var_tags_v, new_tags_v;
  struct genhashtable* var_uf_map;
  UInt *var_tags, *new_tags;

  if (isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
    new_tags = funcPtr->ppt_entry_new_tags;
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
    new_tags = funcPtr->ppt_exit_new_tags;
  }
  // Update from any val_uf merges that have occurred for variables on
  // previous executions of this program point.

  // Make sure that the degenerate behavior of this line is that it
  // returns 0 so we don't do anything when there's no previous info.
  // to update
  //  tag leader = val_uf.find(var_tags[v]);
  //  if (leader != var_tags[v]) {
  //    var_tags[v] = var_uf_map.union(leader, var_tags[v]);
  //  }
  var_tags_v = var_tags[daikonVarIndex];
  leader = val_uf_find_leader(var_tags_v);
  if (leader != var_tags_v) {
    var_tags[daikonVarIndex] = var_uf_map_union(var_uf_map,
                                                leader, var_tags_v);
  }

  // Make sure that an entry is created in var_uf_map for the tag
  // associated with the new value that we observe from the
  // memory-level layer
  //  tag new_leader = val_uf.find(new_tags[v]);
  //  if (!var_uf_map.exists(new_leader)) {
  //    var_uf_map.insert(new_leader, make_set(new uf_object));
  //  }
  new_tags_v = get_tag(a);
  new_leader = val_uf_find_leader(new_tags_v);
  if (new_leader && // Add a constraint that leader has to be non-zero
      !gengettable(var_uf_map, (void*)new_leader)) {
    var_uf_map_insert_and_make_set(var_uf_map, new_leader);
  }

  // Merge the sets of all values that were observed before for this
  // variable at this program point with the new value that we just
  // observed
  //  var_tags[v] = var_uf_map.union(var_tags[v], new_leader);
  var_tags[daikonVarIndex] = var_uf_map_union(var_uf_map,
                                              var_tags_v, new_leader);

  DYNCOMP_DPRINTF(" new_tags[%d]: %u, var_uf_map_union(new_leader: %u, var_tags_v (old): %u) ==> var_tags[%d]: %u (a: 0x%x)\n",
                  daikonVarIndex,
                  new_tags_v,
                  new_leader,
                  var_tags_v,
                  daikonVarIndex,
                  var_tags[daikonVarIndex],
                  a);

}

// This runs once for every Daikon variable at the END of the target
// program's execution

// This is a simplified version of the algorithm in
// DC_post_process_for_variable()
void DC_extra_propagation_post_process(DaikonFunctionInfo* funcPtr,
                                       char isEnter,
                                       int daikonVarIndex) {
  UInt leader, var_tags_v;
  struct genhashtable* var_uf_map;
  UInt *var_tags;

  if (isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
  }
  // Update from any val_uf merges that have occurred for variables on
  // previous executions of this program point.

  // Make sure that the degenerate behavior of this line is that it
  // returns 0 so we don't do anything when there's no previous info.
  // to update
  //  tag leader = val_uf.find(var_tags[v]);
  //  if (leader != var_tags[v]) {
  //    var_tags[v] = var_uf_map.union(leader, var_tags[v]);
  //  }
  var_tags_v = var_tags[daikonVarIndex];
  leader = val_uf_find_leader(var_tags_v);
  if (leader != var_tags_v) {
    var_tags[daikonVarIndex] = var_uf_map_union(var_uf_map,
                                                leader, var_tags_v);
  }

  DYNCOMP_DPRINTF(" var_uf_map_union(leader: %u, var_tags_v: %u) ==> var_tags[%d]: %u (final)\n",
                  leader,
                  var_tags_v,
                  daikonVarIndex,
                  var_tags[daikonVarIndex]);

}


// Super-trivial key comparison method -
int equivalentTags(UInt t1, UInt t2) {
  return (t1 == t2);
}


// Return the comparability number for the variable as a SIGNED
// INTEGER (because Daikon expects a signed integer).
// Here is how we translate from tags to comparability numbers:
// * If the tag is 0, then that means that the variable has never
//   been observed so we want to assign it a new unique number
//   to denote that it is not comparable to anything else
//   (assign it g_curCompNumber and then increment g_curCompNumber)
// * If the tag is non-zero, look up in g_compNumberMap to see
//   if a comp. number already exists for that tag.  If it does
//   exist, re-use that number.  If not, then assign g_curCompNumber
//   to it, add that entry to g_compNumberMap, and
//   increment g_curCompNumber
int DC_get_comp_number_for_var(DaikonFunctionInfo* funcPtr,
                               char isEnter,
                               int daikonVarIndex) {
  int comp_number;
  UInt tag = isEnter ?
    funcPtr->ppt_entry_var_tags[daikonVarIndex] :
    funcPtr->ppt_exit_var_tags[daikonVarIndex];

  if (0 == tag) {
    comp_number = g_curCompNumber;
    g_curCompNumber++;
  }
  else {
    if (gencontains(g_compNumberMap, (void*)tag)) {
      comp_number = (int)gengettable(g_compNumberMap, (void*)tag);
    }
    else {
      comp_number = g_curCompNumber;
      g_curCompNumber++;
      genputtable(g_compNumberMap, (void*)tag, (void*)comp_number);
    }
  }

  return comp_number;
}

// char isEnter = 1 for function ENTER, 0 for EXIT
static void DC_extra_propagate_one_function(DaikonFunctionInfo* funcPtr,
                                            char isEnter)
{
  extern FunctionTree* globalFunctionTree;

  // This is a GLOBAL so be careful :)
  // Reset it before doing any traversals with outputDaikonVar
  g_daikonVarIndex = 0;

  DYNCOMP_DPRINTF("Extra propagation: %s():::", funcPtr->name);
  if (isEnter) {
    DYNCOMP_DPRINTF("ENTER\n");
  }
  else {
    DYNCOMP_DPRINTF("EXIT\n");
  }

  // Propagate through globals
  if (!kvasir_ignore_globals) {
    printVariablesInVarList(funcPtr, isEnter, GLOBAL_VAR, 0,
                            DYNCOMP_EXTRA_PROP, 0,
                            (globalFunctionTree ?
                             globalFunctionTree->function_variables_tree : 0),
                            0, 0);
  }

  // Propagate through formal params.
  printVariablesInVarList(funcPtr, isEnter,
  			  (isEnter ?
  			   FUNCTION_ENTER_FORMAL_PARAM :
  			   FUNCTION_EXIT_FORMAL_PARAM),
  			  0, DYNCOMP_EXTRA_PROP, !isEnter,
  			  funcPtr->trace_vars_tree, 0, 0);

  // If EXIT, propagate through return value
  if (!isEnter) {
    printVariablesInVarList(funcPtr, isEnter, FUNCTION_RETURN_VAR, 0,
                            DYNCOMP_EXTRA_PROP, !isEnter,
                            funcPtr->trace_vars_tree, 0 ,0);
  }
}


// Do one extra round of value-to-variable tag comparability set
// propagations at the end of program execution
void DC_extra_propagate_val_to_var_sets() {
  DYNCOMP_DPRINTF("DC_extra_propagate_val_to_var_sets()\n");
  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);

  while(!it->finished) {
    DaikonFunctionInfo* cur_entry = (DaikonFunctionInfo*)
         gengettable(DaikonFunctionInfoTable, gennext(it));

    if (!cur_entry)
         continue;

    DC_extra_propagate_one_function(cur_entry, 1);
    DC_extra_propagate_one_function(cur_entry, 0);
  }

  genfreeiterator(it);
}

void debugPrintTagsInRange(Addr low, Addr high) {
  Addr a;
  UInt tag;
  char already_print_ellipses = 0;
  for (a = high; a >= low; a--) {
    tag = get_tag(a);
    if (tag) {
      DYNCOMP_DPRINTF("  0x%x: %u\n", a, tag);
      already_print_ellipses = 0;
    }

    else if (!already_print_ellipses) {
      DYNCOMP_DPRINTF("  ...\n");
      already_print_ellipses = 1;
    }
  }
}


// Tag garbage collector:

// Runs the tag garbage collector
void garbage_collect_tags() {
  UInt primaryIndex, secondaryIndex;
  UInt curTag = 0;
  UInt numTagsInUse = 0;
  UInt numTagsFreed = 0;
  UInt t, i;

  char free_list_num_elts_before_gc = 0;

  ThreadId currentTID = VG_(get_running_tid)();

  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);

  // Allocate a vector of size nextTag + 1, where each element is 0
  // if that tag is not being used and non-zero if it is being used.

  // We use calloc so we assume that no tags are initially being used:
  UChar* tagsInUse = VG_(calloc)(nextTag + 1, sizeof(UChar));

  // Possible optimization: Save 8x space by allocating a bit-vector
  // where each bit holds whether one tag has been used.
  // This is not implemented for now because for some reason, Valgrind
  // crashes with it ... do it later if space becomes a premium:

  //  UChar* tagsInUse = VG_(calloc)(((nextTag / 8) + 1), sizeof(UChar));

  // Allocate a bit-vector of size ((nextTag / 8) + 1) bytes to denote
  // which tags are currently being used.  We know that nextTag is an
  // upper-bound on the number of tags currently in use; all tags must
  // be in the range of [1, nextTag).

  // To find out if tag x in being used, we need to query the x-th bit
  // in the vector, which entails looking up tagsInUse[x / 8], then
  // right-shifting it by (x % 8) and masking off all but the LSB.  If
  // it is a 1, then the tag is being used; otherwise, it is not being
  // used:
  //#define TAG_IS_IN_USE(x) ((tagsInUse[(x) / 8] >> ((x) % 8)) & 0x1)

  // To set the 'in-use' bit for a tag x, we do something similar:
  //#define SET_TAG_IN_USE(x) tagsInUse[(x) / 8] |= (0x1 << ((x) % 8))

  VG_(printf)("Start garbage collecting tags (next tag = %u, total assigned = %u) size of free_list = %u ...\n", nextTag, totalNumTagsAssigned, free_list.numElts);

  // Clear to_be_freed_list
  clear_list(&to_be_freed_list);

  // Scan through all of the tag shadow memory and see which tags are
  // being used - these cannot be garbage collected

  for (primaryIndex = 0; primaryIndex < PRIMARY_SIZE; primaryIndex++) {
    if (primary_tag_map[primaryIndex]) {
      for (secondaryIndex = 0; secondaryIndex < SECONDARY_SIZE; secondaryIndex++) {
        // Remember to ignore 0 tags:
        curTag = primary_tag_map[primaryIndex][secondaryIndex];
        if (curTag > 0) {
          tagsInUse[curTag] = 1;
        }
      }
    }
  }

  // Scan through all of the ppt_entry_var_tags and ppt_exit_var_tags
  // of all program points to see which tags are being held there -
  // these cannot be garbage collected

  while(!it->finished) {
    UInt ind;
    DaikonFunctionInfo* cur_entry = (DaikonFunctionInfo*)
      gengettable(DaikonFunctionInfoTable, gennext(it));

    if (!cur_entry)
      continue;

    for (ind = 0; ind < cur_entry->num_daikon_vars; ind++) {
      UInt entry_tag = cur_entry->ppt_entry_var_tags[ind];
      UInt exit_tag = cur_entry->ppt_exit_var_tags[ind];

      if (entry_tag > 0) {
        tagsInUse[entry_tag] = 1;
      }

      if (exit_tag > 0) {
        tagsInUse[exit_tag] = 1;
      }
    }
  }

  genfreeiterator(it);


  // Scan through all of the guest state and see which tags are being
  // used - these cannot be garbage collected

  // Remember the offset * 4 hack thing (see do_shadow_PUT_DC() in
  // dyncomp_translate.c) - eek!

  // Just go through all of the registers in the x86 guest state
  // as depicted in vex/pub/libvex_guest_x86.h

  // These are the offsets that we are interested in:
#define NUM_TOTAL_X86_OFFSETS 55

static int x86_guest_state_offsets[NUM_TOTAL_X86_OFFSETS] = {
    0,  //      UInt  guest_EAX;         /* 0 */
    4,  //      UInt  guest_ECX;
    8,  //      UInt  guest_EDX;
    12, //      UInt  guest_EBX;
    16, //      UInt  guest_ESP;
    20, //      UInt  guest_EBP;
    24, //      UInt  guest_ESI;
    28, //      UInt  guest_EDI;         /* 28 */
      /* 4-word thunk used to calculate O S Z A C P flags. */
    32, //      UInt  guest_CC_OP;       /* 32 */
    36, //      UInt  guest_CC_DEP1;
    40, //      UInt  guest_CC_DEP2;
    44, //      UInt  guest_CC_NDEP;     /* 44 */
      /* The D flag is stored here, encoded as either -1 or +1 */
    48, //      UInt  guest_DFLAG;       /* 48 */
      /* Bit 21 (ID) of eflags stored here, as either 0 or 1. */
    52, //      UInt  guest_IDFLAG;      /* 52 */
      /* EIP */
    56, //      UInt  guest_EIP;         /* 56 */
      /* FPU */
    60, //      UInt  guest_FTOP;        /* 60 */
    64, //      ULong guest_FPREG[8];    /* 64 */
    72,
    80,
    88,
    96,
    104,
    112,
    120,
    128,  //      UChar guest_FPTAG[8];   /* 128 */
    129,
    130,
    131,
    132,
    133,
    134,
    135,
    136, //      UInt  guest_FPROUND;    /* 136 */
    140, //      UInt  guest_FC3210;     /* 140 */
      /* SSE */
    144, //      UInt  guest_SSEROUND;   /* 144 */
    148, //      U128  guest_XMM0;       /* 148 */
    164, //      U128  guest_XMM1;
    180, //      U128  guest_XMM2;
    196, //      U128  guest_XMM3;
    212, //      U128  guest_XMM4;
    228, //      U128  guest_XMM5;
    244, //      U128  guest_XMM6;
    260, //      U128  guest_XMM7;
      /* Segment registers. */
    276, //      UShort guest_CS;
    278, //      UShort guest_DS;
    280, //      UShort guest_ES;
    282, //      UShort guest_FS;
    284, //      UShort guest_GS;
    286, //      UShort guest_SS;
      /* LDT/GDT stuff. */
    288, //      HWord  guest_LDT; /* host addr, a VexGuestX86SegDescr* */
    292, //      HWord  guest_GDT; /* host addr, a VexGuestX86SegDescr* */

      /* Emulation warnings */
    296, //      UInt   guest_EMWARN;

      /* Translation-invalidation area description.  Not used on x86
         (there is no invalidate-icache insn), but needed so as to
         allow users of the library to uniformly assume that the guest
         state contains these two fields -- otherwise there is
         compilation breakage.  On x86, these two fields are set to
         zero by LibVEX_GuestX86_initialise and then should be ignored
         forever thereafter. */
    300, //      UInt guest_TISTART;
    304, //      UInt guest_TILEN;

      /* Padding to make it have an 8-aligned size */
    308  //      UInt   padding;
};

  for (i = 0; i < NUM_TOTAL_X86_OFFSETS; i++) {
    curTag = VG_(get_tag_for_x86_guest_offset)(currentTID,
                                               x86_guest_state_offsets[i]);
    if (curTag > 0) {
      tagsInUse[curTag] = 1;
    }
  }


  VG_(printf)("Iterating through tags in tagsInUse\n");

  free_list_num_elts_before_gc = free_list.numElts;

  // Iterate through all tags in tagsInUse and find which ones are NOT
  // in use (remember to skip the 0 tag):
  for (t = 1; t < nextTag; t++) {
    if (!tagsInUse[t]) {
      // If the tag is not already in free_list, then
      // put it in to_be_freed_list
      // TODO: Do I even need this check here???  I don't think so
      if (!is_tag_in_list(&free_list, t,
                          // Add 1 just to be safe from off-by-1 errors ...
                          // The concept is that we only care about duplicates
                          // from what is already in free_list, not the new
                          // stuff we will put into the tail of it
                          (free_list_num_elts_before_gc + 1))) {
        //        enqueue_tag(&to_be_freed_list, t);

        if (!IS_SECONDARY_UF_NULL(t)) {
          uf_object* obj = GET_UF_OBJECT_PTR(t);
          // Don't destroy objects that have already been destroyed ...
          if ((obj->parent) &&
              ((obj->ref_count == 1) || // This seems to cause tags to be freed which shouldn't be ... but why???
               (obj->ref_count == 0))) {
            uf_destroy_object(obj);

            enqueue_tag(&free_list, t);
            numTagsFreed++;
          }
        }
      }
    }
    else {
      // Count how many tags are being used
      numTagsInUse++;
    }
  }


  // Iterate through to_be_freed_list and check whether each tag can
  // truly be freed (refCount == 0 or 1) SMcC's suggestion: Do this TWICE
  // as a heuristic in order to try to get us closer to fixed-point.
  // This is because if you go through it in a particular order, you
  // may reach a parent before you reach a leaf.  You cannot free the
  // parent, but you can free the leaf.  Then the next time you go
  // through it, you can free the parent.  However, this sort of thing
  // probably doesn't happen too frequently because if the union-find
  // is working properly, you'll have one root and most entries will
  // be leaves.  Perhaps TWO passes is optimal.

/*   // Let's do it just once for now for speed ... */
/*   for (i = 0; i < 1; i++) { */
/*     TagNode* tagNode; */

/*     VG_(printf)("Begin pass # %u thru to_be_freed_list to free stuff\n", i); */

/*     // For every tag in to_be_freed_list, look up the reference count */
/*     // of the corresponding uf_object entry in the val_uf_object map. */
/*     // If it is 0 or 1, then destroy that entry (by clobbering it with */
/*     // zeroes and decreasing the ref_count of its parent!!!) and */
/*     // adding that tag to free_list.  Otherwise, do nothing. */
/*     for (tagNode = to_be_freed_list.first; */
/*          tagNode != NULL; */
/*          tagNode = tagNode->next) { */
/*       UInt tag = tagNode->tag; */
/*       uf_object* obj; */
/*       if (!IS_SECONDARY_UF_NULL(tag)) { */
/*         obj = GET_UF_OBJECT_PTR(tag); */
/*         // Don't destroy objects that have already been destroyed ... */
/*         if ((obj->parent) && */
/*             (obj->tag == tag) && */
/*             ((obj->ref_count == 1) || */
/*              (obj->ref_count == 0))) { */
/*           uf_destroy_object(obj); */

/*           // Optimization: The first pass ensures uniqueness, */
/*           //               but not the second pass */
/*           if (i == 0) { */
/*             if (enqueue_unique_tag(&free_list, tag)) { */
/*               //            VG_(printf)("Freed tag: %u\n", tag); */
/*               numTagsFreed++; */
/*             } */
/*           } */
/*           else { */
/*             if (enqueue_unique_tag(&free_list, tag)) { */
/*               //              VG_(printf)("Freed tag: %u\n", tag); */
/*               numTagsFreed++; */
/*             } */
/*           } */
/*         } */
/*       } */
/*     } */

/*     VG_(printf)("End pass # %u thru to_be_freed_list to free stuff - # tags freed so far: %u\n", i, numTagsFreed); */
/*   } */

  // Clean-up
  VG_(free)(tagsInUse);

  VG_(printf)("Done garbage collecting tags (next tag = %u, total assigned = %u) # tags in use: %u, # tags freed: %u - free_list.numElts = %u\n", nextTag, totalNumTagsAssigned, numTagsInUse, numTagsFreed, free_list.numElts);

}
