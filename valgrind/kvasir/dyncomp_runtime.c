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
#include "dyncomp_main.h"
#include "dyncomp_runtime.h"
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
  uf_make_set(new_obj, tag);
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

  UInt tagBeforeOp;

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

#ifdef USE_REF_COUNT
    tagBeforeOp = var_tags[daikonVarIndex];
#endif

    var_tags[daikonVarIndex] = var_uf_map_union(var_uf_map,
                                                leader, var_tags_v);

#ifdef USE_REF_COUNT
    // Avoid decrementing, freeing, and incrementing ref_count for the
    // SAME tag because that might lead to some subtle bugs:
    if (tagBeforeOp != var_tags[daikonVarIndex]) {
      dec_ref_count_for_tag(tagBeforeOp);
      inc_ref_count_for_tag(var_tags[daikonVarIndex]);
    }
#endif

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


#ifdef USE_REF_COUNT
    tagBeforeOp = var_tags[daikonVarIndex];
#endif

  var_tags[daikonVarIndex] = var_uf_map_union(var_uf_map,
                                              var_tags_v, new_leader);

#ifdef USE_REF_COUNT
    // Avoid decrementing, freeing, and incrementing ref_count for the
    // SAME tag because that might lead to some subtle bugs:
    if (tagBeforeOp != var_tags[daikonVarIndex]) {
      dec_ref_count_for_tag(tagBeforeOp);
      inc_ref_count_for_tag(var_tags[daikonVarIndex]);
    }
#endif


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

  UInt tagBeforeOp;

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

#ifdef USE_REF_COUNT
    tagBeforeOp = var_tags[daikonVarIndex];
#endif

    var_tags[daikonVarIndex] = var_uf_map_union(var_uf_map,
                                                leader, var_tags_v);

#ifdef USE_REF_COUNT
    // Avoid decrementing, freeing, and incrementing ref_count for the
    // SAME tag because that might lead to some subtle bugs:
    if (tagBeforeOp != var_tags[daikonVarIndex]) {
      dec_ref_count_for_tag(tagBeforeOp);
      inc_ref_count_for_tag(var_tags[daikonVarIndex]);
    }
#endif

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

// Offsets for all of the registers in the x86 guest state
// as depicted in vex/pub/libvex_guest_x86.h:

#define NUM_TOTAL_X86_OFFSETS 55

int x86_guest_state_offsets[NUM_TOTAL_X86_OFFSETS] = {
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


// Try to find leaderTag's entry in oldToNewMap (map from old tags to
// new tags).  If it does not exist, then write *p_newTagNumber in the
// contents of the address addr and add a new entry to oldToNewMap
// with the key as leaderTag and the value as *p_newTagNumber.  Then
// increment *p_newTagNumber.  (The idea here is that we want to do a
// mapping from tags which can be any number from 1 to nextTag to new
// numbers that are as small as possible.)  Otherwise, if it exists,
// overwrite the contents of the address addr the new tag associated
// with leaderTag, thus effectively re-assigning the tag held at that
// address to a newer, smaller tag.

// Pre: leaderTag != 0
static void reassign_tag(UInt* addr,
                         UInt leaderTag,
                         UInt* p_newTagNumber,
                         struct genhashtable* oldToNewMap) {

  if (gencontains(oldToNewMap, (void*)leaderTag)) {
    *addr = (int)gengettable(oldToNewMap, (void*)leaderTag);
  }
  else {
    *addr = *p_newTagNumber;
    genputtable(oldToNewMap,
                (void*)leaderTag, (void*)(*p_newTagNumber));

    (*p_newTagNumber)++;
  }
}

// Runs the tag garbage collector
void garbage_collect_tags() {
  UInt primaryIndex, secondaryIndex;
  struct geniterator* it;
  ThreadId currentTID;
  UInt curTag, i;

  UInt* addr;

  // Monotonically increases from 1 to whatever is necessary to map
  // old tags to new tags that are as small as possible (held as
  // values in oldToNewMap)
  UInt newTagNumber = 1;

  // Key: leader of tag which is in use during this step
  //      of garbage collection
  // Value: new tag that is as small as possible (start at 1 and
  //        increments as newTagNumber)
  struct genhashtable* oldToNewMap =
    genallocatehashtable(NULL, // no hash function needed for u_int keys
                         (int (*)(void *,void *)) &equivalentIDs);


  VG_(printf)("  Start tag GC (next tag = %u, total assigned = %u)\n",
              nextTag, totalNumTagsAssigned);

  // This algorithm goes through all places where tags are kept, finds
  // the leader for each one, and 'compresses' the set of tags in use
  // by re-numbering all leaders to the smallest possible numbers.  It
  // has the advantage of not requiring the use of a free list at all,
  // but the disadvantage of causing tag numbers to change, thus maybe
  // making debugging a bit more difficult (but shouldn't really,
  // since the tag numbers that change aren't the ones being used or
  // observed anyways).


  // There are 3 places where tags can be kept ... we need to scan
  // through all of these places looking for tags that are in use and
  // run reassign_tag() on every non-zero tag encountered in order to
  // canonicalize every tag to its leader and, more importantly, to
  // 'compress' the range of leader tags to a range from [1, nextTag)
  // to a smaller range of [1, newTagNumber).
  //
  // 1.) Shadow memory - for each byte of memory in the address space,
  // there is a corresponding 32-bit tag (0 for no tag assigned to
  // that byte of memory)
  //
  // 2.) Per program point - Because we are doing the
  // value-to-variable comparability calculations incrementally,
  // during every execution of a program point, we keep the leaders of
  // the tags of each Daikon variable's value at that program point.
  //
  // 3.) Guest state - There is a tag associated with each register
  // (i.e., EAX, EBX, floating-point stack)


  // 1.) Shadow memory:
  for (primaryIndex = 0; primaryIndex < PRIMARY_SIZE; primaryIndex++) {
    if (primary_tag_map[primaryIndex]) {
      for (secondaryIndex = 0; secondaryIndex < SECONDARY_SIZE; secondaryIndex++) {
        addr = &primary_tag_map[primaryIndex][secondaryIndex];

        if (*addr) { // Remember to ignore 0 tags
          reassign_tag(addr,
                       val_uf_find_leader(*addr),
                       &newTagNumber,
                       oldToNewMap);
        }
      }
    }
  }


  // 2.) Per program point:

  // Scan through all of the ppt_entry_var_tags and ppt_exit_var_tags
  // of all program points to see which tags are being held there -
  // these cannot be garbage collected
  it = gengetiterator(DaikonFunctionInfoTable);

  while(!it->finished) {
    UInt ind;
    DaikonFunctionInfo* cur_entry = (DaikonFunctionInfo*)
      gengettable(DaikonFunctionInfoTable, gennext(it));

    if (!cur_entry)
      continue;

    for (ind = 0; ind < cur_entry->num_daikon_vars; ind++) {
      UInt* p_entry_tag = &cur_entry->ppt_entry_var_tags[ind];
      UInt* p_exit_tag = &cur_entry->ppt_exit_var_tags[ind];

      if (*p_entry_tag) { // Remember to ignore 0 tags
        reassign_tag(p_entry_tag,
                     val_uf_find_leader(*p_entry_tag),
                     &newTagNumber,
                     oldToNewMap);
      }

      if (*p_exit_tag) {  // Remember to ignore 0 tags
        reassign_tag(p_exit_tag,
                     val_uf_find_leader(*p_exit_tag),
                     &newTagNumber,
                     oldToNewMap);
      }
    }
  }

  genfreeiterator(it);


  // 3.) Guest state:

  // Scan through all of the guest state and see which tags are being
  // used - these cannot be garbage collected

  // (Remember the offset * 4 hack thing (see do_shadow_PUT_DC() in
  // dyncomp_translate.c) - eek!)

  // Just go through all of the registers in the x86 guest state
  // as depicted in vex/pub/libvex_guest_x86.h
  currentTID = VG_(get_running_tid)();

  for (i = 0; i < NUM_TOTAL_X86_OFFSETS; i++) {
    addr =
      VG_(get_tag_ptr_for_x86_guest_offset)(currentTID,
                                            x86_guest_state_offsets[i]);
    if ((*addr) > 0) {
      reassign_tag(addr,
                   val_uf_find_leader(*addr),
                   &newTagNumber,
                   oldToNewMap);
    }
  }


  // Now that all tags in use have been re-assigned to newer
  // (hopefully smaller) values as denoted by the running counter
  // newTagNumber, we need to initialize all uf_object entries in the
  // val_uf_object_map from tag 1 until tag (newTagNumber - 1) to
  // singleton sets.  This is because the only tags in use now are in
  // the range of [1, newTagNumber) due to the 'compression' induced
  // by the tag re-assignment.
  for (curTag = 1; curTag < newTagNumber; curTag++) {
    val_uf_make_set_for_tag(curTag);
  }


  // For the grand finale, set nextTag = newTagNumber, thus completing
  // the garbage collection.
  nextTag = newTagNumber;


  // Clean-up:
  genfreehashtable(oldToNewMap);


  VG_(printf)("   Done tag GC (next tag = %u, total assigned = %u)\n", nextTag, totalNumTagsAssigned);

}


// This is called whenever a new 2^16 chunk is allocated (either for
// holding tags of uf_object entries).  Query the relationship between
// n_primary_tag_map_init_entries and
// n_primary_val_uf_object_map_init_entries to determine whether to
// call the garbage collector
void check_whether_to_garbage_collect() {
  const int k = 2;

  // As a heuristic, garbage-collect when
  // (n_primary_val_uf_object_map_init_entries >
  // (k * n_primary_tag_map_init_entries)) because the maximum amount of
  // tags in use is (2^16 * n_primary_tag_map_init_entries) and the
  // number of allocated tags is at most (2^16 *
  // n_primary_val_uf_object_map_init_entries)
  // - where k is some constant factor
  VG_(printf)("Tag map init entries: %u, uf_object map init entries: %u\n",
              n_primary_tag_map_init_entries,
              n_primary_val_uf_object_map_init_entries);

  if (n_primary_val_uf_object_map_init_entries >
      (k * n_primary_tag_map_init_entries)) {
    garbage_collect_tags();
  }

  // As another heuristic, do it every x number of total tag
  // assignments:

}


// Implementation of reference counting:
// (alternative to garbage collection)

#ifdef USE_REF_COUNT

// free_list is actually a uf_object* pointer that points to some
// element in val_uf (implemented as a two-level uf_object map) that
// has been freed. All uf_object elements that have been freed must
// have some special sentinel ref_count value - let's say USHRT_MAX
// (0xFFFF) - to denote that they have been freed and are in
// free_list.  All ub_object entries in free_list have their parent
// fields point to the NEXT freed entry in free_list. The last entry
// in free_list has a NULL parent field. Notice that we are
// overloading the parent field to mean different things when an entry
// is on the free list (linked list link) and not on the free list
// (union-find set link).
uf_object* free_list = NULL;

// During run-time, whenever the ref_count of a uf_object drops to 0
// (from a non-zero number), then add it to the head of
// free_list. This involves setting ref_count to USHRT_MAX,
// decrementing the ref_count field of its parent, setting its parent
// field to point to whatever free_list points to (the old head of the
// list), and changing free_list to point to this entry.

// Pre: obj->ref_count just dropped to 0 from a non-zero number
void free_list_push(uf_object* obj) {

  if (obj->tag == 1706695) {
    VG_(printf)("free_list_push(): obj->tag=%u\n", obj->tag);
  }

  DEC_REF_COUNT(obj->parent);
  obj->ref_count = USHRT_MAX; // Special sentinel value
  obj->parent = free_list;
  free_list = obj;
}


// Whenever a new tag is assigned, first check to see if free_list is
// non-NULL. If so, then there are freed tags waiting to be
// re-assigned so pop the first element off of free_list (by crawling
// one element down the list), initialize that popped element to a
// singleton set, and return the tag associated with that element.

// Pre: free_list is non-NULL
// Returns the tag of the head element of free_list, pops that element
// off of free_list, and initializes that element to a singleton set
UInt free_list_pop() {
  uf_object* popped_uf_obj = free_list;
  free_list = popped_uf_obj->parent;
  uf_make_set(popped_uf_obj, popped_uf_obj->tag);

  //  VG_(printf)("free_list_pop(): tag=%u, free_list=%p\n",
  //              popped_uf_obj->tag, free_list);

  return popped_uf_obj->tag;
}

// Increments the ref_count field of the uf_object entry corresponding
// to this tag.  This should be called whenever an operation causes a
// tag to be stored in one extra location.

// Pre: A uf_object for this tag has been allocated somewhere,
//      which means (!IS_SECONDARY_UF_NULL(tag))
void inc_ref_count_for_tag(UInt tag) {
  // Punt if it's a zero tag or UINT_MAX (special for ESP)
  if (tag && (tag != UINT_MAX)) {
    uf_object* obj = GET_UF_OBJECT_PTR(tag);
    INC_REF_COUNT(obj);
  }
}

// Decrements the ref_count field of the uf_object entry corresponding
// to this tag, and if it becomes 0, add it to free_list.  This should
// be called whenever an operation causes a tag to be removed from
// some location.

// Pre: A uf_object for this tag has been allocated somewhere,
//      which means (!IS_SECONDARY_UF_NULL(tag))
void dec_ref_count_for_tag(UInt tag) {
  // Punt if it's a zero tag or UINT_MAX (special for ESP)
  if (tag && (tag != UINT_MAX)) {

    uf_object* obj = GET_UF_OBJECT_PTR(tag);
    DEC_REF_COUNT(obj);

    // This tag may be eligible to be added onto free_list:
    if (0 == obj->ref_count) {
      free_list_push(obj);
    }
  }
}

#endif
