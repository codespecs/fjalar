// dyncomp_runtime.c
// Contains the code to perform the run-time processing of variable
// comparability which occurs at every program point

/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool.
  
   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
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

#include "../my_libc.h"

#include "pub_tool_basics.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h"
#include "pub_tool_threadstate.h"

#include "decls-output.h"
#include "kvasir_main.h"
#include "dyncomp_runtime.h"
#include "union_find.h"
#include "dyncomp_main.h"
#include "dyncomp_runtime.h"

#include "../fjalar_include.h"

#include "libvex_guest_x86.h"

extern char* func_name;
extern char* cur_var_name;

#if 0  // debuging
static void dump_function_exit_var_map(DaikonFunctionEntry*);
static void dump_all_function_exit_var_map(void);
static uf_name val_uf_tag(UInt);
#endif // debuging
static struct genhashtable* regenerate_var_uf_map(UInt, UInt*, struct genhashtable*, UInt*);
static void reassign_tag(UInt*, UInt, UInt*);

// Cast an intger to a void pointer in a architecture independent way. (markro)
#define VoidPtr(arg)  (void*)(ptrdiff_t)(arg)


// Maps tags to comparability numbers, which are assigned sequentially
// for every program point.  This is only used for DynComp.
// Key: tag (unsigned int)
// Value: comparability number (int) - notice that this is SIGNED because that
//                                     is what Daikon requires
struct genhashtable* g_compNumberMap = 0;

// This is the current sequential comparability number (only for
// DynComp).  It increments after it has been assigned as a value in
// g_compNumberMap, and it is reset back to 1 during every program
// point.
int g_curCompNumber = 1;


// Key (Array index): leader of tag which is in use during this step
//                    of garbage collection
// Value (Array contents): new tag that is as small as possible (start
//                         at 1 and increments as newTagNumber)
//
// Clear and initialize it to (nextTag + 1) before every run of
// garbage collector (Remember that index 0 is never used because 0
// tag is invalid)
UInt* g_oldToNewMap = 0;

int is_enter;
static TraversalAction dyncompExtraPropAction;

// Initialize hash tables for DynComp
// Pre: kvasir_with_dyncomp is active
// (comment added 2005)  
// TODO: WARNING!  This hashtable-within-hashtable structure may
// blow up in my face and cause a huge memory overload!!!
// The use of calloc ensures that all tags within var_tags & new_tags are 0
void allocate_ppt_structures(DaikonFunctionEntry* funcPtr,
                             char isEnter,
                             int numDaikonVars) {
  // Don't do anything if we are attempting to allocate for enter and
  // are not using --dyncomp-separate-entry-exit
  if (isEnter && !dyncomp_separate_entry_exit) {
    return;
  }

  if (dyncomp_separate_entry_exit && isEnter) {
    if (dyncomp_detailed_mode) {
      UInt bitarray_size = bitarraySize(numDaikonVars);
      if (bitarray_size > 0) {
        funcPtr->ppt_entry_bitmatrix = VG_(calloc)("dyncomp_runtime.c: allocate_ppt_structures.1", bitarray_size,
                                                   sizeof(*(funcPtr->ppt_entry_bitmatrix)));
      }

      if (numDaikonVars > 0) { // calloc'ing 0-length array doesn't work
        funcPtr->ppt_entry_new_tag_leaders = VG_(calloc)("dyncomp_runtime.c: allocate_ppt_structures.2", numDaikonVars,
                                                         sizeof(*(funcPtr->ppt_entry_new_tag_leaders)));
      }
    }
    else {
      // no hash function needed because GenericHashtable.h simply
      // mods it by the current size of the table
      funcPtr->ppt_entry_var_uf_map =
        genallocateSMALLhashtable((unsigned int (*)(void *)) 0,
                                  (int (*)(void *,void *)) &equivalentTags);

      if (numDaikonVars > 0) { // calloc'ing 0-length array doesn't work
        funcPtr->ppt_entry_var_tags = VG_(calloc)("dyncomp_runtime.c: allocate_ppt_structures.3", numDaikonVars,
                                                  sizeof(*(funcPtr->ppt_entry_var_tags)));
      }
    }

    funcPtr->num_entry_daikon_vars = numDaikonVars;
  }
  else {
    if (dyncomp_detailed_mode) {
      UInt bitarray_size = bitarraySize(numDaikonVars);
      if (bitarray_size > 0) {
        funcPtr->ppt_exit_bitmatrix = VG_(calloc)("dyncomp_runtime.c: allocate_ppt_structures.4", bitarray_size,
                                                  sizeof(*(funcPtr->ppt_exit_bitmatrix)));
      }

      if (numDaikonVars > 0) { // calloc'ing 0-length array doesn't work
        funcPtr->ppt_exit_new_tag_leaders = VG_(calloc)("dyncomp_runtime.c: allocate_ppt_structures.5", numDaikonVars,
                                                        sizeof(*(funcPtr->ppt_exit_new_tag_leaders)));
      }
    }
    else {
      funcPtr->ppt_exit_var_uf_map =
        genallocateSMALLhashtable((unsigned int (*)(void *)) 0,
                                  (int (*)(void *,void *)) &equivalentTags);

      if (numDaikonVars > 0) { // calloc'ing 0-length array doesn't work
        funcPtr->ppt_exit_var_tags = VG_(calloc)("dyncomp_runtime.c: allocate_ppt_structures.6", numDaikonVars,
                                                 sizeof(*(funcPtr->ppt_exit_var_tags)));
      }
    }

    funcPtr->num_exit_daikon_vars = numDaikonVars;
  }
}

void destroy_ppt_structures(DaikonFunctionEntry* funcPtr, char isEnter) {
  // Don't do anything if we are attempting to free for enter and are
  // not using --dyncomp-separate-entry-exit
  if (isEnter && !dyncomp_separate_entry_exit) {
    return;
  }

  if (dyncomp_separate_entry_exit && isEnter) {
    if (dyncomp_detailed_mode) {
      VG_(free)(funcPtr->ppt_entry_bitmatrix);
      funcPtr->ppt_entry_bitmatrix = 0;
      VG_(free)(funcPtr->ppt_entry_new_tag_leaders);
      funcPtr->ppt_entry_new_tag_leaders = 0;
    }
    else {
      genfreehashtableandvalues(funcPtr->ppt_entry_var_uf_map);
      funcPtr->ppt_entry_var_uf_map = 0;
      VG_(free)(funcPtr->ppt_entry_var_tags);
      funcPtr->ppt_entry_var_tags = 0;
    }
  }
  else {
    if (dyncomp_detailed_mode) {
      VG_(free)(funcPtr->ppt_exit_bitmatrix);
      funcPtr->ppt_exit_bitmatrix = 0;
      VG_(free)(funcPtr->ppt_exit_new_tag_leaders);
      funcPtr->ppt_exit_new_tag_leaders = 0;
    }
    else {
      genfreehashtableandvalues(funcPtr->ppt_exit_var_uf_map);
      funcPtr->ppt_exit_var_uf_map = 0;
      VG_(free)(funcPtr->ppt_exit_var_tags);
      funcPtr->ppt_exit_var_tags = 0;
    }
  }
}


// Variable comparability set map (var_uf_map) operations:

#if 0  // debuging
static uf_name var_uf_map_find(struct genhashtable* var_uf_map, UInt tag) {
  if (!tag) {
    return NULL;
  }
  return (uf_object*)gengettable(var_uf_map, VoidPtr(tag));
}
#endif // debuging

static UInt var_uf_map_find_leader(struct genhashtable* var_uf_map, UInt tag) {
  if (!tag) {
    return 0;
  } else {
    uf_object* uf_obj = (uf_object*)gengettable(var_uf_map, VoidPtr(tag));
    if (uf_obj) {
      return (uf_find(uf_obj))->tag;
    } else {
      return 0;
    }
  }
}

// Pre: tag is not a KEY in var_uf_map, tag is not zero
// Inserts a new entry in var_uf_map with tag as the KEY and a
// freshly-allocated uf_object in a singleton set (instantiated using
// uf_make_set) as the VALUE
// Returns the uf_object* to the new entry
static uf_object* var_uf_map_insert_and_make_set(struct genhashtable* var_uf_map,
                                                 UInt tag) {
  uf_object *new_obj;
  if (!tag) {
    return 0;
  }

  new_obj = VG_(malloc)("dyncomp_runtime.c: var_uf_mims", sizeof(*new_obj));
  uf_make_set(new_obj, tag);
  genputtable(var_uf_map, VoidPtr(tag), (void*)new_obj);
  return new_obj;
}

// Unions the uf_objects corresponding to tags tag1 and tag2 in
// var_uf_map and returns the leader:
// (Note that if a tag is non-zero but does not yet have an entry in
//  var_uf_map, a new singleton entry will be created for it.
//  This seems to allow the garbage collector to work correctly.)
static UInt var_uf_map_union(struct genhashtable* var_uf_map,
                             UInt tag1,
                             UInt tag2) {

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
    uf_object* uf_obj1 = (uf_object*)gengettable(var_uf_map, VoidPtr(tag1));
    uf_object* uf_obj2 = (uf_object*)gengettable(var_uf_map, VoidPtr(tag2));
    uf_object* leader_obj = 0;

    // If one of the tags is NOT in var_uf_map, then
    // create a new singleton entry for it
    if (!uf_obj1) {
      uf_obj1 = var_uf_map_insert_and_make_set(var_uf_map, tag1);
    }

    if (!uf_obj2) {
      uf_obj2 = var_uf_map_insert_and_make_set(var_uf_map, tag2);
    }

    leader_obj = uf_union(uf_obj1, uf_obj2);
    DYNCOMP_TPRINTF("[DynComp] Merging %u with %u to get %u at (%s - %s) - VARIABLE\n",
		    tag1, tag2, leader_obj->tag,(is_enter == 1)?"Entering":"Exiting", func_name );
    return leader_obj->tag;
  }
}


// Pre: The variable indexed by daikonVarIndex located at address 'a'
//      has been observed and the proper tags have been merged in memory.
// Performs post-processing after observing a variable's value when
// printing out .dtrace information.  This roughly follows the
// algorithm described in Philip Guo's and/or Robert Rudd's Master Thesis.
/*
for each variable indexed by v {
  // Update to account for any val_uf merges that have occurred for a
  // variable's previously observed values.  I.e., changes that have
  // occured between the previous program point (for this function) and
  // the current program point.
  tag leader = val_uf.find(var_tags[v]);
  if (leader != var_tags[v]) {
    var_tags[v] = var_uf_map.union(leader, var_tags[v]);
  }

  // Make sure that an entry is created in var_uf_map for the tag
  // associated with the value that we observe for this program point.
  tag new_leader = val_uf.find(val_tags[address of v]);
  if (!var_uf_map.exists(new_leader)) {
    var_uf_map.insert(new_leader, make_set(new uf_object));
  }

  // Merge the sets of all values that were observed before for this
  // variable at this program point with the new value that we just
  // observed
  var_tags[v] = var_uf_map.union(var_tags[v], new_leader);
*/

// IMPORTANT ADDENDUM:
// While the first step described above is necessary, it is not
// sufficient.  You must check for any val tag changes in all
// members of the var set, not just the leader.
// (markro June 2016)

void DC_post_process_for_variable(DaikonFunctionEntry* funcPtr,
                                  char isEnter,
                                  VariableOrigin varOrigin,
                                  int daikonVarIndex,
                                  Addr a) {

  UInt leader, new_leader, var_tags_v, new_tags_v;
  struct genhashtable* var_uf_map;
  UInt* var_tags;
  UInt* new_tag_leaders;

  DYNCOMP_DPRINTF("DC_post_process_for_variable - %p\n", (void *)a);
  // Remember to use only the EXIT structures unless
  // isEnter and --dyncomp-separate-entry-exit are both True
  is_enter = isEnter;
  if (dyncomp_separate_entry_exit && isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
    new_tag_leaders = funcPtr->ppt_entry_new_tag_leaders;
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
    new_tag_leaders = funcPtr->ppt_exit_new_tag_leaders;
  }

  if (dyncomp_detailed_mode) { // detailed O(n^2) algorithm
    // When iterating through all the variables, simply collect tags
    // in new_tag_leaders.  Iterate through all of them in
    // DC_detailed_mode_process_ppt_execution() after we are done
    // collecting the leader tags for all variables:
    if (a) {
      new_tag_leaders[daikonVarIndex] = val_uf_find_leader(get_tag(a));
    }
    else {
      // clear this out so that it doesn't leak values from a previous
      // execution of this program point:
      new_tag_leaders[daikonVarIndex] = 0;
    }
  }
  else {// default algorithm
    if (!a) {// Do not bother processing if there is no address!
      return;
    }

  // Update to account for any val_uf merges that have occurred for a
  // variable's previously observed values.
  var_tags_v = var_tags[daikonVarIndex];
  if (var_tags_v) {
    uf_object* uf_leader = (uf_object*)gengettable(var_uf_map, VoidPtr(var_tags_v));
    tl_assert(uf_leader);

    // See if the associated val set has changed since the last observation.
    leader = val_uf_find_leader(var_uf_map_find_leader(var_uf_map, var_tags_v));
    if (leader != var_tags_v) {
      // If it has, union old with new
      DYNCOMP_TPRINTF("Dyncomp] leader != var_tags_v. var_tags_v: %u, leader: %u\n", var_tags_v, leader);
      leader = var_uf_map_union(var_uf_map, leader, var_tags_v);
      DYNCOMP_TPRINTF("         new leader: %u\n", leader);
    }

    // (This next section is the correction described in the addendum.)
    // We need to iterate through the members of the var set for var_tags_v.
    // No easy way to do this, so check all members of the var_uf_map to
    // see if they qualify.
    struct genpointerlist* var_item = var_uf_map->list;
    while (var_item) {
      uf_object* uf_obj = (uf_object*)(var_item->object);
      // If member of the same var set, then we need to process
      // (but not if its the leader, that was already processed)
      if ((uf_leader == uf_obj->parent) && (uf_leader != uf_obj)) {
        // See if the associated val set has changed since the last observation.
        UInt t = val_uf_find_leader(uf_obj->tag);
        DYNCOMP_TPRINTF("         %p %8u %u\n", uf_obj, uf_obj->tag, t);
        if (t !=  uf_obj->tag) {
          // It has, union our current leader with new val set.
          leader = var_uf_map_union(var_uf_map, leader, t);
          DYNCOMP_TPRINTF("         new leader: %u\n", leader);
        }
      }
      var_item = var_item->inext;
    }

    // If any of the associated val sets have changed we need
    // to update the leader stored in the var_tags array.
    if (leader != var_tags_v) {
      DYNCOMP_TPRINTF("Dyncomp] new leader != var_tags_v. var_tags_v: %u, new leader: %u\n", var_tags_v, leader);
      var_tags[daikonVarIndex] = leader;
      var_tags_v = leader;
    }
  }

  // Make sure that an entry is created in var_uf_map for the tag
  // associated with the value that we observe for this program point.
  new_tags_v = get_tag(a);
  new_leader = val_uf_find_leader(new_tags_v);

  DYNCOMP_TPRINTF("\n[DynComp] OBSERVATION POINT: %s - %u (%s - %s invocation %u)\n",
                  cur_var_name,  new_leader, isEnter?"ENTRY":"EXIT", func_name, funcPtr->num_invocations);
  DYNCOMP_TPRINTF("post_process_for_variable - address: %p, current var tag: %u, new val tag: %u, new val leader: %u \n",
            (void *)a, var_tags_v, new_tags_v, new_leader);

  if (new_leader && // We don't want to insert 0 tags into the union find structure
      !gengettable(var_uf_map, VoidPtr(new_leader))) {
    var_uf_map_insert_and_make_set(var_uf_map, new_leader);
  }

  // While I still feel there is something not quite right with how
  // we process the special function 'return' variable, the changes
  // I have tried do not look better.  I am leaving this part of
  // the alogorithm unchanged for now.  markro 6/27/2016.
  //
  // Merge the sets of all values that were observed before for this
  // variable at this program point with the new value that we just
  // observed
//if (varOrigin != FUNCTION_RETURN_VAR) {
  new_leader = var_uf_map_union(var_uf_map, var_tags_v, new_leader);
//}

  DYNCOMP_TPRINTF("[DynComp] %s new var tag[%d]: %u\n", cur_var_name, daikonVarIndex, new_leader);
  var_tags[daikonVarIndex] = new_leader;
  }
}


// This is a simplified version of the algorithm in
// DC_post_process_for_variable() that runs once
// for every Daikon variable at the END of the target
// program's execution.
// NOTE: The same addendum applies here. (markro)
void DC_extra_propagation_post_process(DaikonFunctionEntry* funcPtr,
                                       char isEnter,
                                       int daikonVarIndex) {
  UInt leader, var_tags_v;
  struct genhashtable* var_uf_map;
  UInt *var_tags;

  // We currently do not do any extra propagation when we are in
  // dyncomp_detailed_mode:
  if (dyncomp_detailed_mode) {
    return;
  }
  is_enter = isEnter;

  // Remember to use only the EXIT structures unless
  // isEnter and --dyncomp-separate-entry-exit are both True
  if (dyncomp_separate_entry_exit && isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
  }

  // Update to account for any val_uf merges that have occurred for a
  // variable's previously observed values.
  var_tags_v = var_tags[daikonVarIndex];
  if (var_tags_v) {
    uf_object* uf_leader = (uf_object*)gengettable(var_uf_map, VoidPtr(var_tags_v));
    tl_assert(uf_leader);

    // See if the associated val set has changed since the last observation.
    leader = val_uf_find_leader(var_uf_map_find_leader(var_uf_map, var_tags_v));
    if (leader != var_tags_v) {
      // If it has, union old with new
      DYNCOMP_TPRINTF("extra-post_process (leader): %u, %u \n", var_tags_v, leader);
      leader = var_uf_map_union(var_uf_map, leader, var_tags_v);
      DYNCOMP_TPRINTF("               new leader: %u\n", leader);
    }

    // (This next section is the correction described in the addendum.)
    // We need to iterate through the members of the var set for var_tags_v.
    // No easy way to do this, so check all members of the var_uf_map to
    // see if they qualify.
    struct genpointerlist* var_item = var_uf_map->list;
    while (var_item) {
      uf_object* uf_obj = (uf_object*)(var_item->object);
      // If member of the same var set, then we need to process
      // (but not if its the leader, that was already processed)
      if ((uf_leader == uf_obj->parent) && (uf_leader != uf_obj)) {
        // See if the associated val set has changed since the last observation.
        UInt t = val_uf_find_leader(uf_obj->tag);
        DYNCOMP_TPRINTF("  %p %8u %u\n", uf_obj, uf_obj->tag, t);
        if (t !=  uf_obj->tag) {
          // It has, union our current leader with new val set.
          leader = var_uf_map_union(var_uf_map, leader, t);
          DYNCOMP_TPRINTF("extra-post_process (set member): %u \n", leader);
        }
      }
      var_item = var_item->inext;
    }

    // If any of the associated val sets have changed we need
    // to update the leader stored in the var_tags array.
    if (leader != var_tags_v) {
      var_tags[daikonVarIndex] = leader;
    }
  }

  DYNCOMP_TPRINTF("[DynComp] Variable processing in %s[%d]: merging distinct values "
		  "%u (old) and %u (new) to %u (final round)\n",
		  funcPtr->funcEntry.name, daikonVarIndex,
		  var_tags_v, leader, var_tags[daikonVarIndex]);
}

// Super-trivial key comparison method -
int equivalentTags(UInt t1, UInt t2) {
  return (t1 == t2);
}

// Return the comparability number for the variable as a SIGNED
// INTEGER (because Daikon expects a signed integer).
//
// First of all, update the tag with its LEADER in the appropriate var_uf_map,
// because the leaders represent the disjoint sets, not the tags themselves.
//
// Here is how we translate from leader tags to comparability numbers:
// * If the tag is 0, then that means that the variable has never
//   been observed so we want to assign it a new unique number
//   to denote that it is not comparable to anything else
//   (assign it g_curCompNumber and then increment g_curCompNumber)
// * If the leader tag is non-zero, look up in g_compNumberMap to see
//   if a comp. number already exists for that leader tag.  If it does
//   exist, re-use that number.  If not, then assign g_curCompNumber
//   to it, add that entry to g_compNumberMap, and
//   increment g_curCompNumber
//
// If the --dyncomp-separate-entry-exit option is not on, then
// always grab the comparability numbers from the exit ppt
// of the function in order to ensure that the comparability
// numbers from the entrance/exit always matches.
int DC_get_comp_number_for_var(DaikonFunctionEntry* funcPtr,
                               char isEnter,
                               int daikonVarIndex) {
  int comp_number;
  UInt tag;

  struct genhashtable* var_uf_map;
  UInt *var_tags;

  // Remember to use only the EXIT structures unless
  // isEnter and --dyncomp-separate-entry-exit are both True
  if (dyncomp_separate_entry_exit && isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
  }

  if (dyncomp_detailed_mode) {
    // var_tags already contains the leaders, so all we need to do is
    // to have it map to g_curCompNumber to produce the correct
    // comparability numbers:
    UInt leader = var_tags[daikonVarIndex];
    if (gencontains(g_compNumberMap, VoidPtr(leader))) {
      comp_number = (ptrdiff_t)gengettable(g_compNumberMap, VoidPtr(leader));
    }
    else {
      comp_number = g_curCompNumber;
      g_curCompNumber++;
      genputtable(g_compNumberMap, VoidPtr(leader), VoidPtr(comp_number));
    }
  }
  else {  // default behavior
    tag = var_tags[daikonVarIndex];
    if (0 == tag) {
      comp_number = g_curCompNumber;
      g_curCompNumber++;
    }
    else {
      // First, convert the tag to its leader.  This is very
      // important, because if we don't do this, we are going to get
      // smaller comparability sets, which is inaccurate.  We should
      // map the LEADERS (not individual tags) to comparability
      // numbers because the leaders represent the distinctive sets.
      UInt leader = val_uf_find_leader(var_uf_map_find_leader(var_uf_map, tag));

      // If we are debugging, don't change any state.
      if (!doing_debug_print) {
        var_tags[daikonVarIndex] = leader;
      }
      if (gencontains(g_compNumberMap, VoidPtr(leader))) {
        comp_number = (ptrdiff_t)gengettable(g_compNumberMap, VoidPtr(leader));
      }
      else {
        comp_number = g_curCompNumber;
        g_curCompNumber++;
        genputtable(g_compNumberMap, VoidPtr(leader), VoidPtr(comp_number));
      }
      DYNCOMP_TPRINTF("[DynComp] Final tag for Function %s Variable %s - %u\n", funcPtr->funcEntry.name, cur_var_name, leader);
      DYNCOMP_TPRINTF("tag: %u, leader1: %u, leader2: %u \n", tag, var_uf_map_find_leader(var_uf_map, tag), leader);
    }
  }

  return comp_number;
}

static TraversalResult dyncompExtraPropAction(VariableEntry* var,
                                              const HChar* varName,
                                              VariableOrigin varOrigin,
                                              UInt numDereferences,
                                              UInt layersBeforeBase,
                                              Bool overrideIsInit,
                                              DisambigOverride disambigOverride,
                                              Bool isSequence,
                                              // pValue only valid if isSequence is false
                                              Addr pValue,
                                              Addr pValueGuest,
                                              // pValueArray and numElts only valid if
                                              // isSequence is true
                                              Addr* pValueArray,
                                              Addr* pValueArrayGuest,
                                              UInt numElts,
                                              FunctionEntry* varFuncInfo,
                                              Bool isEnter) {
  // Cast it to a DaikonFunctionEntry in order to access the
  // DynComp-specific fields:
  DaikonFunctionEntry* daikonFuncInfo = (DaikonFunctionEntry*)varFuncInfo;

  /* Silence unused-variable warnings */
  (void)varName; (void)varOrigin; (void)numDereferences;
  (void)overrideIsInit; (void)disambigOverride; (void)isSequence;
  (void)pValue; (void)pValueArray; (void)numElts;
  (void)pValueGuest; (void)pValueArrayGuest;

  // Special handling for static arrays: Currently, in the
  // .dtrace, for a static arrays 'int foo[]', we print out
  // 'foo' as the address of foo and 'foo[]' as the contents of
  // 'foo'.  However, for comparability, there is no place in
  // memory where the address of 'foo' is maintained; thus,
  // there is no tag for it anywhere, so we must not
  // post-process it and simply allow it to keep a tag of 0.
  // This implies that all static array hashcode values are
  // unique and not comparable to one another, which is the
  // intended behavior.  (Notice that if one wants to assign a
  // pointer to 'foo', then the address of 'foo' resides
  // somewhere in memory - where that pointer is located - and
  // thus gets a fresh tag.  One can then have that pointer
  // interact with other pointers and have THEM be comparable,
  // but 'foo' itself still has no tag and is not comparable to
  // anything else.)

  // Don't do anything if this condition holds:
  // (layersBeforeBase > 0) is okay since var->isStaticArray implies
  // that there is only one level of pointer indirection, and for a
  // static string (static array of 'char'), layersBeforeBase == 0
  // right away so we still process it
  if (!(IS_STATIC_ARRAY_VAR(var) && (layersBeforeBase > 0))) {
    DC_extra_propagation_post_process(daikonFuncInfo,
                                      isEnter,
                                      g_variableIndex);
  }

  return DISREGARD_PTR_DEREFS;
}

// char isEnter = 1 for function ENTER, 0 for EXIT
static void DC_extra_propagate_one_function(FunctionEntry* funcPtr,
                                            char isEnter)
{
  // This is a GLOBAL so be careful :)
  // Reset it before doing any traversals with outputDaikonVar
  g_variableIndex = 0;

  DYNCOMP_DPRINTF("Extra propagation: %s():::", funcPtr->name);
  if (isEnter) {
    DYNCOMP_DPRINTF("ENTER\n");
  }
  else {
    DYNCOMP_DPRINTF("EXIT\n");
  }

  // Propagate through globals (visitVariableGroup() ignores the
  // globals if --ignore-globals is used):
  visitVariableGroup(GLOBAL_VAR,
                     funcPtr, // need this for DynComp to work properly
                     isEnter,
                     0,
		     0,
                     &dyncompExtraPropAction);

  // Propagate through formal params.
  visitVariableGroup(FUNCTION_FORMAL_PARAM,
                     funcPtr,
                     isEnter,
                     0,
		     0,
                     &dyncompExtraPropAction);

  // If EXIT, propagate through return value
  if (!isEnter) {
  visitVariableGroup(FUNCTION_RETURN_VAR,
                     funcPtr,
                     0,
                     0,
		     0,
                     &dyncompExtraPropAction);
  }
}

// Do one extra round of value-to-variable tag comparability set
// propagations at the end of program execution
void DC_extra_propagate_val_to_var_sets() {
  FuncIterator* funcIt = newFuncIterator();
  DYNCOMP_DPRINTF("DC_extra_propagate_val_to_var_sets()\n");

  //dump_all_function_exit_var_map();
  while (hasNextFunc(funcIt)) {
    FunctionEntry* cur_entry = nextFunc(funcIt);
    tl_assert(cur_entry);
    DYNCOMP_DPRINTF("Function: %s\n", cur_entry->name);
    // Remember to only propagate through the functions to be traced
    // if kvasir_trace_prog_pts_filename is on:
    if (!fjalar_trace_prog_pts_filename ||
        // If kvasir_trace_prog_pts_filename is on (we are reading in
        // a ppt list file), then DO NOT OUTPUT .decls entries for
        // program points that we are not interested in tracing.  This
        // decreases the clutter of the .decls file and speeds up
        // processing time
        prog_pts_tree_entry_found(cur_entry)) {
      DC_extra_propagate_one_function(cur_entry, 1);
      DC_extra_propagate_one_function(cur_entry, 0);
      //dump_all_function_exit_var_map();
    }
  }
  deleteFuncIterator(funcIt);
}

void debugPrintTagsInRange(Addr low, Addr high) {
  Addr a;
  UInt tag;
  char already_print_ellipses = 0;
  for (a = high; a >= low; a--) {
    tag = get_tag(a);
    if (tag) {
      DYNCOMP_DPRINTF("  %p: %u\n", (void *)a, tag);
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

#define NUM_TOTAL_X86_OFFSETS 56 // 55

// Use the offsetof macro to get offsets instead of
// hand-coding them:
int x86_guest_state_offsets[NUM_TOTAL_X86_OFFSETS] = {
  offsetof(VexGuestX86State, guest_EAX),
  offsetof(VexGuestX86State, guest_ECX),
  offsetof(VexGuestX86State, guest_EDX),
  offsetof(VexGuestX86State, guest_EBX),

  offsetof(VexGuestX86State, guest_ESP),
  offsetof(VexGuestX86State, guest_EBP),
  offsetof(VexGuestX86State, guest_ESI),
  offsetof(VexGuestX86State, guest_EDI),

  offsetof(VexGuestX86State, guest_CC_OP),
  offsetof(VexGuestX86State, guest_CC_DEP1),
  offsetof(VexGuestX86State, guest_CC_DEP2),
  offsetof(VexGuestX86State, guest_CC_NDEP),

  offsetof(VexGuestX86State, guest_DFLAG),
  offsetof(VexGuestX86State, guest_IDFLAG),
  offsetof(VexGuestX86State, guest_ACFLAG),

  offsetof(VexGuestX86State, guest_EIP),

  offsetof(VexGuestX86State, guest_FPREG[0]),
  offsetof(VexGuestX86State, guest_FPREG[1]),
  offsetof(VexGuestX86State, guest_FPREG[2]),
  offsetof(VexGuestX86State, guest_FPREG[3]),
  offsetof(VexGuestX86State, guest_FPREG[4]),
  offsetof(VexGuestX86State, guest_FPREG[5]),
  offsetof(VexGuestX86State, guest_FPREG[6]),
  offsetof(VexGuestX86State, guest_FPREG[7]),

  offsetof(VexGuestX86State, guest_FPTAG[0]),
  offsetof(VexGuestX86State, guest_FPTAG[1]),
  offsetof(VexGuestX86State, guest_FPTAG[2]),
  offsetof(VexGuestX86State, guest_FPTAG[3]),
  offsetof(VexGuestX86State, guest_FPTAG[4]),
  offsetof(VexGuestX86State, guest_FPTAG[5]),
  offsetof(VexGuestX86State, guest_FPTAG[6]),
  offsetof(VexGuestX86State, guest_FPTAG[7]),

  offsetof(VexGuestX86State, guest_FPROUND),
  offsetof(VexGuestX86State, guest_FC3210),
  offsetof(VexGuestX86State, guest_FTOP),

  offsetof(VexGuestX86State, guest_SSEROUND),
  offsetof(VexGuestX86State, guest_XMM0),
  offsetof(VexGuestX86State, guest_XMM1),
  offsetof(VexGuestX86State, guest_XMM2),
  offsetof(VexGuestX86State, guest_XMM3),
  offsetof(VexGuestX86State, guest_XMM4),
  offsetof(VexGuestX86State, guest_XMM5),
  offsetof(VexGuestX86State, guest_XMM6),
  offsetof(VexGuestX86State, guest_XMM7),

  offsetof(VexGuestX86State, guest_CS),
  offsetof(VexGuestX86State, guest_DS),
  offsetof(VexGuestX86State, guest_ES),
  offsetof(VexGuestX86State, guest_FS),
  offsetof(VexGuestX86State, guest_GS),
  offsetof(VexGuestX86State, guest_SS),

  offsetof(VexGuestX86State, guest_LDT),
  offsetof(VexGuestX86State, guest_GDT),

  offsetof(VexGuestX86State, guest_EMNOTE),

  offsetof(VexGuestX86State, guest_CMSTART),
  offsetof(VexGuestX86State, guest_CMLEN)
};

#if 0  // debuging

static uf_name val_uf_tag(UInt tag) {
  if (IS_ZERO_TAG(tag) || IS_SECONDARY_UF_NULL(tag)) {
     return NULL;
  } else {
     return uf_find(GET_UF_OBJECT_PTR(tag));
  }
}

static void dump_function_exit_var_map(DaikonFunctionEntry* funcPtr) {
  int daikonVarIndex;
  UInt var_tag1, var_tag2, var_tag3;
  UInt val_tag1, val_tag2;
  struct genhashtable* var_uf_map;
  struct genhashtable* var_set_map;
  uf_name uf_var1, uf_var2;
  uf_name uf_val1, uf_val2;
  UInt set_number;
  UInt* var_tags;
  int comp_number;

    printf("Function: %s, raw map table:\n", funcPtr->funcEntry.name);
    struct genpointerlist* exit_var_item = funcPtr->ppt_exit_var_uf_map->list;
    while (exit_var_item) {
      uf_object* uf_obj = (uf_object*)(exit_var_item->object);
      if (uf_obj == uf_obj->parent) {
        printf("  %p %8u %4d\n", uf_obj, uf_obj->tag, uf_obj->rank);
      } else {
        uf_object* uf_obj2 = uf_obj;
        int depth = 0;
        while (uf_obj2 != uf_obj2->parent) {
          depth++;
          uf_obj2 = uf_obj2->parent;
        }
        printf("  %p %8u %4d %p %2d %8u\n", uf_obj, uf_obj->tag, uf_obj->rank, uf_obj->parent, depth, uf_obj2->tag);
      }
      exit_var_item = exit_var_item->inext;
    }

    printf("\nFunction: %s, num_vars: %u\n", funcPtr->funcEntry.name, funcPtr->num_exit_daikon_vars);

    var_set_map = genallocatehashtable(NULL, // no hash function needed for u_int keys
                                       (int (*)(void *,void *)) &equivalentIDs);

    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
    set_number = 1;

    for (daikonVarIndex = 0; daikonVarIndex < funcPtr->num_exit_daikon_vars; daikonVarIndex++) {

      var_tag1 = var_tags[daikonVarIndex];
      uf_var1 = var_uf_map_find(var_uf_map, var_tag1);
      if (uf_var1) {
        var_tag2 = uf_var1->tag;
        uf_var2  = uf_find(uf_var1);
        var_tag3 = uf_var2->tag;
      } else {
        var_tag2 = 0;
        uf_var2  = NULL;
        var_tag3 = 0;
      }

      uf_val1 = val_uf_tag(var_tag3);
      if (uf_val1) {
        val_tag1 = uf_val1->tag;
        uf_val2  = uf_find(uf_val1);
        val_tag2 = uf_val2->tag;
      } else {
        val_tag1 = 0;
        uf_val2  = NULL;
        val_tag2 = 0;
      }

      if (0 == var_tag1) {
        comp_number = set_number;
        set_number++;
      }
      else {
        if (gencontains(var_set_map, VoidPtr(val_tag2))) {
          comp_number = (ptrdiff_t)gengettable(var_set_map, VoidPtr(val_tag2));
        }
        else {
          comp_number = set_number;
          set_number++;
          genputtable(var_set_map, VoidPtr(val_tag2), VoidPtr(comp_number));
        }
      }

#if 0
      printf(" var-index: [%d]: set: %d\n", daikonVarIndex, comp_number);
#else
      printf(" var-index: [%d]: var-tag1: %u,\tuf-var1: %p,\tvar-tag2: %u\tset: %d\n",
             daikonVarIndex, var_tag1, uf_var1, var_tag2, comp_number);
      if (var_tag1 != var_tag2) {
          printf("   PROBLEM! var_tag1 != var_tag2\n");
      }
      if (var_tag1 != var_tag3) {
          printf("            [%d]: var-tag1: %u,\tuf-var2: %p,\tvar-tag3: %u\n",
                 daikonVarIndex, var_tag1, uf_var2, var_tag3);
      }
      if (var_tag1 != val_tag1) {
          printf("            [%d]: var-tag1: %u,\tuf-val1: %p,\tval-tag1: %u\n",
                 daikonVarIndex, var_tag1, uf_val1, val_tag1);
      }
      if (val_tag1 != val_tag2) {
          printf("  val_tag2  [%d]: var-tag1: %u,\tuf-val2: %p,\tval-tag2: %u\n",
                 daikonVarIndex, var_tag1, uf_val2, val_tag2);
      }
#endif
    }
    genfreehashtable(var_set_map);
}

static Addr alist[] = {};
static int alist_size = (sizeof alist) / (sizeof alist[0]);

static void dump_all_function_exit_var_map() {
  int i;
  Addr a;

  printf("partial val leaders:\n");
  for (i = 0; i < alist_size; i++) {
    a = alist[i];
    printf("  %p %8u\n", (void*)a, val_uf_find_leader(get_tag(a)));
  }
  printf("\n");

  FuncIterator* funcIt = newFuncIterator();
  while (hasNextFunc(funcIt)) {
    DaikonFunctionEntry* funcPtr = (DaikonFunctionEntry*)nextFunc(funcIt);
    tl_assert(funcPtr);
    dump_function_exit_var_map(funcPtr);
  }
  deleteFuncIterator(funcIt);
}

#endif // debuging

// Pre: the ppt_entry/exit_var_tags array has been updated to reflect
// the changes in the val tag numbers.
// Now we must rebuild the ppt_entry/exit_var_uf_map in a similar
// manner - updating all the var tags to be the new value for the
// corresponding val tags.
static struct genhashtable* regenerate_var_uf_map(UInt num_daikon_vars,
                                                  UInt* ppt_var_tags,
                                                  struct genhashtable* ppt_var_uf_map,
                                                  UInt* p_newTagNumber) {
  UInt ind;
  struct genhashtable* new_var_uf_map =
    genallocateSMALLhashtable((unsigned int (*)(void *)) 0,
                              (int (*)(void *,void *)) &equivalentTags);

  // First, copy new leaders into new map
  for (ind = 0; ind < num_daikon_vars; ind++) {
    UInt leader_tag = ppt_var_tags[ind];
    if (leader_tag && !gencontains(new_var_uf_map, VoidPtr(leader_tag))) {
      //printf("create uf var number: %d\n", ind);
      var_uf_map_insert_and_make_set(new_var_uf_map, leader_tag);
    }
  }

  // Next, copy non-leaders from old map items to new map, updating tags
  struct genpointerlist* current_var_item = ppt_var_uf_map->list;
  while (current_var_item) {
    UInt new_tag;
    UInt new_parent_tag;
    uf_object* uf_obj = (uf_object*)(current_var_item->object);
    // if leader, then already done
    if (uf_obj != uf_obj->parent) {
      //printf("process var map tag: %lu %p %p\n", (long unsigned int)current_var_item->src, uf_obj, uf_obj->parent);
      reassign_tag(&new_tag, val_uf_find_leader(uf_obj->tag), p_newTagNumber);
      // I don't think we need to call reassign_tag, the argument has already
      // been processed in the reasign_tag loop above. The following
      // should work, I will test later.
      // new_parent_tag = g_oldToNewMap[val_uf_find_leader(var_uf_map_find_leader(ppt_var_uf_map, uf_obj->parent->tag))];
      reassign_tag(&new_parent_tag,
                   val_uf_find_leader(var_uf_map_find_leader(ppt_var_uf_map, uf_obj->parent->tag)),
                   p_newTagNumber);
      //printf("new tag: %u, new parent tag: %u\n", new_tag, new_parent_tag);
      var_uf_map_union(new_var_uf_map, new_tag, new_parent_tag);

    }
    current_var_item = current_var_item->inext;
  }

  // Now update the var_tags, as they may no longer be the leader
  // of their var set due to loop above.
  for (ind = 0; ind < num_daikon_vars; ind++) {
    UInt leader_tag = ppt_var_tags[ind];
    if (leader_tag) {
      ppt_var_tags[ind] = var_uf_map_find_leader(new_var_uf_map, leader_tag);
      //printf("update var: %d: %u to %u\n", ind, leader_tag, ppt_var_tags[ind]);
    }
  }

  return new_var_uf_map;
}


// Try to find leaderTag's entry in g_oldToNewMap (map from old tags to
// new tags).  If it does not exist, then write *p_newTagNumber in the
// contents of the address addr and add a new entry to g_oldToNewMap
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
                         UInt* p_newTagNumber) {

  if (g_oldToNewMap[leaderTag]) {
    *addr = g_oldToNewMap[leaderTag];
  }
  else {
    *addr = *p_newTagNumber;
    g_oldToNewMap[leaderTag] = *p_newTagNumber;
    (*p_newTagNumber)++;
  }
  //printf("tag: %u now: %u\n", leaderTag, *addr);
}


// Runs the tag garbage collector
void garbage_collect_tags() {
  UInt primaryIndex, secondaryIndex;
  FuncIterator* funcIt;
  ThreadId currentTID;
  UInt curTag, i;
  UInt* addr;

  Bool dyncomp_trace = dyncomp_print_trace_info;
  dyncomp_print_trace_info = False;

  // Monotonically increases from 1 to whatever is necessary to map
  // old tags to new tags that are as small as possible (held as
  // values in oldToNewMap)
  UInt newTagNumber = 1;

  if (g_oldToNewMap) {
    VG_(free)(g_oldToNewMap);
  }
  g_oldToNewMap = VG_(calloc)("dyncomp_runtime.c: garbage_collect_tags.1 ", (nextTag + 1), sizeof(*g_oldToNewMap));

  printf("  Start garbage collecting (next tag = %u, total assigned = %u)\n",
              nextTag, totalNumTagsAssigned);

  //debug_print_decls();
  //dump_all_function_exit_var_map();

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
  // (Remember that these tags correspond to entries in the individual
  //  var_uf_map union-find data structures associated with each
  //  program point, not just the global val_uf union-find structure.
  //  Thus, the correct thing to do is to first find the leader of each
  //  tag in var_uf_map, and then find the leader of that leader in the
  //  global val_uf union-find.)
  //
  // 3.) Guest state - There is a tag associated with each register
  // (i.e., EAX, EBX, floating-point stack)


  // 1.) Shadow memory:
  for (primaryIndex = 0; primaryIndex < PRIMARY_SIZE; primaryIndex++) {
    if (primary_tag_map[primaryIndex]) {
      //printf("  primary address: %lx\n", ((Addr)primaryIndex) << SECONDARY_SHIFT);
      for (secondaryIndex = 0; secondaryIndex < SECONDARY_SIZE; secondaryIndex++) {
        addr = &primary_tag_map[primaryIndex][secondaryIndex];

        if (*addr) { // Remember to ignore 0 tags
          reassign_tag(addr,
                       val_uf_find_leader(*addr),
                       &newTagNumber);
        }
      }
    }
  }

  // 2.) Per program point:

  // Scan through all of the ppt_entry_var_tags and ppt_exit_var_tags
  // of all program points to see which tags are being held there.

  // First, find the leader of each tag in var_uf_map (specific to that
  // particular program point) and then find the leader of that leader
  // tag in the global val_uf union-find.  It is imperative that we
  // both of these steps or else the garbage collector will not work
  // correctly.  After we have the 'leader of the leader', we can
  // re-assign it to a lower tag number using oldToNewMap.
  funcIt = newFuncIterator();

  dyncomp_print_trace_info = dyncomp_trace;

  while (hasNextFunc(funcIt)) {
    UInt ind;
    DaikonFunctionEntry* cur_entry = (DaikonFunctionEntry*)nextFunc(funcIt);
    tl_assert(cur_entry);

    //dump_function_exit_var_map(cur_entry);
    //printf("compress var map for function: %s\n", cur_entry->funcEntry.name);

    if (dyncomp_separate_entry_exit) {
      for (ind = 0; ind < cur_entry->num_entry_daikon_vars; ind++) {
        UInt* p_entry_tag = &cur_entry->ppt_entry_var_tags[ind];

        if (*p_entry_tag) { // Remember to ignore 0 tags
          reassign_tag(p_entry_tag,
                       // We need to first find the leader in var_uf_map,
                       // then find the leader of that in val_uf:
                       val_uf_find_leader(var_uf_map_find_leader(cur_entry->ppt_entry_var_uf_map, *p_entry_tag)),
                       &newTagNumber);
        }
      }
    }

    for (ind = 0; ind < cur_entry->num_exit_daikon_vars; ind++) {
      UInt* p_exit_tag = &cur_entry->ppt_exit_var_tags[ind];

      if (*p_exit_tag) { // Remember to ignore 0 tags
        //printf("process var number: %d\n", ind);
        reassign_tag(p_exit_tag,
                     // We need to first find the leader in var_uf_map,
                     // then find the leader of that in val_uf:
                     val_uf_find_leader(var_uf_map_find_leader(cur_entry->ppt_exit_var_uf_map, *p_exit_tag)),
                     &newTagNumber);
      }
    }

    // At his point we have updated the tag values in the var_tags array(s).
    // We now need to rebuild the var_uf_map(s) to reflect the updated values.
    if (dyncomp_separate_entry_exit) {
      if (cur_entry->ppt_entry_var_uf_map) {
        struct genhashtable* new_entry_map =
            regenerate_var_uf_map(cur_entry->num_entry_daikon_vars,
                                  cur_entry->ppt_entry_var_tags,
                                  cur_entry->ppt_entry_var_uf_map,
                                  &newTagNumber);
        // free the old map and switch to the new map.
        genfreehashtableandvalues(cur_entry->ppt_entry_var_uf_map);
        cur_entry->ppt_entry_var_uf_map = new_entry_map;
      }
    }

    if (cur_entry->ppt_exit_var_uf_map) {
      struct genhashtable* new_exit_map =
          regenerate_var_uf_map(cur_entry->num_exit_daikon_vars,
                                cur_entry->ppt_exit_var_tags,
                                cur_entry->ppt_exit_var_uf_map,
                                &newTagNumber);
      // free the old map and switch to the new map.
      genfreehashtableandvalues(cur_entry->ppt_exit_var_uf_map);
      cur_entry->ppt_exit_var_uf_map = new_exit_map;
    }

    //dump_function_exit_var_map(cur_entry);
  }

  deleteFuncIterator(funcIt);

  // 3.) Guest state:

  // Scan through all of the guest state and see which tags are being
  // used - these cannot be garbage collected

  // (Remember the offset * 4 hack thing (see do_shadow_PUT_DC() in
  // dyncomp_translate.c) - eek!)

  // Just go through all of the registers in the x86 guest state
  // as depicted in vex/pub/libvex_guest_x86.h
  // (comment added 2007)  
  /* XXX AMD64 support */
  currentTID = VG_(get_running_tid)();

  for (i = 0; i < NUM_TOTAL_X86_OFFSETS; i++) {
    addr =
      VG_(get_tag_ptr_for_guest_offset)(currentTID,
					 x86_guest_state_offsets[i]);
    //printf("  gc shadow addr: %p\n", addr);
    //printf("%u %u %u %u\n", *addr, *(addr+1), *(addr+2), *(addr+3));
    if ((*addr) > 0) {
      reassign_tag(addr,
                   val_uf_find_leader(*addr),
                   &newTagNumber);
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

  printf("   Done garbage collecting (next tag = %u, total assigned = %u)\n",
              nextTag, totalNumTagsAssigned);

  //debug_print_decls();
  //dump_all_function_exit_var_map();
}


/*******************************************************************

 DynComp detailed mode:

 This mode for converting value to variable comparability takes O(n^2)
 time and space but provides better precision than the default mode,
 which takes roughly O(n).  The general idea is to keep a bit-matrix
 at every program point and mark two variables as comparable at a
 program point if at any execution they ever held values that
 interacted (have the same leader tag).

 e.g., for a particular program point, if there are 6 variables,
       then the matrix would look like the following:

    0  1  2  3  4  5

 0     X  X  X  X  X

 1        X  X  X  X

 2           X  X  X

 3              X  X

 4                 X

 5


 For n variables, the maximum number of marks (denoted by 'X') is
 (1/2)*(n^2 - n).  Only the upper triangle needs to be allocated
 because the lower triangle (and diagonal) is redundant information.

 Thus, the densest representation possible is a bit array of size
 (1/2)*(n^2 - n), which can be represented as an array of chars of
 size (((1/2)*(n^2 - n)) / 8) rounded up to the nearest byte.  This is
 represented by the "UChar* ppt_[entry|exit]_bitmatrix" fields inside
 of each DaikonFunctionEntry.

 Bitmatrix Abstraction Function:

 To represent the upper triangle of an n by n matrix, we use a bit
 array of (1/2)*(n^2 - n) elements.  Here is how the mapping works:


    0  1  2  3  4  5 (horizontal entries indexed by j)
   +-----------------
 0 |   0  1  2  3  4
   |
 1 |      5  6  7  8
   |
 2 |         9  10 11
   |
 3 |            12 13
   |
 4 |               14
   |
 5 |

(vertical entries indexed by i)


 The numbers indicate the index in the bitarray that corresponds to
 that spot in the matrix.

     ABSTRACT                      CONCRETE
  bitmatrix[i][j]   <==>   bitarray[((i*n) - (1/2)(i^2+i)) + (j-i-1)]

  where (i < j), 0 <= i < n, 0 <= j < n

  running example:

  n = 6

     i     j      bitarray index
  -----------------------------------
     0     1         0
     0     2         1
     0     3         2
     0     4         3
     0     5         4
     1     2         5
     1     3         6
     1     4         7
     1     5         8
     2     3         9
     2     4         10
     2     5         11
     3     4         12
     3     5         13
     4     5         14

 (g_variableIndex is the running variable index that iterates through
 all n variables, starting at 0 and going up until n - 1.)

*******************************************************************/

// Returns the size (in bytes) of a bit array required to hold the
// upper triangle of an n by n matrix
UInt bitarraySize(UInt n) {
  UInt num_bits = (((n*n) - n)/2);
  UInt num_bytes = num_bits / 8;
  // Round up if necessary:
  if (num_bits % 8) {
    num_bytes++;
  }
  return num_bytes;
}

// Pre: i < j, 0 <= i < n, 0 <= j < n where n is length(bitarray)
// Return: 1 if the (i,j)-th spot in the matrix is marked, 0 otherwise.
char isMarked(UChar* bitarray, UInt n, UInt i, UInt j) {
  UInt idx = ((i*n) - (((i*i)+i)/2)) + (j-i-1);
  UInt bitarray_base = idx / 8;
  UInt bitarray_offset = idx % 8;

  // Remove for performance boost:
  tl_assert((i < j) && (i < n) && (j < n));

  return ((bitarray[bitarray_base] >> bitarray_offset) & 0x1);
}

// Pre: i < j, 0 <= i < n, 0 <= j < n where n is length(bitarray)
// Marks the (i,j)-th spot in the matrix represented by bitarray
void mark(UChar* bitarray, UInt n, UInt i, UInt j) {
  UInt idx = ((i*n) - (((i*i)+i)/2)) + (j-i-1);
  UInt bitarray_base = idx / 8;
  UInt bitarray_offset = idx % 8;
  UChar mask = 1 << bitarray_offset;

  // Remove for performance boost:
  tl_assert((i < j) && (i < n) && (j < n));

  bitarray[bitarray_base] |= mask;
}

// Runs the O(n^2) detailed algorithm to update bitmatrix with X's in
// the appropriate spots to denote variable comparability based on the
// leader tags held in new_tag_leaders:
void DC_detailed_mode_process_ppt_execution(DaikonFunctionEntry* funcPtr,
                                            Bool isEnter) {
  UInt num_daikon_vars;
  UChar* bitmatrix;
  UInt* new_tag_leaders;
  UInt i = 0;
  UInt j = 0;

  tl_assert(dyncomp_detailed_mode);

  // Remember to use only the EXIT structures unless
  // isEnter and --dyncomp-separate-entry-exit are both True
  if (dyncomp_separate_entry_exit && isEnter) {
    bitmatrix = funcPtr->ppt_entry_bitmatrix;
    new_tag_leaders = funcPtr->ppt_entry_new_tag_leaders;
    num_daikon_vars = funcPtr->num_entry_daikon_vars;
  }
  else {
    bitmatrix = funcPtr->ppt_exit_bitmatrix;
    new_tag_leaders = funcPtr->ppt_exit_new_tag_leaders;
    num_daikon_vars = funcPtr->num_exit_daikon_vars;
  }

  DYNCOMP_DPRINTF("  %s (%s): %u\n",
              funcPtr->funcEntry.name,
              isEnter ? "ENTER" : "EXIT",
              num_daikon_vars);

  for (i = 0; i < num_daikon_vars; i++) {
    for (j = i + 1; j < num_daikon_vars; j++) {
      // DON'T COUNT 0 tags!!!
      if ((new_tag_leaders[i] == new_tag_leaders[j]) &&
          (new_tag_leaders[i] != 0)) {
        mark(bitmatrix, num_daikon_vars, i, j);
        DYNCOMP_DPRINTF("    marked: (%u, %u)\n", i, j);
        // Sanity-check ... take out for slight performance boost
        tl_assert(isMarked(bitmatrix, num_daikon_vars, i, j));
      }
    }
  }
}

// This should only be run at the end of execution when we need to
// convert the pairwise variable comparability relations denoted in
// bitmatrix to the (transitive) comparability sets in a format that
// Daikon can comprehend.
// Effects: Allocates var_tags array and populates it with the leaders
// of sets formed by iterating over the pairwise variable relations in
// bitmatrix.
/*
  For example, if the bitmatrix represented the following:

  A  B  C  D  E  F

A    X     X

B             X

C                X

D

E

F

These are the pairwise relations between variables that directly held
comparable values: (A, B), (A, D), (B, E), (C, F)

However, because Daikon expects the variable comparability
relationship to be transitive, we must collapse these pairwise
relations into the following sets:

{A, B, D, E} {C, F}

Notice that we lose a lot of information this way, but Daikon requires
transitivity :(

We will perform this conversion by using an union-find disjoint set
data structure.  We first iterate over all variables and create unique
singleton set entries for each of them (in var_tags).  Then we iterate
over bitmatrix and merge the sets of each pair of variables that
interact.  Finally, we iterate over all variables one more time and
find the leaders of all the tags.

The reason why we store the results in var_tags is so that we can
still use DC_get_comp_number_for_var() to convert into comparability
numbers that we need to output to the .decls file for Daikon.
*/
void DC_convert_bitmatrix_to_sets(DaikonFunctionEntry* funcPtr,
                                  char isEnter) {
  UInt num_daikon_vars;
  UChar* bitmatrix;
  UInt* var_tags;
  UInt var_index = 0;
  UInt i = 0;
  UInt j = 0;

  tl_assert(dyncomp_detailed_mode);

  // Remember to use only the EXIT structures unless
  // isEnter and --dyncomp-separate-entry-exit are both True
  if (dyncomp_separate_entry_exit && isEnter) {
    bitmatrix = funcPtr->ppt_entry_bitmatrix;
    num_daikon_vars = funcPtr->num_entry_daikon_vars;

    if (num_daikon_vars == 0) {
      return;
    }
    funcPtr->ppt_entry_var_tags = VG_(calloc)("dyncomp_runtime.c: DC_convert_bitmatrix_to_sets.1", num_daikon_vars,
                                              sizeof(*(funcPtr->ppt_entry_var_tags)));
    var_tags = funcPtr->ppt_entry_var_tags;
  }
  else {
    bitmatrix = funcPtr->ppt_exit_bitmatrix;
    num_daikon_vars = funcPtr->num_exit_daikon_vars;

    if (num_daikon_vars == 0) {
      return;
    }
    funcPtr->ppt_exit_var_tags = VG_(calloc)("dyncomp_runtime.c: DC_convert_bitmatrix_to_sets.2", num_daikon_vars,
                                             sizeof(*(funcPtr->ppt_exit_var_tags)));
    var_tags = funcPtr->ppt_exit_var_tags;
  }

  // Iterate over all variables and create singleton sets for all of
  // them:
  for (var_index = 0; var_index < num_daikon_vars; var_index++) {
    uf_object* new_obj = VG_(malloc)("dyncomp_runtime.c: DC_convert_bm_to_sets", sizeof(*new_obj));
    uf_make_set(new_obj, var_index);
    // Overload var_tags to hold uf_object* instead of UInt* for now ...
    // shady!
    // (comment added 2013)  
    // HACK ALERT: This isn't right for a 64bit address machine, but
    // apparently 4 bytes produces enough uniqueness for this to work. (markro)
    var_tags[var_index] = (UInt)(ptrdiff_t)(new_obj);
  }

  // Now iterate through all pairs of variables i and j and merge
  // their sets as appropriate:
  for (i = 0; i < num_daikon_vars; i++) {
    for (j = i + 1; j < num_daikon_vars; j++) {
      if (isMarked(bitmatrix, num_daikon_vars, i, j)) {
    // (comment added 2013)  
    // HACK ALERT: see above (markro)
        uf_union((uf_object*)(Addr)var_tags[i], (uf_object*)(Addr)var_tags[j]);
      }
    }
  }

  // Now iterate one more time, find the leaders, and store the
  // leaders' tag in var_tags[], thereby completing the conversion
  // process:
  for (var_index = 0; var_index < num_daikon_vars; var_index++) {
    // (comment added 2013)  
    // HACK ALERT: see above (markro)
    uf_object* cur_obj = (uf_object*)(Addr)(var_tags[var_index]);
    uf_object* leader = uf_find(cur_obj);
    var_tags[var_index] = leader->tag;
  }
}
