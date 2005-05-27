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

    funcPtr->ppt_entry_smallest_tag = UINT_MAX;

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

    funcPtr->ppt_exit_smallest_tag = UINT_MAX;

    if (numDaikonVars > 0) {
      funcPtr->ppt_exit_var_tags =
        VG_(calloc)(numDaikonVars,
                    sizeof(*(funcPtr->ppt_exit_var_tags)));

      funcPtr->ppt_exit_new_tags =
        VG_(calloc)(numDaikonVars,
                    sizeof(*(funcPtr->ppt_exit_new_tags)));
    }
  }
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
  UInt *ppt_smallest_tag_ptr;

  if (isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
    new_tags = funcPtr->ppt_entry_new_tags;
    ppt_smallest_tag_ptr = &(funcPtr->ppt_entry_smallest_tag);
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
    new_tags = funcPtr->ppt_exit_new_tags;
    ppt_smallest_tag_ptr = &(funcPtr->ppt_exit_smallest_tag);
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

  DYNCOMP_DPRINTF(" new_tags[%d]: %u, new_leader: %u, var_tags_v (old): %u, var_tags[%d]: %u (a: %u)\n",
                  daikonVarIndex,
                  new_tags_v,
                  new_leader,
                  var_tags_v,
                  daikonVarIndex,
                  var_tags[daikonVarIndex],
                  a);

  // Ignore tags of zero because they are meaningless
  if ((var_tags[daikonVarIndex] > 0) &&
      (var_tags[daikonVarIndex] < (*ppt_smallest_tag_ptr))) {
    *ppt_smallest_tag_ptr = var_tags[daikonVarIndex];
    //    VG_(printf)("updated smallest_tag: %d\n", (*ppt_smallest_tag_ptr));
  }
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
  UInt *ppt_smallest_tag_ptr;

  if (isEnter) {
    var_uf_map = funcPtr->ppt_entry_var_uf_map;
    var_tags = funcPtr->ppt_entry_var_tags;
    ppt_smallest_tag_ptr = &(funcPtr->ppt_entry_smallest_tag);
  }
  else {
    var_uf_map = funcPtr->ppt_exit_var_uf_map;
    var_tags = funcPtr->ppt_exit_var_tags;
    ppt_smallest_tag_ptr = &(funcPtr->ppt_exit_smallest_tag);
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

  DYNCOMP_DPRINTF(" var_tags_v: %u, leader: %u, var_tags[%d]: %u (final)\n",
                  var_tags_v,
                  leader,
                  daikonVarIndex,
                  var_tags[daikonVarIndex]);

  // Ignore tags of zero because they are meaningless
  if ((var_tags[daikonVarIndex] > 0) &&
      (var_tags[daikonVarIndex] < (*ppt_smallest_tag_ptr))) {
    *ppt_smallest_tag_ptr = var_tags[daikonVarIndex];
    //    VG_(printf)("updated smallest_tag: %d\n", (*ppt_smallest_tag_ptr));
  }
}


// Super-trivial key comparison method -
int equivalentTags(UInt t1, UInt t2) {
  return (t1 == t2);
}


// Return the comparability number for the variable as a SIGNED
// INTEGER (because Daikon expects a signed integer).
// Unless smallest tag for this program point is still equal to
// UINT_MAX, subtract all tags from (smallest tag - 2) in order to
// make them look reasonable.  This ensures that the smallest observed
// tag at this program point will have a comparability number of 2,
// which is DIFFERENT from '1', a reserved tag for hashcodes.

// Reserve the special tag '1' for all hashcode values since
// conceptually, there is only one 'abstract type' of hashcodes
// so all hashcodes should be comparable to one another but not
// to any other Daikon variables.
int DC_get_comp_number_for_var(DaikonFunctionInfo* funcPtr,
                               char isEnter,
                               int daikonVarIndex,
                               char isHashcode) {
  int comp_number = -1;
  UInt *var_tags;
  UInt smallest_tag;


  if (isHashcode) {
    return 1;
  }

  else {
    if (isEnter) {
      var_tags = funcPtr->ppt_entry_var_tags;
      smallest_tag = funcPtr->ppt_entry_smallest_tag;
    }
    else {
      var_tags = funcPtr->ppt_exit_var_tags;
      smallest_tag = funcPtr->ppt_exit_smallest_tag;
    }

    if (UINT_MAX == smallest_tag) {
      comp_number = (int)(var_tags[daikonVarIndex]);
    }
    else {
      // Remember to subtract (smallest_tag - 2) from the tag
      // so that no tag could possibly be the reserved value of '1'
      comp_number = (int)(var_tags[daikonVarIndex] - (smallest_tag - 2));
    }

    // Set all negative comparability numbers to -1 for aesthetic purposes
    if (comp_number < 0) {
      comp_number = -1;
      DYNCOMP_DPRINTF("Warning! Comparability number is negative.\n");
    }

    return comp_number;
  }

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
