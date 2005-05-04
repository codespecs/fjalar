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

#include "dyncomp_runtime.h"
#include "GenericHashtable.h"

// Initialize hash tables for DynComp
// Pre: kvasir_with_dyncomp is active
// TODO: WARNING!  This hashtable-within-hashtable structure may
// blow up in my face and cause a huge memory overload!!!
void allocate_ppt_structures(DaikonFunctionInfo* funcPtr, char isEnter) {
  if (isEnter) {
    funcPtr->ppt_entry_var_tags =
      genallocateSMALLhashtable((unsigned int (*)(void *)) &hashString,
                                (int (*)(void *,void *)) &equivalentStrings);

    funcPtr->ppt_entry_new_tags =
      genallocateSMALLhashtable((unsigned int (*)(void *)) &hashString,
                                (int (*)(void *,void *)) &equivalentStrings);
  }
  else {
    funcPtr->ppt_exit_var_tags =
      genallocateSMALLhashtable((unsigned int (*)(void *)) &hashString,
                                (int (*)(void *,void *)) &equivalentStrings);

    funcPtr->ppt_exit_new_tags =
      genallocateSMALLhashtable((unsigned int (*)(void *)) &hashString,
                                (int (*)(void *,void *)) &equivalentStrings);
  }
}

void destroy_ppt_structures(DaikonFunctionInfo* funcPtr, char isEnter) {
  if (isEnter) {
    genfreehashtable(funcPtr->ppt_entry_var_tags);
    genfreehashtable(funcPtr->ppt_entry_new_tags);
  }
  else {
    genfreehashtable(funcPtr->ppt_exit_var_tags);
    genfreehashtable(funcPtr->ppt_exit_new_tags);
  }
}

// Initialize keys of various program point data structures as strings
// which represent the full Daikon name of the variable and the values
// as malloc'ed 32-bit tags filled with 0 (invalid tag).
// This function will make a copy of the strings.
void initialize_ppt_structures(DaikonFunctionInfo* funcPtr,
                               char isEnter,
                               char* fullDaikonName) {
  struct genhashtable* ppt_var_tags =
    (isEnter ?
     funcPtr->ppt_entry_var_tags :
     funcPtr->ppt_exit_var_tags);

  struct genhashtable* ppt_new_tags =
    (isEnter ?
     funcPtr->ppt_entry_new_tags :
     funcPtr->ppt_exit_new_tags);

  // Add a new entry with a copy of fullDaikonName and a
  // calloc'ed null tag of 0
  char* fullNameCopy = VG_(strdup)(fullDaikonName);

  // Insert it into the hash tables (it should not already exist if all
  // goes well)
  genputtable(ppt_var_tags, (void*)(fullNameCopy),
              (void*)(VG_(calloc)(1, sizeof(UInt))));

  genputtable(ppt_new_tags, (void*)(fullNameCopy),
              (void*)(VG_(calloc)(1, sizeof(UInt))));
  //  VG_(printf)("%s (%d)\n", fullNameCopy, isEnter);
}

// Harvests the tag at location 'a' into the appropriate ppt-specific
// structures for the variable denoted by fullDaikonName
void harvest_new_tag_value(DaikonFunctionInfo* funcPtr,
                           char isEnter,
                           char* fullDaikonName,
                           Addr a) {
  UInt tag = get_tag (a);
  UInt* valuePtr = 0;
  if (isEnter) {
    valuePtr = (UInt*)(gengettable(funcPtr->ppt_entry_new_tags,
                                   (void*)fullDaikonName));
  }
  else {
    valuePtr = (UInt*)(gengettable(funcPtr->ppt_exit_new_tags,
                                   (void*)fullDaikonName));
  }
  *valuePtr = tag;

  VG_(printf)("harvest tag %u into %s (%d)\n",
              tag, fullDaikonName, isEnter);
}

// Performs post-processing after observing a variable's value when
// printing out .dtrace information.  This roughly follows the
// algorithm created by SMcC in the comparability design document.
// (SMcC's pseudo-code is enclosed in SMcC comments)
// Pre: The variable named 'fullDaikonName' located at address 'a'
//      has been observed and the proper tags have been merged in memory
//      (handled in dtrace-output.c)
void DC_post_process_for_variable(DaikonFunctionInfo* funcPtr,
                                  char isEnter,
                                  char* fullDaikonName,
                                  Addr a) {
  UInt leader, new_leader, var_tags_v, new_tags_v;

  // A really important first step is to initialize new_tags[v] by
  // harvesting the tag and assigning it to this variable v:
  harvest_new_tag_value(funcPtr, isEnter, fullDaikonName, a);

  // SMcC:  // Update from any val_uf merges that have occurred
  // SMcC:   tag leader = val_uf.find(var_tags[v]);
  // SMcC:   if (leader != var_tags[v]) {
  // SMcC:     var_tags[v] = var_uf.union(leader, var_tags[v]);
  // SMcC:   }

  // SMcC:   // Make sure there's an entry for the new value
  // SMcC:   tag new_leader = val_uf.find(new_tags[v]);
  // SMcC:   if (!var_uf.exists(new_leader)) {
  // SMcC:     var_uf.make_singleton(new_leader);
  // SMcC:   }

  // SMcC:   // Merge old and new values
  // SMcC:   var_tags[v] = var_uf.union(var_tags[v], new_leader);
}
