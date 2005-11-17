/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_runtime.c:

Contains functions that interact with the Valgrind core after
initialization and provides run-time functionality that is useful for
tools.

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <search.h>
#include <limits.h>

#include "fjalar_main.h"
#include "fjalar_runtime.h"
#include "fjalar_select.h"
#include "generate_fjalar_entries.h"
#include "elf/dwarf2.h"
#include "mc_include.h"

FunctionExecutionState* curFunctionExecutionStatePtr = 0;

// For debug printouts
char within_main_program = 0;

static void updateAllGlobalVariableNames();

// Updates the full fjalar_name for all functions in FunctionTable
// which have C++ mangled names by using the Valgrind VG_(get_fnname)
// function and also updates the trace_vars_tree
void updateAllFunctionEntryNames() {
  extern FunctionTree* vars_tree;
  struct geniterator* it = gengetiterator(FunctionTable);

  while(!it->finished)
    {
      FunctionEntry* cur_entry = (FunctionEntry*)
        gengettable(FunctionTable, gennext(it));

      // Skip to the next entry if this entry is null for some reason

      if (!cur_entry)
        continue;

      // OPTIMIZATION:
      // Don't demangle the name if this entry doesn't have a C++
      // mangled name.  Note that if cur_entry->mangled_name does NOT
      // exist, then cur_entry->fjalar_name has already been
      // initialized much earlier in
      // initializeFunctionTable()
      if (cur_entry->mangled_name) {
        // Let's initialize the full function name right now:
        char* full_fnname = VG_(calloc)(500, sizeof(*full_fnname));

        char *the_class;
        char *buf, *p;

        int full_fnname_len = 0;
        int add_parens;

        VG_(get_fnname)(cur_entry->startPC, full_fnname, 500);

        // Set the demangled_name to the demangled version:
        cur_entry->demangled_name = VG_(strdup)(full_fnname);

        if (cur_entry->isExternal) {
          the_class = ".";
        } else {
          the_class = cur_entry->filename;
        }

        /* We want to print static_fn in subdir/filename.c
           as "subdir/filename.c.static_fn() */
        full_fnname_len = VG_(strlen)(full_fnname);
        // If it's a C function name that does NOT end in ')',
        // then we need to append a "()" onto the end of it
        add_parens = (full_fnname[full_fnname_len - 1] != ')');
        buf = VG_(malloc)(VG_(strlen)(the_class) + 1 +
                          full_fnname_len + (add_parens ? 2 : 0) + 1);
        VG_(strcpy)(buf, the_class);
        for (p = buf; *p; p++) {
          if (!isalpha(*p) && !isdigit(*p) && *p != '.' && *p != '/'
              && *p != '_')
            *p = '_';
        }
        VG_(strcat)(buf, ".");
        VG_(strcat)(buf, full_fnname);

        if (add_parens)
          VG_(strcat)(buf, "()");

        // Important step!  Set the fjalar_name to buf
        cur_entry->fjalar_name = buf;

        //      VG_(printf)("Original name: %s | Valgrind's name: %s | Fjalar name: %s\n",
        //                  cur_entry->name, full_fnname, cur_entry->fjalar_name);

        VG_(free)(full_fnname);
      }


      // See if we are interested in tracing variables for this file,
      // and if so, we must initialize cur_entry->trace_vars_tree
      // appropriately.  We cannot initialize it any earlier because
      // we need to use the Fjalar name of the function to identify
      // its entry in vars_tree, and this is the earliest point where
      // the Fjalar name is guaranteed to be initialized.
      if (fjalar_trace_vars_filename &&
	  (!cur_entry->trace_vars_tree_already_initialized))
	{
	  FunctionTree** foundFuncTree = 0;

	  FunctionTree searchFuncTree;
	  searchFuncTree.function_fjalar_name = cur_entry->fjalar_name;
	  searchFuncTree.function_variables_tree = 0;

	  if ((foundFuncTree =
	       (FunctionTree**)tfind((void*)&searchFuncTree,
				     (void**)&vars_tree,
				     compareFunctionTrees)))
	    {
	      cur_entry->trace_vars_tree = (*foundFuncTree)->function_variables_tree;

	      FJALAR_DPRINTF("FOUND FOUND FOUND!!! - %s\n", (*foundFuncTree)->function_fjalar_name);
	    }
	  else
	    {
	      cur_entry->trace_vars_tree = 0;
	    }
	}
      // No matter what, we've ran it once for this function
      // so trace_vars_tree has been initialized
      cur_entry->trace_vars_tree_already_initialized = 1;

    }

  genfreeiterator(it);

  // Now that the function names have been updated, we can generate
  // full global variable names
  updateAllGlobalVariableNames();
}

// Pre: updateAllFunctionEntryNames() MUST BE RUN before
//      running this function - in fact, it calls this function :)
// Iterates through globalVars and generates a fully-qualified name
// for each global variable so that it's not ambiguous
static void updateAllGlobalVariableNames()
{
  char* globalName = 0;
  char *loc_part; /* Part of the name to specify where the variable came from
		     (doesn't exist in the real language) */
  char *p;

  VarNode* curNode;
  VariableEntry* curVar;

  for (curNode = globalVars.first; curNode != 0; curNode = curNode->next)
    {
      char full_fnname[500];

      curVar = curNode->var;

      tl_assert(curVar->isGlobal);

      // For file static global variables, we are going to append
      // the filename in front of it

      if (curVar->isExternal)
	{
	  /* A leading slash indicates a true global */
	  loc_part = "";
	}
      else
	{
	  loc_part = curVar->fileName;
	}

      /* We want to print static variables in subdir/filename.c
	 as "subdir/filename_c/static_var for globally-declared static variables
	 or as "subdir/filename_c@function_name/static_var for static vars declared within functions
      */
      tl_assert(curVar->name);

      if (curVar->functionStartPC)
	{
	  // Grab the function's demangled name using VG_(get_fnname)
	  VG_(get_fnname)(curVar->functionStartPC, full_fnname, 500);

	  globalName = VG_(calloc)(VG_(strlen)(loc_part) + 1 +
			      VG_(strlen)(full_fnname) + 1 +
			      VG_(strlen)(curVar->name) + 1, sizeof(*globalName));
	}
      else
	{
	  globalName = VG_(calloc)(VG_(strlen)(loc_part) + 1 +
			      VG_(strlen)(curVar->name) + 1, sizeof(*globalName));
	}

      VG_(strcpy)(globalName, loc_part);
      for (p = globalName; *p; p++) {
	if (!isalpha(*p) && !isdigit(*p) && *p != '/' && *p != '_')
	  *p = '_';
      }

      if (curVar->functionStartPC)
	{
	  VG_(strcat)(globalName, "@");
	  VG_(strcat)(globalName, full_fnname);

	  FJALAR_DPRINTF("full_fnname: %s\n", full_fnname);

	  for (p = globalName; *p; p++) {
	    if (!isalpha(*p) && !isdigit(*p) && *p != '/' && *p != '_' && *p != '@')
	      *p = '_';
	  }
	}

      VG_(strcat)(globalName, curVar->name);

      // Assign curVar->name to the newly-formed Fjalar name:
      curVar->name = globalName;
    }
}


// Return a pointer to a FunctionExecutionState which contains the address
// specified by "a" in its stack frame
// Assumes: The stack grows DOWNWARD on x86 Linux so this returns
//          the function entry with the smallest EBP that is HIGHER
//          than "a" and a lowestESP that is LOWER than "a"
// Returns 0 if no function found
static
FunctionExecutionState* returnFunctionExecutionStateWithAddress(Addr a)
{
  Int i;

  FunctionExecutionState* cur_fn = 0;
  FunctionExecutionState* next_fn = 0;

  FJALAR_DPRINTF("Looking for function corresponding "
	  "to stack variable 0x%x\n", a);

  // Traverse the function stack from the function with
  // the highest ESP to the one with the lowest ESP
  // but DON'T LOOK at the function that's the most
  // recent one on the stack yet - hence 0 <= i <= (fn_stack_first_free_index - 2)
  for (i = 0; i <= fn_stack_first_free_index - 2; i++)
    {
      cur_fn = &FunctionExecutionStateStack[i];
      next_fn = &FunctionExecutionStateStack[i + 1];

      if (!cur_fn || !next_fn)
	{
	  VG_(printf)( "Error in returnFunctionExecutionStateWithAddress()");
	  abort();
	}

      // If it is not the most recent function pushed on the stack,
      // then the stack frame of this function lies in between
      // the EBP of that function and the function immediately
      // following it on the stack
      if ((cur_fn->EBP >= a) && (next_fn->EBP <= a)) {
	return cur_fn;
      }
    }

  // If a function hasn't been found yet, now
  // look at the most recent function on the stack:
  // If it is the most recent function on the stack,
  // then the stack frame can only be approximated to lie
  // in between its EBP and lowestESP
  // (this isn't exactly accurate because there are issues
  //  with lowestESP, but at least it'll give us some info.)
  cur_fn = &FunctionExecutionStateStack[fn_stack_first_free_index - 1];

  if ((cur_fn->EBP >= a) && (cur_fn->lowestESP <= a)) {
    return cur_fn;
  }

  FJALAR_DPRINTF("  EXIT FAILURE returnFunctionExecutionStateWithAddress\n");
  return 0;
}

// Tries to find a static array within structVar whose address is within
// range of targetAddr.  The struct's base addr is structVarBaseAddr.
// The return value is the static array variable.
// Remember to recurse on non-pointer struct variables within structVar
// and repeat this same process because they themselves might contain
// static arrays
// *baseAddr = base address of the array variable
// Pre: VAR_IS_STRUCT(structVar)
static VariableEntry* searchForArrayWithinStruct(VariableEntry* structVar,
                                                  Addr structVarBaseAddr,
                                                  Addr targetAddr,
                                                  Addr* baseAddr) {
  VarNode* v = 0;

  for (v = structVar->varType->memberVarList->first;
       v != 0;
       v = v->next) {
    VariableEntry* potentialVar = v->var;

    Addr potentialVarBaseAddr =
      structVarBaseAddr + potentialVar->data_member_location;

    if (potentialVar->isStaticArray &&
        (potentialVarBaseAddr <= targetAddr) &&
        (targetAddr < (potentialVarBaseAddr +
                       (potentialVar->upperBounds[0] *
                        getBytesBetweenElts(potentialVar))))) {
      *baseAddr = potentialVarBaseAddr;
      return potentialVar;
    }
    // Recursive step (be careful to avoid infinite recursion)
    else if VAR_IS_STRUCT(potentialVar) {
      VariableEntry* targetVar =
        searchForArrayWithinStruct(potentialVar,
                                   potentialVarBaseAddr,
                                   targetAddr, baseAddr);

      if (targetVar) {
        return targetVar;
      }
    }
  }

  *baseAddr = 0;
  return 0;
}

// Returns an array or struct variable within varList
// that encompasses the address provided by "a".
// Properties for return value r = &(returnNode.var):
// location(r) <= "a" < location(r) + (r->upperBounds[0] * getBytesBetweenElts(r))
//   [if array]
// location(r) <= "a" < location(r) + (getBytesBetweenElts(r))
//   [if struct]
// where location(.) is the global location if isGlobal and stack location
// based on EBP if !isGlobal
// *baseAddr = the base address of the variable returned
static VariableEntry*
returnArrayVariableWithAddr(VarList* varList,
                            Addr a,
                            char isGlobal,
                            Addr EBP,
                            Addr* baseAddr) {
  VarNode* cur_node = 0;

  for (cur_node = varList->first;
       cur_node != 0;
       cur_node = cur_node->next) {
    VariableEntry* potentialVar = cur_node->var;
    Addr potentialVarBaseAddr = 0;

    if (!potentialVar)
      continue;

    if (isGlobal) {
      potentialVarBaseAddr = potentialVar->globalLocation;
    }
    else {
      potentialVarBaseAddr = EBP + potentialVar->byteOffset;
    }

    // array
    if (potentialVar->isStaticArray &&
        (potentialVarBaseAddr <= a) &&
        (a < (potentialVarBaseAddr + (potentialVar->upperBounds[0] *
                                      getBytesBetweenElts(potentialVar))))) {
      *baseAddr = potentialVarBaseAddr;
      return potentialVar;
    }
    // struct
    else if (VAR_IS_STRUCT(potentialVar) &&
             (potentialVarBaseAddr <= a) &&
             (a < (potentialVarBaseAddr + getBytesBetweenElts(potentialVar)))) {
      return searchForArrayWithinStruct(potentialVar,
                                        potentialVarBaseAddr,
                                        a, baseAddr);
    }
  }

  *baseAddr = 0;
  return 0;
}

// Return a single global variable, not an array, which matches the supplied
// address if any. When pointed to, such a variable can be treated as
// a 1-element array of its type.
VariableEntry* returnGlobalSingletonWithAddress(Addr a) {
  VarNode* cur_node = 0;
  VariableEntry* r = 0;
  FJALAR_DPRINTF(" in returnGlobalSingletonWithAddress\n");
  for (cur_node = globalVars.first; cur_node != 0; cur_node = cur_node->next)
    {
      r = cur_node->var;

      if (!r)
	continue;

      if (r->isGlobal && !r->isStaticArray && r->globalLocation == a)
        {
	  FJALAR_DPRINTF(" EXIT SUCCESS returnGlobalSingletonWithAddress - %s\n", r->name);
          return r;
        }
    }
  FJALAR_DPRINTF(" EXIT FAILURE returnGlobalSingletonWithAddress\n");
  return 0;
}


// Takes a pointer to a variable of size typeSize starting at startAddr
// and probes ahead to see how many contiguous blocks of memory are allocated
// (using memcheck check_writable()) for that variable starting at startAddr.
// This is used to determine whether a pointer points to one variable
// (return 1) or whether it points to an array (return > 1).
// We can use this function to determine the array size at runtime
// so that we can properly output the variable as either a single
// variable or an array
// NOTE!  If you pass a pointer to the MIDDLE of an array as startAddr,
// this function will return the number of entries in the array AFTER
// the pointer since it only probes AHEAD and NOT BEHIND!
//
// This is very flaky!!!  It only works properly for heap allocated
// arrays since the stack and global space contain lots of squished-together
// contiguous variables
//
// Now we do a two-pass approach which first goes FORWARD until it
// hits a set of bytes of size typeSize whose A-bits are all unset and
// then BACKWARDS until it hits the first set of bytes of size
// typeSize with at least ONE byte whose V-bit is SET.  This avoids
// printing out large chunks of garbage values when most elements of
// an array are uninitialized.  For example, this function will return
// 10 for an int array allocated to hold 1000 elements but only with
// the first 10 elements initialized.
int probeAheadDiscoverHeapArraySize(Addr startAddr, UInt typeSize)
{
  int arraySize = 0;
  /*tl_assert(typeSize > 0);*/
  if (typeSize == 0)
    return 0;
  while (mc_check_writable( startAddr, typeSize, 0))
    {
      if (fjalar_debug)
	{
	  if (arraySize % 1000 == 0)
	    VG_(printf)( "Made it to %d elements at 0x%x\n", arraySize,
		    startAddr);
	}
      /* Cut off the search if we can already see it's really big:
         no need to look further than we're going to print. */
      if (fjalar_array_length_limit != -1 &&
          arraySize > fjalar_array_length_limit)
        break;

      arraySize++;
      startAddr+=typeSize;
    }

  startAddr -= typeSize;
  // Now do a SECOND pass and probe BACKWARDS until we reach the
  // first set of bytes with at least one byte whose V-bit is SET
  while ((arraySize > 0) &&
         // If at least ONE byte within the element (struct or
         // primitive) of size typeSize is initialized, then consider
         // the entire element to be initialized.  This is done
         // because sometimes only certain members of a struct are
         // initialized, and if we perform the more stringent check
         // for whether ALL members are initialized, then we will
         // falsely mark partially-initialized structs as
         // uninitialized and lose information.  For instance,
         // consider struct point{int x; int y;} - Let's say you had
         // struct point foo[10] and initialized only the 'x' member
         // var. in every element of foo (foo[0].x, foo[1].x, etc...)
         // but left the 'y' member var uninitialized.  Every element
         // of foo has typeSize = 2 * sizeof(int) = 8, but only the
         // first 4 bytes are initialized ('x') while the last 4 are
         // uninitialized ('y').  This function should return 10 for
         // the size of foo, so it must mark each element as
         // initialized when at least ONE byte is initialized (in this
         // case, a byte within 'x').
         !MC_(are_some_bytes_initialized)(startAddr, typeSize, 0)) {
    arraySize--;
    startAddr-=typeSize;
  }

  return arraySize;
}

// Return the number of bytes between elements of this variable
// if it were used as an array
int getBytesBetweenElts(VariableEntry* var)
{
  tl_assert(var);

  if (var->ptrLevels > 1)
    {
      FJALAR_DPRINTF("getBytesBetweenElts returning sizeof(void*) (%d)\n",
              sizeof(void*));
      return sizeof(void*);
    }
  else
    {
      FJALAR_DPRINTF("getBytesBetweenElts returning %d\n", var->varType->byteSize);
      return var->varType->byteSize;
    }
}


// Takes a location and a VariableEntry and tries to determine
// the UPPER BOUND of the array which the pointer refers to.
// CAUTION: This function is still fairly primitive and untested
//
// This now uses a two-pass scheme which first searches to the end of the
// array and then goes backwards until it finds the first byte whose V-bit
// is valid so that it can avoid printing out tons of garbage values and
// cluttering up the .dtrace file.
//
// This also now has support to find statically-sized arrays within structs
// declared as global and local variables as well as statically-sized arrays
// which are themselves global and local variables
int returnArrayUpperBoundFromPtr(VariableEntry* var, Addr varLocation)
{
  VariableEntry* targetVar = 0;
  Addr baseAddr = 0;
  char foundGlobalArrayVariable = 0;

  FJALAR_DPRINTF("Checking for upper bound of %p\n", varLocation);

  // 1. Search if varLocation is within a global variable
  targetVar = returnArrayVariableWithAddr(&globalVars,
                                          varLocation,
                                          1, 0, &baseAddr);

  if (targetVar) {
    foundGlobalArrayVariable = 1;
  }
  else {
    targetVar = returnGlobalSingletonWithAddress(varLocation);
    if (targetVar) {
      return 0;
    }
  }

  // 2. If not found, then search if varLocation is within the stack
  //    frame of a function currently on the stack
  if (!targetVar) {
    FunctionExecutionState* e;
    FJALAR_DPRINTF("Not found in globals area, checking on stack\n");

    e = returnFunctionExecutionStateWithAddress(varLocation);

    FJALAR_DPRINTF("Found function entry %p\n", e);

    if (e) {
      VarList* localArrayAndStructVars = &(e->func->localArrayAndStructVars);

      // TODO: Try to get to the bottom of this problem of bogus
      // localArrayAndStructVars pointers, but for now, let's just mask it
      // so that Fjalar runs without crashing:
      // assert(!localArrayAndStructVars || (unsigned int)localArrayAndStructVars > 0x100);

      if (localArrayAndStructVars &&
          // hopefully ensures that it's not totally bogus
          ((unsigned int)localArrayAndStructVars > 0x100) &&
          (localArrayAndStructVars->numVars > 0)) {
        targetVar = returnArrayVariableWithAddr(localArrayAndStructVars,
                                                varLocation,
                                                0, e->EBP, &baseAddr);
      }
    }
  }

  // 3. If still not found, then search the heap for varLocation
  //    if it is lower than the current EBP
  // This is a last-ditch desperation attempt and won't yield valid-looking
  // results in cases like when you have a pointer to an int which is located
  // within a struct malloc'ed on the heap.
  if (!targetVar) {
    FJALAR_DPRINTF("Not found on stack, checking in heap\n");

    tl_assert(curFunctionExecutionStatePtr);

    // Make sure the address is not in the stack or global region
    // before probing so that we don't accidentally make a mistake
    // where we erroneously conclude that the array size is HUGE
    // since all areas on the stack and global regions are ALLOCATED
    // so probing won't do us much good
    if ((varLocation < curFunctionExecutionStatePtr->EBP) &&
        (varLocation > highestGlobalVarAddr)) {
      int size;
      FJALAR_DPRINTF("Location looks reasonable, probing at %p\n",
              varLocation);

      size =
        probeAheadDiscoverHeapArraySize(varLocation,
                                        getBytesBetweenElts(var));

      // We want an upper-bound on the array, not the actual size
      if (size > 0)
        return (size - 1);
      else
        return 0;
    }
  }
  // This is a less strict match which only compares rep. types
  // ... we will do more checking later to really determine the relative sizes.
  // This leniency allows an int* to reference a char[] and so forth ...
  // see below for translation
  //  else if (baseAddr &&
	   //           (targetVar->varType->repType == var->varType->repType)) {

  // TODO: Hmmmm, what are we gonna do without repTypes???  I need to
  // investigate this 'if' condition more carefully later:
  else if (baseAddr) {
    int targetVarSize = 0;
    int bytesBetweenElts = getBytesBetweenElts(targetVar);

    unsigned int highestAddr = baseAddr +
      (targetVar->upperBounds[0] * bytesBetweenElts);

    // NEW!: Probe backwards until you find the first address whose V-bit is SET:
    // but ONLY do this for globals and NOT for stuff on the stack because
    // V-bits for stack variables are FLAKY!!!  During function exit, all the V-bits
    // are wiped out :(

    if (foundGlobalArrayVariable) {
      while ((highestAddr > varLocation) &&
             (fjalar_use_bit_level_precision ?
              (!MC_(are_some_bytes_initialized)(highestAddr, bytesBetweenElts, 0)) :
              (MC_Ok != mc_check_readable(highestAddr, bytesBetweenElts, 0)))) {
        highestAddr -= bytesBetweenElts;
      }
    }

    // This is IMPORTANT that we subtract from varLocation RATHER than baseAddr
    // because of the fact that varLocation can point to the MIDDLE of an array
    targetVarSize = (highestAddr - varLocation) / bytesBetweenElts;

    // Now translate based on relative sizes of var->varType and
    // targetVar->varType, making sure to only do INTEGER operations:
    if (targetVar->varType->byteSize == var->varType->byteSize) {
      return targetVarSize;
    }
    // FLAKY!  Assumes that the ratios always divide evenly ...
    // I think we're okay though because byteSize = {1, 2, 4, 8}
    else if (targetVar->varType->byteSize > var->varType->byteSize) {
      return (targetVarSize * var->varType->byteSize) / targetVar->varType->byteSize;
    }
    else {
      return (targetVarSize * targetVar->varType->byteSize) / var->varType->byteSize;
    }
  }

  return 0;
}

// Checks if numBytes that this address points to has been allocated
// and is thus safe to dereference or readable and thus contains
// valid data
// allocatedOrInitialized = 1 - checks for allocated (A-bits)
// allocatedOrInitialized = 0 - checks for initialized (V-bits)
char addressIsAllocatedOrInitialized(Addr addressInQuestion, unsigned int numBytes, char allocatedOrInitialized)
{
  // Everything on the stack frame of the current function IN BETWEEN
  // the function's EBP and the lowestESP is OFF THE HOOK!!!
  // We treat this as allocated automatically since the function has
  // actually explicitly allocated this on the stack at one time
  // or another, even though at function exit time, it's bad because
  // the ESP increments back up near EBP:
  // The reason why we need this check is that during function exit time,
  // Valgrind marks that function's stack frame as invalid even though
  // it's technically still valid at the moment we exit because
  // nothing else has had time to touch it yet

  // TODO: The problem with this is that, although everything in this range
  //       should be allocate (A-bits), not everything in this range is
  //       initialized (V-bits) but we are ASSUMING that it is!!!
  //       In order to get initialization information, we will need to make
  //       a copy of the V-bits and store them with the function
  int wraparound = ((addressInQuestion + numBytes) < addressInQuestion);
  if ((curFunctionExecutionStatePtr && !wraparound &&
       ((addressInQuestion + numBytes) <= curFunctionExecutionStatePtr->EBP) &&
       (addressInQuestion >= curFunctionExecutionStatePtr->lowestESP)))
    {
      tl_assert(addressInQuestion != 0xffffffff);
      return 1;
    }
  else
  {
      if (allocatedOrInitialized)
	{
	  return mc_check_writable(addressInQuestion, numBytes, 0);
	}
      else
	{
          // Notice that the return type of mc_check_readable has
          // changed from the Valgrind 2.X Memcheck:
	  return (MC_Ok == mc_check_readable(addressInQuestion, numBytes, 0));
	}
  }
}


/* Set the buffer for a file handle to a VG_(malloc)ed block, rather than
 * a glibc-malloced one as it would otherwise be. On some systems (e.g.,
 * Red Hat 9 ones) this seems to work around a bug where the two mallocs
 * both think they own an area of memory. It would be better if we could
 * fix the underlying bug, though. */
void fixBuffering(FILE *fp) {
  char *buffer = VG_(malloc)(8192);
  if (setvbuf(fp, buffer, _IOFBF, 8192)) {
     VG_(printf)("setvbuf failed\n");
  }
}
