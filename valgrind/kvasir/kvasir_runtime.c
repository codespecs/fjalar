/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* kvasir_runtime.c:
   Performs runtime analysis of variables in memory to generate .dtrace file.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <search.h>
#include <limits.h>

#include "kvasir_runtime.h"
#include "generate_daikon_data.h"
#include "dyncomp_runtime.h"
#include "dtrace-output.h"
#include "decls-output.h"
#include "elf/dwarf2.h"
#include "mc_include.h"

// from kvasir_main.c
extern FunctionEntry fn_stack[];
extern Int fn_stack_top;

static char atLeastOneFunctionHandled = 0;

FunctionEntry* currentFunctionEntryPtr = 0;

// For debug printouts
char within_main_program = 0;

// Updates the full daikon_name for all functions in DaikonFunctionInfoTable
// by using the Valgrind VG_(get_fnname) function
// and also updates the trace_vars_tree
void updateAllDaikonFunctionInfoEntries()
{
  extern FunctionTree* vars_tree;
  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);

  while(!it->finished)
    {
      DaikonFunctionInfo* cur_entry = (DaikonFunctionInfo*)
        gengettable(DaikonFunctionInfoTable, gennext(it));

      if (!cur_entry)
        continue;

      // Let's initialize the full Daikon function name right now:
      char* full_fnname = VG_(calloc)(500, sizeof(*full_fnname));

      char *the_class; /* What Daikon will think of as the
			  "class" part of the PPT name */
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

//      VG_(printf)("Original name: %s | Valgrind's name: %s\n",
//                  cur_entry->name, full_fnname);

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

      // Important step!  Set the daikon name to buf
      cur_entry->daikon_name = buf;

      VG_(free)(full_fnname);

      // See if we are interested in tracing variables for this file,
      // and if so, we must initialize cur_entry->trace_vars_tree
      // appropriately
      if (kvasir_trace_vars_filename &&
	  (!cur_entry->trace_vars_tree_already_initialized))
	{
	  FunctionTree** foundFuncTree = 0;

	  FunctionTree searchFuncTree;
	  searchFuncTree.function_daikon_name = cur_entry->daikon_name;
	  searchFuncTree.function_variables_tree = 0;

	  if ((foundFuncTree =
	       (FunctionTree**)tfind((void*)&searchFuncTree,
				     (void**)&vars_tree,
				     compareFunctionTrees)))
	    {
	      cur_entry->trace_vars_tree = (*foundFuncTree)->function_variables_tree;

	      DPRINTF("FOUND FOUND FOUND!!! - %s\n", (*foundFuncTree)->function_daikon_name);
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

// Pre: updateAllDaikonFunctionInfoEntries MUST BE RUN before
//      running this function - in fact, it calls this function :)
// Iterates through globalVars and generates a fully-qualified Daikon name
// for each global variable so that it's not ambiguous
void updateAllGlobalVariableNames()
{
  char* globalName = 0;
  char *loc_part; /* Part of the name to specify where the variable came from
		     (doesn't exist in the real language) */
  char *p;

  VarNode* curNode;
  DaikonVariable* curVar;

  for (curNode = globalVars.first; curNode != 0; curNode = curNode->next)
    {
      char full_fnname[500];

      curVar = &(curNode->var);

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

	  DPRINTF("full_fnname: %s\n", full_fnname);

	  for (p = globalName; *p; p++) {
	    if (!isalpha(*p) && !isdigit(*p) && *p != '/' && *p != '_' && *p != '@')
	      *p = '_';
	  }
	}

      VG_(strcat)(globalName, "/");
      VG_(strcat)(globalName, curVar->name);

      // Assign curVar->name to the newly-formed Daikon name:
      curVar->name = globalName;
    }
}

// The main file calls this whenever it enters a function
// DO NOT MODIFY e - its value will NOT be placed in the stack - see push_fn()
// TODO: --- ummm, is this still true now?  I dunno.
void handleFunctionEntrance(FunctionEntry* e)
{
  DaikonFunctionInfo* daikonFuncPtr;

  // If it's the first time you've ever handled a function entrance,
  // then you better run outputDeclsAndCloseFile so that Kvasir
  // can take advantage of all of Valgrind's name demangling functionality
  // while still producing a complete .decls file before the .dtrace file
  // in order to allow streaming feeds into Daikon:
  if (!atLeastOneFunctionHandled)
    {
      // Remember to not actually output the .decls right now when
      // we're running DynComp.  We need to wait until the end to
      // actually output .decls, but we need to make a fake run in
      // order to set up the proper data structures
      outputDeclsFile(kvasir_with_dyncomp);

      if (actually_output_separate_decls_dtrace && !dyncomp_without_dtrace) {
	openTheDtraceFile();
      }

      atLeastOneFunctionHandled = 1;
    }

  if (VG_(strcmp)(e->name, "main") == 0) {
    within_main_program = 1;
  }

  // Don't forget to initialize the function's full Daikon filename here :)
  // The full name is not initialized until runtime!!!
  daikonFuncPtr = findFunctionInfoByAddr(e->startPC);

  if (!daikonFuncPtr)
    {
      VG_(printf)("Couldn't find function %s\n", e->name);
      return;
    }

  DYNCOMP_DPRINTF("***ENTER %s at EBP=0x%x, lowestESP=0x%x, startPC=%p\n",
                  e->name,
                  e->EBP,
                  e->lowestESP,
                  (void*)e->startPC);

  debugPrintTagsInRange(e->EBP - 50, e->EBP + 50);

  if (daikonFuncPtr->parentClass) {
    DPRINTF("   --- member function - parent is %s\n",
                daikonFuncPtr->parentClass->collectionName);
  }

  // Avoid running okayToPrintThisProgramPoint if you can
  if((daikonFuncPtr->okayToPrintAlreadyInitialized &&
      !daikonFuncPtr->okayToPrint) ||
     !okayToPrintThisProgramPoint(daikonFuncPtr))
    {
      return;
    }

  // Reset this properly!
  g_daikonVarIndex = 0;

  currentFunctionEntryPtr = e;

  DPRINTF("About to outputFormalParamsAndGlobals for %s\n", e->name);

  outputFormalParamsAndGlobals(e, daikonFuncPtr, 1);

  // Mike said that OBJECT/CLASS PPTs in .dtrace is ignored altogether
  // so don't bother to output it:
  //  outputObjectAndClassPPTs(e, daikonFuncPtr, 1);
  //  currentFunctionEntryPtr = 0;

  DPRINTF("\n");

  //  printf("Function entrance: %s\n\n", e->name);
  //  printFunctionEntryStack();
  //  printf("\n");
}

// The main file calls this whenever it exits a function
void handleFunctionExit(FunctionEntry* e)
{
  DaikonFunctionInfo* daikonFuncPtr;

  daikonFuncPtr = findFunctionInfoByAddr(e->startPC);

  if (!daikonFuncPtr)
    {
      VG_(printf)("Couldn't find function %s\n", e->name);
      return;
    }

  DYNCOMP_DPRINTF("***EXIT %s - EBP=0x%x, lowestESP=0x%x\n",
                  e->name,
                  e->EBP,
                  e->lowestESP);

  debugPrintTagsInRange(e->EBP - 50, e->EBP + 50);

  if (daikonFuncPtr->parentClass) {
    DPRINTF("   --- member function - parent is %s\n",
                daikonFuncPtr->parentClass->collectionName);
  }

  // Avoid running okayToPrintThisProgramPoint if you can
  if((daikonFuncPtr->okayToPrintAlreadyInitialized &&
      !daikonFuncPtr->okayToPrint) ||
     !okayToPrintThisProgramPoint(daikonFuncPtr))
    {
      return;
    }

  // Reset this properly!
  g_daikonVarIndex = 0;

  currentFunctionEntryPtr = e;

  outputFormalParamsAndGlobals(e, daikonFuncPtr, 0);
  outputReturnValue(e, daikonFuncPtr);

  // Mike said that OBJECT/CLASS PPTs in .dtrace is ignored altogether
  // so don't bother to output it:
  //  outputObjectAndClassPPTs(e, daikonFuncPtr, 0);

  //  currentFunctionEntryPtr = 0;

  DPRINTF("\n");

  //  printf("Function exit: %s\n\n", e->name);
  //  printFunctionEntryStack();
  //  printf("\n");

  if (VG_(strcmp)(e->name, "main") == 0) {
    within_main_program = 0;
  }
}


// This is the part where we decide whether to even print out the
// entries for this program point based on comparisons with strings
// in prog_pts_tree and whether kvasir_trace_prog_pts_filename is valid:
char okayToPrintThisProgramPoint(DaikonFunctionInfo* daikonFuncPtr)
{
  extern char* prog_pts_tree;

  if (kvasir_trace_prog_pts_filename)
    {
      // It's only okay if the function's full daikon name is found in prog_pts_tree
      if (tfind((void*)daikonFuncPtr->daikon_name, (void**)&prog_pts_tree, compareStrings))
	{
	  daikonFuncPtr->okayToPrint = 1;
	  daikonFuncPtr->okayToPrintAlreadyInitialized = 1;
	  return 1;
	}
      else
	{
	  daikonFuncPtr->okayToPrint = 0;
	  daikonFuncPtr->okayToPrintAlreadyInitialized = 1;
	  return 0;
	}
    }
  // It's always okay to print program point if kvasir_trace_prog_pts_filename is not valid
  else
    {
      daikonFuncPtr->okayToPrint = 1;
      daikonFuncPtr->okayToPrintAlreadyInitialized = 1;
      return 1;
    }
}

// Return a pointer to a FunctionEntry which contains the address
// specified by "a" in its stack frame
// Assumes: The stack grows DOWNWARD on x86 Linux so this returns
//          the function entry with the smallest EBP that is HIGHER
//          than "a" and a lowestESP that is LOWER than "a"
// Returns 0 if no function found
FunctionEntry* returnFunctionEntryWithAddress(Addr a)
{
  Int i;

  FunctionEntry* cur_fn = 0;
  FunctionEntry* next_fn = 0;

  DPRINTF("Looking for function corresponding "
	  "to stack variable 0x%x\n", a);

  // Traverse the function stack from the function with
  // the highest ESP to the one with the lowest ESP
  // but DON'T LOOK at the function that's the most
  // recent one on the stack yet - hence 0 <= i <= (fn_stack_top - 2)
  for (i = 0; i <= fn_stack_top - 2; i++)
    {
      cur_fn = &fn_stack[i];
      next_fn = &fn_stack[i + 1];

      if (!cur_fn || !next_fn)
	{
	  VG_(printf)( "Error in returnFunctionEntryWithAddress()");
	  abort();
	}

      DPRINTF("fn_stack[%d] - %s - EBP: %p\n",
	      i, cur_fn->name, (void*)cur_fn->EBP);

      // If it is not the most recent function pushed on the stack,
      // then the stack frame of this function lies in between
      // the EBP of that function and the function immediately
      // following it on the stack
      if ((cur_fn->EBP >= a) && (next_fn->EBP <= a)) {
	DPRINTF("  EXIT SUCCESS "
		"returnFunctionEntryWithAddress - %s\n", cur_fn->name);

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
  cur_fn = &fn_stack[fn_stack_top - 1];

  if ((cur_fn->EBP >= a) && (cur_fn->lowestESP <= a)) {
    DPRINTF("  EXIT SUCCESS "
	    "returnFunctionEntryWithAddress - %s\n", cur_fn->name);

    return cur_fn;
  }

  DPRINTF("  EXIT FAILURE returnFunctionEntryWithAddress\n");
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
static DaikonVariable* searchForArrayWithinStruct(DaikonVariable* structVar,
                                                  Addr structVarBaseAddr,
                                                  Addr targetAddr,
                                                  Addr* baseAddr) {
  VarNode* v = 0;

  for (v = structVar->varType->memberListPtr->first;
       v != 0;
       v = v->next) {
    DaikonVariable* potentialVar = &(v->var);

    Addr potentialVarBaseAddr =
      structVarBaseAddr + potentialVar->data_member_location;

    if (VAR_IS_STATIC_ARRAY(potentialVar) &&
        (potentialVarBaseAddr <= targetAddr) &&
        (targetAddr < (potentialVarBaseAddr +
                       (potentialVar->upperBounds[0] *
                        getBytesBetweenElts(potentialVar))))) {
      *baseAddr = potentialVarBaseAddr;
      return potentialVar;
    }
    // Recursive step (be careful to avoid infinite recursion)
    else if VAR_IS_STRUCT(potentialVar) {
      DaikonVariable* targetVar =
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
static DaikonVariable*
returnArrayVariableWithAddr(VarList* varList,
                            Addr a,
                            char isGlobal,
                            Addr EBP,
                            Addr* baseAddr) {
  VarNode* cur_node = 0;

  for (cur_node = varList->first;
       cur_node != 0;
       cur_node = cur_node->next) {
    DaikonVariable* potentialVar = &(cur_node->var);
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
    if (VAR_IS_STATIC_ARRAY(potentialVar) &&
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
DaikonVariable* returnGlobalSingletonWithAddress(Addr a) {
  VarNode* cur_node = 0;
  DaikonVariable* r = 0;
  DPRINTF(" in returnGlobalSingletonWithAddress\n");
  for (cur_node = globalVars.first; cur_node != 0; cur_node = cur_node->next)
    {
      r = &(cur_node->var);

      if (!r)
	continue;

      if (r->isGlobal && !r->isStaticArray && r->globalLocation == a)
        {
	  DPRINTF(" EXIT SUCCESS returnGlobalSingletonWithAddress - %s\n", r->name);
          return r;
        }
    }
  DPRINTF(" EXIT FAILURE returnGlobalSingletonWithAddress\n");
  return 0;
}


// isEnter = 1 for function ENTER, 0 for EXIT
void outputFormalParamsAndGlobals(FunctionEntry* e, DaikonFunctionInfo* daikonFuncPtr, char isEnter)
{
  DPRINTF("In outputFormalParamsAndGlobals\n");

  // Error! Function not found
  if (!daikonFuncPtr)
    return;

  // Print out function header

  if (!dyncomp_without_dtrace) {
    printDtraceFunctionHeader(daikonFuncPtr, isEnter);
  }

  DPRINTF("About to print globals\n");

  // Print out globals
  if (!kvasir_ignore_globals)
    {
      extern FunctionTree* globalFunctionTree;

      printVariablesInVarList(daikonFuncPtr, isEnter, GLOBAL_VAR, 0, DTRACE_FILE, 0,
			      (globalFunctionTree ?
			       globalFunctionTree->function_variables_tree : 0), 0, 0);
    }

  DPRINTF("Now printing parameters\n");

  // Print out formal params
  printVariablesInVarList(daikonFuncPtr, isEnter,
			  (isEnter ?
			   FUNCTION_ENTER_FORMAL_PARAM :
			   FUNCTION_EXIT_FORMAL_PARAM),
			  e->virtualStack, DTRACE_FILE, 0,
			  daikonFuncPtr->trace_vars_tree, 0, 0);
}

// isEnter = 1 for function ENTER, 0 for EXIT
void outputObjectAndClassPPTs(FunctionEntry* e, DaikonFunctionInfo* daikonFuncPtr, char isEnter) {
  if (daikonFuncPtr->parentClass &&
      daikonFuncPtr->parentClass->collectionName &&
      ((0 == daikonFuncPtr->accessibility) || // 0 or 1 means public
       (1 == daikonFuncPtr->accessibility))) { // is a member function
    // Print a :::OBJECT program point iff it is a NON-STATIC PUBLIC
    //  member function with "this" as its first parameter
    // Check to see if there is at least one parameter and the first one is named "this"
    extern FILE* dtrace_fp;
    extern FunctionTree* globalFunctionTree;
    VarNode* first = daikonFuncPtr->formalParameters.first;

    if (first) {
      DaikonVariable* var = &(first->var);

      if (var && VG_STREQ(var->name, "this")) {

        if (!dyncomp_without_dtrace) {
          fputs("\n", dtrace_fp);
          fputs(daikonFuncPtr->parentClass->collectionName, dtrace_fp);
          fputs(":::OBJECT\n", dtrace_fp);
        }

        printVariablesInVarList(daikonFuncPtr, isEnter, // TODO: Hmmm, this may be a problem because in decls-output.c:printAllObjectAndClassDecls(), I always set 'isEnter' to 1
                                (isEnter ?
                                 FUNCTION_ENTER_FORMAL_PARAM :
                                 FUNCTION_EXIT_FORMAL_PARAM),
                                e->virtualStack, DTRACE_FILE, 0,
                                daikonFuncPtr->trace_vars_tree, 0, 1);
      }
    }

    // Print a :::CLASS program point iff it is a PUBLIC
    // member function
    if (!dyncomp_without_dtrace) {
      fputs("\n", dtrace_fp);
      fputs(daikonFuncPtr->parentClass->collectionName, dtrace_fp);
      fputs(":::CLASS\n", dtrace_fp);
    }

    printVariablesInVarList(daikonFuncPtr, isEnter, // TODO: Hmmm, this may be a problem because in decls-output.c:printAllObjectAndClassDecls(), I always set 'isEnter' to 1
                            GLOBAL_VAR, 0, DTRACE_FILE, 0,
			      (globalFunctionTree ?
			       globalFunctionTree->function_variables_tree : 0), 1, 0);
  }
}

// Treat all return values as "initialized", at least
// at the very top layer
void outputReturnValue(FunctionEntry* e, DaikonFunctionInfo* daikonFuncPtr)
{
  VarNode* cur_node;

  // From decls-output.c:
  // The stack which represents the full name of the variable
  // that we currently want to print out
  extern char* fullNameStack[];
  extern int fullNameStackSize;

  // Error! Function not found
  if (!daikonFuncPtr)
    return;

  // We need to push the return value name onto the string stack!
  stringStackClear(&fullNameStackSize);

  cur_node = daikonFuncPtr->returnValue.first;

  if (!cur_node)
    return;

  stringStackPush(fullNameStack, &fullNameStackSize, cur_node->var.name);

  // Struct/union type - use EAX but remember that EAX holds
  // a POINTER to the struct/union so we must dereference appropriately
  // WE NEED TO CHECK THAT declaredPtrLevels == 0 since we need a
  // real struct/union, not just a pointer to one
  // BE CAREFUL WITH declaredType - it may be misleading since all
  // pointers share the same declaredType
  if ((cur_node->var.declaredPtrLevels == 0) &&
      (cur_node->var.varType->isStructUnionType))
    {
      // e->EAX is the contents of the virtual EAX, which should
      // be the address of the struct/union, so pass that along ...
      // NO extra level of indirection needed
      outputDaikonVar(&(cur_node->var),
		      FUNCTION_RETURN_VAR,
		      0,
		      0,
		      0,
		      0,
		      0,
		      daikonFuncPtr->trace_vars_tree,
		      DTRACE_FILE,
		      0,
		      (void*)e->EAX,
                      // No longer need to overrideIsInitialized
                      // because we now keep shadow V-bits for e->EAX
                      // and friends
		      0, // e->EAXvalid,
		      0,
		      0,
		      0,
		      0,
                      0,
                      daikonFuncPtr, 0);
    }
  // Double type - use FPU
  else if ((cur_node->var.declaredPtrLevels == 0) &&
	   (cur_node->var.varType->repType == R_DOUBLE))
    {
      // SPECIAL CASE: The value in FPU must be interpreted as a double
      // even if its true type may be a float

      // Need an additional indirection level
      outputDaikonVar(&(cur_node->var),
		      FUNCTION_RETURN_VAR,
		      0,
		      0,
		      0,
		      0,
		      0,
		      daikonFuncPtr->trace_vars_tree,
		      DTRACE_FILE,
		      0,
		      &(e->FPU),
                      // No longer need to overrideIsInitialized
                      // because we now keep shadow V-bits for e->EAX
                      // and friends
                      0, // e->FPUvalid,
		      0,
		      0,
		      0,
		      0,
                      0,
                      daikonFuncPtr, 0);
    }
  // Remember that long long int types use EAX as the low 4 bytes
  // and EDX as the high 4 bytes
  // long long ints - create a long long int and pass its address
  else if ((cur_node->var.declaredPtrLevels == 0) &&
           (cur_node->var.varType->declaredType == D_UNSIGNED_LONG_LONG_INT))
    {
      unsigned long long int uLong = (e->EAX) | (((unsigned long long int)(e->EDX)) << 32);
      // Remember to copy A and V-bits over:
      mc_copy_address_range_state((Addr)(&(e->EAX)),
                                  (Addr)(&uLong),
                                  sizeof(e->EAX));

      mc_copy_address_range_state((Addr)(&(e->EDX)),
                                  (Addr)(&uLong) + (Addr)sizeof(e->EAX),
                                  sizeof(e->EDX));

      outputDaikonVar(&(cur_node->var),
		      FUNCTION_RETURN_VAR,
		      0,
		      0,
		      0,
		      0,
		      0,
		      daikonFuncPtr->trace_vars_tree,
		      DTRACE_FILE,
		      0,
		      &uLong,
                      // No longer need to overrideIsInitialized
                      // because we now keep shadow V-bits for e->EAX
                      // and friends
		      0, // e->EAXvalid,
		      0,
		      0,
		      0,
		      0,
                      0,
                      daikonFuncPtr, 0);
    }
  else if ((cur_node->var.declaredPtrLevels == 0) &&
           (cur_node->var.varType->declaredType == D_LONG_LONG_INT))
    {
      long long int signedLong = (e->EAX) | (((long long int)(e->EDX)) << 32);
      // Remember to copy A and V-bits over:
      mc_copy_address_range_state((Addr)(&(e->EAX)),
                                  (Addr)(&signedLong),
                                  sizeof(e->EAX));

      mc_copy_address_range_state((Addr)(&(e->EDX)),
                                  (Addr)(&signedLong) + (Addr)sizeof(e->EAX),
                                  sizeof(e->EDX));

      outputDaikonVar(&(cur_node->var),
		      FUNCTION_RETURN_VAR,
		      0,
		      0,
		      0,
		      0,
		      0,
		      daikonFuncPtr->trace_vars_tree,
		      DTRACE_FILE,
		      0,
		      &signedLong,
                      // No longer need to overrideIsInitialized
                      // because we now keep shadow V-bits for e->EAX
                      // and friends
		      0, // e->EAXvalid,
		      0,
		      0,
		      0,
		      0,
                      0,
                      daikonFuncPtr, 0);
    }
  // All other types (integer and pointer) - use EAX
  else
    {
      // Need an additional indirection level
      DPRINTF(" RETURN - int/ptr.: cur_node=%p, basePtr=%p\n",
	      cur_node, &(e->EAX));

      outputDaikonVar(&(cur_node->var),
		      FUNCTION_RETURN_VAR,
		      0,
		      0,
		      0,
		      0,
		      0,
		      daikonFuncPtr->trace_vars_tree,
		      DTRACE_FILE,
		      0,
		      &(e->EAX),
                      // No longer need to overrideIsInitialized
                      // because we now keep shadow V-bits for e->EAX
                      // and friends
		      0, // e->EAXvalid,
		      0,
		      0,
		      0,
		      0,
                      0,
                      daikonFuncPtr, 0);
    }

  stringStackPop(fullNameStack, &fullNameStackSize);
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
// Now we do a two-pass approach which first goes FORWARD until it hits a byte
// whose A-bit is unset and then BACKWARDS until it hits the first bytes whose
// V-bit is SET.  This avoids printing out large chunks of garbage values when
// most of an array is uninitialized.
int probeAheadDiscoverHeapArraySize(Addr startAddr, UInt typeSize)
{
  int arraySize = 0;
  /*tl_assert(typeSize > 0);*/
  if (typeSize == 0)
    return 0;
  while (mc_check_writable( startAddr, typeSize, 0))
    {
      if (kvasir_print_debug_info)
	{
	  if (arraySize % 1000 == 0)
	    VG_(printf)( "Made it to %d elements at 0x%x\n", arraySize,
		    startAddr);
	}
      /* Cut off the search if we can already see it's really big:
         no need to look further than we're going to print. */
      if (kvasir_array_length_limit != -1 &&
          arraySize > kvasir_array_length_limit)
        break;

      arraySize++;
      startAddr+=typeSize;
    }

  startAddr -= typeSize;
  // Now do a SECOND pass and probe BACKWARDS until we reach the
  // first byte whose V-bit is SET
  while ((arraySize > 0) &&
         (kvasir_use_bit_level_precision ?
          (!MC_(are_some_bytes_initialized)(startAddr, typeSize, 0)) :
          (MC_Ok != mc_check_readable(startAddr, typeSize, 0)))) {
    arraySize--;
    startAddr-=typeSize;
  }

  return arraySize;
}

// Return the number of bytes between elements of this variable
// if it were used as an array
int getBytesBetweenElts(DaikonVariable* var)
{
  tl_assert(var);

  // Special treatment for strings
  //  if ((var->isString && (var->repPtrLevels > 0)) ||
  //      (!(var->isString) && (var->repPtrLevels > 1)))
  // Don't worry about that anymore - just use declaredPtrLevels
  if (var->declaredPtrLevels > 1)
    {
      DPRINTF("getBytesBetweenElts returning sizeof(void*) (%d)\n",
              sizeof(void*));
      return sizeof(void*);
    }
  else
    {
      DPRINTF("getBytesBetweenElts returning %d\n", var->varType->byteSize);
      return var->varType->byteSize;
    }
}


// Takes a location and a DaikonVariable and tries to determine
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
int returnArrayUpperBoundFromPtr(DaikonVariable* var, Addr varLocation)
{
  DaikonVariable* targetVar = 0;
  Addr baseAddr = 0;
  char foundGlobalArrayVariable = 0;

  DPRINTF("Checking for upper bound of %p\n", varLocation);

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
    FunctionEntry* e;
    DPRINTF("Not found in globals area, checking on stack\n");

    e = returnFunctionEntryWithAddress(varLocation);

    DPRINTF("Found function entry %p\n", e);

    if (e) {
      VarList* localArrayAndStructVars = e->localArrayVariablesPtr;

      // TODO: Try to get to the bottom of this problem of bogus
      // localArrayAndStructVars pointers, but for now, let's just mask it
      // so that Daikon runs:
      // assert(!localArrayAndStructVars || (unsigned int)localArrayAndStructVars > 0x100);

      if (localArrayAndStructVars &&
          // hopefully ensures that it's not totally bogus
          ((unsigned int)localArrayAndStructVars > 0x100) &&
          (localArrayAndStructVars->numVars > 0)) {
        DPRINTF(" zeta - %s - %p - %d\n", e->name,
                localArrayAndStructVars, localArrayAndStructVars->numVars);

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
    DPRINTF("Not found on stack, checking in heap\n");

    tl_assert(currentFunctionEntryPtr);

    // Make sure the address is not in the stack or global region
    // before probing so that we don't accidentally make a mistake
    // where we erroneously conclude that the array size is HUGE
    // since all areas on the stack and global regions are ALLOCATED
    // so probing won't do us much good
    if ((varLocation < currentFunctionEntryPtr->EBP) &&
        (varLocation > highestGlobalVarAddr)) {
      int size;
      DPRINTF("Location looks reasonable, probing at %p\n",
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
  else if (baseAddr &&
           (targetVar->varType->repType == var->varType->repType)) {
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
             (kvasir_use_bit_level_precision ?
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
  // or another, even though at function exit time, it blows since
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
  if ((currentFunctionEntryPtr && !wraparound &&
       ((addressInQuestion + numBytes) <= currentFunctionEntryPtr->EBP) &&
       (addressInQuestion >= currentFunctionEntryPtr->lowestESP)))
    {
      DPRINTF(" Address 0x%x is OFF THE HOOK for allocated in %s "
	      "(EBP: 0x%x, lowestESP: 0x%x)\n",
	      addressInQuestion,
	      currentFunctionEntryPtr->name,
	      currentFunctionEntryPtr->EBP,
	      currentFunctionEntryPtr->lowestESP);
      DASSERT(addressInQuestion != 0xffffffff);
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

// Return true if some of the bytes are initialized (V-bits set)
// and initializes GLOBAL_MASK to the bits which are initialized
char are_some_bytes_init(Addr addressInQuestion, unsigned int numBytes) {
  extern char GLOBAL_MASK[];

  // Everything on the stack frame of the current function IN BETWEEN
  // the function's EBP and the lowestESP is OFF THE HOOK!!!
  // We treat this as allocated automatically since the function has
  // actually explicitly allocated this on the stack at one time
  // or another, even though at function exit time, it blows since
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
  if ((currentFunctionEntryPtr && !wraparound &&
       ((addressInQuestion + numBytes) <= currentFunctionEntryPtr->EBP) &&
       (addressInQuestion >= currentFunctionEntryPtr->lowestESP)))
    {
      DASSERT(addressInQuestion != 0xffffffff);
      VG_(memset)(GLOBAL_MASK, 0xFF, numBytes);
      return 1;
    }
  else
  {
    return MC_(are_some_bytes_initialized)(addressInQuestion, numBytes, GLOBAL_MASK);
  }
}
