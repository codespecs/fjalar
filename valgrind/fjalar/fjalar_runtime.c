/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

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

#include "my_libc.h"

#include "fjalar_main.h"
#include "fjalar_include.h"
#include "fjalar_runtime.h"
#include "fjalar_select.h"
#include "generate_fjalar_entries.h"
#include "mc_include.h"

// I don't want to use macros, but this is a useful one for finding
// out whether a particular VariableEntry refers to a
// struct/union/class and not a pointer to such:
#define VAR_IS_BASE_STRUCT(var) ((var->ptrLevels == 0) && (IS_AGGREGATE_TYPE(var->varType)))


FunctionExecutionState* curFunctionExecutionStatePtr = 0;

// Return a pointer to a FunctionExecutionState which contains the address
// specified by "a" in its stack frame
// Assumes: The stack grows DOWNWARD on all supported platforms so this
//          returns the function entry with the smallest FP that is HIGHER
//          than "a" and a lowestSP that is LOWER than "a"
// Returns 0 if no function found
static
FunctionExecutionState* returnFunctionExecutionStateWithAddress(Addr a)
{
  Int i;

  ThreadId tid = VG_(get_running_tid)();

  FunctionExecutionState* cur_fn = 0;
  FunctionExecutionState* next_fn = 0;

  FJALAR_DPRINTF("Looking for function corresponding "
                 "to stack variable 0x%p\n", (void *)a);

  // Traverse the function stack from the function with
  // the highest ESP to the one with the lowest ESP
  // but DON'T LOOK at the function that's the most
  // recent one on the stack yet - hence 0 <= i <= (fn_stack_first_free_index - 2)
  for (i = 0; i <= fn_stack_first_free_index[tid] - 2; i++)
    {
      cur_fn = &FunctionExecutionStateStack[tid][i];
      next_fn = &FunctionExecutionStateStack[tid][i + 1];

      if (!cur_fn || !next_fn)
        {
          printf( "Error in returnFunctionExecutionStateWithAddress()");
          my_abort();
        }

      FJALAR_DPRINTF("cur_fn->FP: %p\n", (void *)cur_fn->FP);
      FJALAR_DPRINTF("next_fn->FP: %p\n", (void *)next_fn->FP);

      // If it is not the most recent function pushed on the stack,
      // then the stack frame of this function lies in between
      // the EBP of that function and the function immediately
      // following it on the stack
      if ((cur_fn->FP >= a) && (next_fn->FP <= a)) {
        FJALAR_DPRINTF("Returning functionEntry: %p\n", cur_fn);
        return cur_fn;
      }
    }

  // If a function hasn't been found yet, now
  // look at the most recent function on the stack:
  // If it is the most recent function on the stack,
  // then the stack frame can only be approximated to lie
  // in between its FP and lowestSP
  // (this isn't exactly accurate because there are issues
  //  with lowestSP, but at least it'll give us some info.)
  cur_fn = fnStackTop(tid);

  if ((cur_fn->FP >= a) && (cur_fn->lowestSP <= a)) {
    FJALAR_DPRINTF("Returning functionEntry: %zx\n", (size_t)cur_fn);
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
// Pre: VAR_IS_BASE_STRUCT(structVar)
static VariableEntry* searchForArrayWithinStruct(VariableEntry* structVar,
                                                  Addr structVarBaseAddr,
                                                  Addr targetAddr,
                                                  Addr* baseAddr) {
  VarNode* v = 0;

  tl_assert(structVar->varType->aggType);

  FJALAR_DPRINTF("searchForArrayWithinStruct: %s, structVarBaseAddr: %p, targetAddr: %p, baseAddr: %p\n",
                 structVar->name, (void*)structVarBaseAddr, (void*)targetAddr, (void*)baseAddr);

//  FJALAR_DPRINTF("aggType: %p, memberVarList: %p\n",
//                 structVar->varType->aggType,
//                (structVar->varType->aggType ? structVar->varType->aggType->memberVarList : 0));

  if (structVar->varType->aggType->memberVarList) {
    for (v = structVar->varType->aggType->memberVarList->first;
         v != 0;
         v = v->next) {
      VariableEntry* potentialVar;
      Addr potentialVarBaseAddr;

      potentialVar = v->var;
      tl_assert(IS_MEMBER_VAR(potentialVar));
      FJALAR_DPRINTF("examining: %s, offset: %lu\n", potentialVar->name,
                      potentialVar->memberVar->data_member_location);

//      FJALAR_DPRINTF("staticArr: %p, ptrLevels: %d, varType: %d\n",
//                      potentialVar->staticArr, potentialVar->ptrLevels,
//                     (potentialVar->varType ? potentialVar->varType->decType : 0));

      potentialVarBaseAddr = structVarBaseAddr + potentialVar->memberVar->data_member_location;

      if (IS_STATIC_ARRAY_VAR(potentialVar) &&
          (potentialVarBaseAddr <= targetAddr) &&
          (targetAddr < (potentialVarBaseAddr +
                         (potentialVar->staticArr->upperBounds[0] *
                          getBytesBetweenElts(potentialVar))))) {
        *baseAddr = potentialVarBaseAddr;
        FJALAR_DPRINTF("Wins: %s\n", potentialVar->name);
        return potentialVar;
      }
      // Recursive step (be careful to avoid infinite recursion)
      else if VAR_IS_BASE_STRUCT(potentialVar) {
        VariableEntry* targetVar =
          searchForArrayWithinStruct(potentialVar,
                                     potentialVarBaseAddr,
                                     targetAddr, baseAddr);

        if (targetVar) {
          FJALAR_DPRINTF("wins: %s\n", potentialVar->name);
          return targetVar;
        }
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
// based on FP or SP if !isGlobal
// *baseAddr = the base address of the variable returned
static VariableEntry*
returnArrayVariableWithAddr(VarList* varList,
                            Addr a,
                            char isGlobal,
                            FunctionExecutionState* e,
                            Addr* baseAddr) {
  VarNode* cur_node = 0;
  ThreadId tid = VG_(get_running_tid)();
  Addr var_loc = 0;

  FJALAR_DPRINTF("[returnArrayVariableWithAddr] varList: %p, Addr: %p, %s\n", varList, (void *)a, (isGlobal)?"Global":"NonGlobal");
  if (!isGlobal) {
    FJALAR_DPRINTF("frame_ptr: %p, stack_ptr: %p\n", (void *)e->FP, (void *)e->lowSP);
  }

  for (cur_node = varList->first;
       cur_node != 0;
       cur_node = cur_node->next) {
    VariableEntry* potentialVar = cur_node->var;
    Addr potentialVarBaseAddr = 0;

    if (!potentialVar)
      continue;

    FJALAR_DPRINTF("Examining potential var: %s, offset: 0x%x, locType: 0x%x\n",
                    potentialVar->name, (unsigned int) potentialVar->byteOffset, potentialVar->locationType);

    if (isGlobal) {
      tl_assert(IS_GLOBAL_VAR(potentialVar));
      potentialVarBaseAddr = potentialVar->globalVar->globalLocation;
      FJALAR_DPRINTF("Examining potential var address: %p\n",(void *) potentialVarBaseAddr);
    } else {
      if (potentialVar->locationType == FP_OFFSET_LOCATION) {
        potentialVarBaseAddr = e->FP + potentialVar->byteOffset;
      } else {  
        // (comment added 2014)  
        // Potential bug!  We are ignoring other locationTypes
        // and just assuming it is ESP.  This is the only case
        // we've seen (i386 only) so far.  (markro)
        potentialVarBaseAddr = e->lowSP + potentialVar->byteOffset;
      }
    }
    if (potentialVar->location_expression_size) {
      unsigned int i = 0;
      for(i = 0; i < potentialVar->location_expression_size; i++ ) {
        dwarf_location *dloc  = &(potentialVar->location_expression[i]);
        unsigned int  op = dloc->atom;
        int reg_val;

        if(op == DW_OP_addr) {
          // DWARF supplied address
          var_loc = dloc->atom_offset;

        } else if(op == DW_OP_deref) {
          // Dereference result of last DWARF operation
          tl_assert(var_loc);
          var_loc = *(Addr *)var_loc;

        } else if((op >= DW_OP_const1u) && (op <= DW_OP_consts)) {
          // DWARF supplied constant
          var_loc = dloc->atom_offset;

        } else if((op >= DW_OP_plus) && (op <= DW_OP_plus_uconst)) {
          // Add DWARF supplied constant to value to result of last DWARF operation
          var_loc += dloc->atom_offset;

        } else if((op >= DW_OP_reg0) && (op <= DW_OP_reg31)) {
          // Get value located in architectural register
          reg_val = (*get_reg[dloc->atom - DW_OP_reg0])(tid);
          FJALAR_DPRINTF("\tObtaining register value: [%%%s]: %x\n", dwarf_reg_string[dloc->atom - DW_OP_reg0], (unsigned int) reg_val);
          var_loc = (Addr)&reg_val;

        } else if((op >= DW_OP_breg0) && (op <= DW_OP_breg31)) {
          // Get value pointed to by architectural register
          reg_val = (*get_reg[dloc->atom - DW_OP_breg0])(tid);
          FJALAR_DPRINTF("\tObtaining register value: [%%%s]: %x\n", dwarf_reg_string[dloc->atom - DW_OP_breg0], (unsigned int) reg_val);
          var_loc = reg_val + dloc->atom_offset;
          FJALAR_DPRINTF("\tAdding %lld to the register value for %p\n", dloc->atom_offset, (void *)var_loc);
          tl_assert(var_loc);

        } else if(op == DW_OP_fbreg) {
          // Get value located at an offset from the FRAME_BASE.
          FJALAR_DPRINTF("atom offset: %lld vs. byteOffset: %d\n", dloc->atom_offset, potentialVar->byteOffset);
          var_loc = e->FP + dloc->atom_offset;

        } else {
          // There's a fair number of DWARF operations still unsupported. There is a full list
          // in fjalar_debug.h
          FJALAR_DPRINTF("\tUnsupported DWARF stack OP: %s\n", location_expression_to_string(op));
          tl_assert(0);
        }
        FJALAR_DPRINTF("\tApplying DWARF Stack Operation %s - %p\n",location_expression_to_string(op), (void *)var_loc);
      }
    }
    FJALAR_DPRINTF("addr: %p, potential var_loc: %p, staticArr: %p, ptrLevels: %u, varType: %u\n",
                   (void*)a, (void*)potentialVarBaseAddr, potentialVar->staticArr, potentialVar->ptrLevels,
                   (potentialVar->varType ? potentialVar->varType->decType : 0));

    // array
    if (IS_STATIC_ARRAY_VAR(potentialVar) &&
        (potentialVarBaseAddr <= a) &&
        (a < (potentialVarBaseAddr + (potentialVar->staticArr->upperBounds[0] *
                                      getBytesBetweenElts(potentialVar))))) {

      FJALAR_DPRINTF("returnArrayVar: found matching array with upperBounds[0]: %u\n", potentialVar->staticArr->upperBounds[0]);
      *baseAddr = potentialVarBaseAddr;
      return potentialVar;
    }
    // struct
    else if (VAR_IS_BASE_STRUCT(potentialVar) &&
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
/*
static
VariableEntry* returnGlobalSingletonWithAddress(Addr a) {
  VarNode* cur_node = 0;
  VariableEntry* r = 0;
  FJALAR_DPRINTF(" in returnGlobalSingletonWithAddress\n");
  for (cur_node = globalVars.first; cur_node != 0; cur_node = cur_node->next)
    {
      r = cur_node->var;

      if (!r)
        continue;

      if (IS_GLOBAL_VAR(r) && (!IS_STATIC_ARRAY_VAR(r)) && r->globalVar->globalLocation == a)
        {
          FJALAR_DPRINTF(" EXIT SUCCESS returnGlobalSingletonWithAddress - %s\n", r->name);
          return r;
        }
    }
  FJALAR_DPRINTF(" EXIT FAILURE returnGlobalSingletonWithAddress\n");
  return 0;
} */


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
  FJALAR_DPRINTF ( "typeSize: 0x%x\n", typeSize);
  while (mc_check_writable( startAddr, typeSize, 0))
    {
      if (arraySize % 1000 == 0)
        FJALAR_DPRINTF ( "Made it to %d elements at 0x%x\n", arraySize,
                         (unsigned int)startAddr);
      /* Cut off the search if we can already see it's really big:
         no need to look further than we're going to print. */
      // RUDD TEMP
/*       if (fjalar_array_length_limit != -1 && */
/*           arraySize > fjalar_array_length_limit) */
/*         break; */

      arraySize++;
      startAddr+=typeSize;
    }

  startAddr -= typeSize;
  // Now do a SECOND pass and probe BACKWARDS until we reach the
  // first set of bytes with at least one byte whose V-bit is SET
  while ((arraySize > 0) &&
         // If at least ONE byte within the element of size typeSize
         // is initialized, then consider the entire element to be
         // initialized.  This is done because sometimes only certain
         // members of a struct are initialized, and if we perform the
         // more stringent check for whether ALL members are
         // initialized, then we will falsely mark
         // partially-initialized structs as uninitialized and lose
         // information.  For instance, consider struct point{int x;
         // int y;} - Let's say you had struct point foo[10] and
         // initialized only the 'x' member var. in every element of
         // foo (foo[0].x, foo[1].x, etc...)  but left the 'y' member
         // var uninitialized.  Every element of foo has typeSize = 2
         // * sizeof(int) = 8, but only the first 4 bytes are
         // initialized ('x') while the last 4 are uninitialized
         // ('y').  This function should return 10 for the size of
         // foo, so it must mark each element as initialized when at
         // least ONE byte is initialized (in this case, a byte within
         // 'x').
         !mc_are_some_bytes_initialized(startAddr, typeSize)) {
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
      FJALAR_DPRINTF("getBytesBetweenElts returning sizeof(void*) (%zu)\n",
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

  FJALAR_DPRINTF("Checking for upper bound of %p\n", (void *)varLocation);

  // 1. Search if varLocation is within a global variable
  if (addressIsGlobal(varLocation)) {
    targetVar = returnArrayVariableWithAddr(&globalVars,
                                            varLocation,
                                            1, 0, &baseAddr);

    if (targetVar) {
      foundGlobalArrayVariable = 1;
    }
    else {
      // UNCONDITIONALLY RETURN 0 IF WE CANNOT FIND A GLOBAL ARRAY
      // VARIABLE.  WE DO NOT WANT TO PROBE IN THE GLOBAL SPACE
      // BECAUSE ALL OF IT MAY POSSIBLY BE INITIALIZED.

      //      targetVar = returnGlobalSingletonWithAddress(varLocation);
      //      if (targetVar) {
      return 0;
        //      }
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
      FJALAR_DPRINTF(" e->FP is %p\n", (void *)e->FP);
      FJALAR_DPRINTF(" localArrayAndSTructVars: %p, numVars: %u\n", localArrayAndStructVars, localArrayAndStructVars->numVars);

      tl_assert(!localArrayAndStructVars || (Addr)localArrayAndStructVars > 0x100);

      if (localArrayAndStructVars &&
          // hopefully ensures that it's not totally bogus
          ((Addr)localArrayAndStructVars > 0x100) &&
          (localArrayAndStructVars->numVars > 0)) {
        targetVar = returnArrayVariableWithAddr(localArrayAndStructVars,
                                                varLocation,
                                                0, e, &baseAddr);
      }
    }
  }

  // 3. If still not found, then search the heap for varLocation
  //    if it is lower than the current frame pointer
  // This is a last-ditch desperation attempt and won't yield valid-looking
  // results in cases like when you have a pointer to an int which is located
  // within a struct malloc'ed on the heap.
  if (!targetVar) {
    FJALAR_DPRINTF("Not found on stack, checking in heap\n");

    tl_assert(curFunctionExecutionStatePtr);

    FJALAR_DPRINTF("Checking if the variable is on the stack:\n");
    FJALAR_DPRINTF("\tCurrent Stackframe: [%p - %p]\n", (void*)curFunctionExecutionStatePtr->FP, (void*)curFunctionExecutionStatePtr->lowestSP);

    // Make sure the address is not in the stack or global region
    // before probing so that we don't accidentally make a mistake
    // where we erroneously conclude that the array size is HUGE
    // since all areas on the stack and global regions are ALLOCATED
    // so probing won't do us much good
    if ((varLocation < curFunctionExecutionStatePtr->lowestSP) &&
        !addressIsGlobal(varLocation)) {
      int size;
      FJALAR_DPRINTF("Location looks reasonable, probing at %p\n",
             (void *)varLocation);

      size =
        probeAheadDiscoverHeapArraySize(varLocation,
                                        getBytesBetweenElts(var));

      FJALAR_DPRINTF("Size is %d\n", size);

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

  // (comment added 2005)  
  // TODO: Hmmmm, what are we gonna do without repTypes???  I need to
  // investigate this 'if' condition more carefully later:
  else if (baseAddr) {
    int targetVarSize = 0;
    int targetVarBytesBetweenElts = getBytesBetweenElts(targetVar);
    int varBytesBetweenElts = getBytesBetweenElts(var);
    Addr highestAddr;

    tl_assert(IS_STATIC_ARRAY_VAR(targetVar));
    FJALAR_DPRINTF("varLocation: %p\n", (void *)varLocation);

    highestAddr = baseAddr + ((targetVar->staticArr->upperBounds[0]) * targetVarBytesBetweenElts);

    FJALAR_DPRINTF("baseAddr is: %p, highestAddr is %p\n", (void *)baseAddr, (void *)highestAddr);

    // NEW!: Probe backwards until you find the first address whose V-bit is SET:
    // but ONLY do this for globals and NOT for stuff on the stack because
    // V-bits for stack variables are FLAKY!!!  During function exit, all the V-bits
    // are wiped out :(

    if (foundGlobalArrayVariable) {
      while ((highestAddr > varLocation) &&
              (MC_Ok != mc_check_readable(highestAddr, targetVarBytesBetweenElts, 0))) {
        highestAddr -= targetVarBytesBetweenElts;
      }
    }

    // This is IMPORTANT that we subtract from varLocation RATHER than baseAddr
    // because of the fact that varLocation can point to the MIDDLE of an array
    targetVarSize = (highestAddr - varLocation) / targetVarBytesBetweenElts;
    FJALAR_DPRINTF("targetVarBytesBetweenElts is %d, varBytesBetweenElts is %d, targetVarSize is %d\n",
                    targetVarBytesBetweenElts, varBytesBetweenElts, targetVarSize);


    FJALAR_DPRINTF("Target : [%s - %d] Source : [%s - %d]\n",
                    targetVar->varType->typeName, targetVarBytesBetweenElts,
                    var->varType->typeName, varBytesBetweenElts);

    if (targetVarBytesBetweenElts == varBytesBetweenElts) {
      return targetVarSize;
    } else {
      return (targetVarSize * targetVarBytesBetweenElts) / varBytesBetweenElts;
    }

  }
  return 0;
}

// Checks if numBytes that this address points to has been allocated
// and is thus safe to dereference or readable and thus contains
// valid data
// allocatedOrInitialized = 1 - checks for allocated (A-bits)
// allocatedOrInitialized = 0 - checks for initialized (V-bits)
static
Bool addressIsAllocatedOrInitialized(Addr addressInQuestion,
                                     UInt numBytes,
                                     Bool allocatedOrInitialized)
{
  // Everything on the stack frame of the current function IN BETWEEN
  // the function's FP and the lowestSP is OFF THE HOOK!!!
  // We treat this as allocated automatically since the function has
  // actually explicitly allocated this on the stack at one time
  // or another, even though at function exit time, it's bad because
  // the ESP increments back up near FP:
  // The reason why we need this check is that during function exit time,
  // Valgrind marks that function's stack frame as invalid even though
  // it's technically still valid at the moment we exit because
  // nothing else has had time to touch it yet

  // (comment added 2005)  
  // TODO: The problem with this is that, although everything in this range
  //       should be allocate (A-bits), not everything in this range is
  //       initialized (V-bits) but we are ASSUMING that it is!!!
  //       In order to get initialization information, we will need to make
  //       a copy of the V-bits and store them with the function
  int wraparound = ((addressInQuestion + numBytes) < addressInQuestion);
  if ((curFunctionExecutionStatePtr && !wraparound &&
       ((addressInQuestion + numBytes) <= curFunctionExecutionStatePtr->FP) &&
       (addressInQuestion >= (curFunctionExecutionStatePtr->lowestSP - VG_STACK_REDZONE_SZB))))
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

// Returns True if all numBytes bytes starting at addressInQuestion
// have been allocated, False otherwise
Bool addressIsAllocated(Addr addressInQuestion, UInt numBytes) {
  return addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 1);
}

// Returns True if all numBytes bytes starting at addressInQuestion
// have been initialized by the program, False otherwise (indicates a
// possible garbage value)
Bool addressIsInitialized(Addr addressInQuestion, UInt numBytes) {
  return addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 0);
}
