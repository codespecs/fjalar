/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_traversal.c:
   Functions for traversing through data structures at run time
*/

#include "fjalar_traversal.h"

#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/errno.h>
#include <assert.h>
#include <search.h>
#include <limits.h>

// This increments every time a call to visitSingleVar() or
// visitSequence() is made.  It is up to the caller to reset this
// properly!
int g_variableIndex = 0;

static char* dereference = "[]";
static char* zeroth_elt = "[0]";
static char* dot = ".";
static char* arrow = "->";
static char* star = "*";

// This stack represents the full name of the variable that we
// currently want to output (Only puts REFERENCES to strings in
// fullNameStack; does not do any allocations)
char* fullNameStack[MAX_STRING_STACK_SIZE];
int fullNameStackSize = 0;

void stringStackPush(char** stringStack, int* pStringStackSize, char* str)
{
  tl_assert(str && *pStringStackSize < MAX_STRING_STACK_SIZE);

  // Don't allow null strings at all:
  //  if (!str) {
  //    VG_(printf)( "Null string passed to push!\n");
  //    /* abort(); */
  //    str = "<null>";
  //  }

  stringStack[*pStringStackSize] = str;
  (*pStringStackSize)++;
}

char* stringStackPop(char** stringStack, int* pStringStackSize)
{
  char* temp;
  tl_assert(*pStringStackSize > 0);

  temp = stringStack[*pStringStackSize - 1];
  (*pStringStackSize)--;

  return temp;
}

char* stringStackTop(char** stringStack, int stringStackSize)
{
  return stringStack[stringStackSize - 1];
}

void stringStackClear(int* pStringStackSize)
{
  (*pStringStackSize) = 0;
}

// Returns: Total length of all strings on stringStack
int stringStackStrLen(char** stringStack, int stringStackSize)
{
  int i;
  int total = 0;
  for (i = stringStackSize - 1; i >=0; i--)
    {
      total+=VG_(strlen)(stringStack[i]);
    }
  return total;
}

void stringStackPrint(char** stringStack, int stringStackSize)
{
  int i;
  for (i = stringStackSize - 1; i >= 0; i--)
    {
      printf("stringStack[%d] = %s\n", i, stringStack[i]);
    }
}

// Takes all of the strings on stringStack, copies them into a newly
// calloc'ed string (in a queue-like FIFO order), and returns a
// pointer to that string.
char* stringStackStrdup(char** stringStack, int stringStackSize)
{
  // Extra 1 for trailing '\0'
  int totalStrLen = stringStackStrLen(stringStack, stringStackSize) + 1;
  char* fullName = (char*)VG_(calloc)(totalStrLen, sizeof(char));
  int i;

  for (i = 0; i < stringStackSize; i++) {
    VG_(strcat)(fullName, stringStack[i]);
  }
  return fullName;
}

// Visit all variables in a particular VarList depending on varOrigin:
void visitAllVariablesInList(FunctionEntry* funcPtr, // 0 for unspecified function
                             char isEnter,           // 1 for function entrance, 0 for exit
			     VariableOrigin varOrigin,
			     char* stackBaseAddr) {
  VarNode* i = 0;

  VarList* varListPtr = 0;
  int numIters = 0;

  // If funcPtr is null, then you better be GLOBAL_VAR
  if (!funcPtr) {
    tl_assert(varOrigin == GLOBAL_VAR);
  }

  switch (varOrigin) {
  case GLOBAL_VAR:
    varListPtr = &globalVars;
    break;
  case FUNCTION_ENTER_FORMAL_PARAM:
  case FUNCTION_EXIT_FORMAL_PARAM:
    varListPtr = &(funcPtr->formalParameters);
    break;
  case FUNCTION_RETURN_VAR:
    varListPtr = &(funcPtr->returnValue);
    break;
  default:
    tl_assert(0 && "Invalid varOrigin");
    break;
  }

  stringStackClear(&fullNameStackSize);

  assert(varListPtr);

  for (i = varListPtr->first;
       i != NULL;
       i = i->next) {
      VariableEntry* var;
      void* basePtrValue = 0;

      var = &(i->var);

      if (!var->name) {
	VG_(printf)( "  Warning! Weird null variable name!\n");
	continue;
      }

      if ((varOrigin == FUNCTION_ENTER_FORMAL_PARAM) ||
	  (varOrigin == FUNCTION_EXIT_FORMAL_PARAM)) {
        basePtrValue = (void*)((int)stackBaseAddr + var->byteOffset);
      }
      else if (varOrigin == GLOBAL_VAR) {
        basePtrValue = (void*)(var->globalLocation);

        // If "--limit-static-vars" option was selected, then:
        // * Only print file-static variables at program points
        //   in the file in which the variables were declared
        // * Only print static variables declared within functions
        //   at program points of that particular function
        if (!var->isExternal && fjalar_limit_static_vars && funcPtr) {
          // Declared within a function
          if (var->functionStartPC) {
            if (funcPtr->startPC != var->functionStartPC) {
              continue;
            }
          }
          // Declared globally
          else if (!VG_STREQ(funcPtr->filename, var->fileName)) {
            continue;
          }
        }

        // Under normal circumstances, DON'T PRINT OUT C++ static member variables
        // UNLESS it belongs to the SAME CLASS as the function we are printing
        // Print out all regular globals normally (hence the check for
        // var->structParentType)
        if (var->structParentType && funcPtr &&
            (var->structParentType != funcPtr->parentClass)) {
          continue;
        }
      }

      stringStackPush(fullNameStack, &fullNameStackSize, var->name);

      visitVariable(var,
                    basePtrValue,
                    0,
                    varOrigin,
                    funcPtr,
                    isEnter);

      stringStackPop(fullNameStack, &fullNameStackSize);
    }
}


/* Functions for visiting variables at every program point */

// Returns 1 if we are interested in visiting this variable and its
// children, 0 otherwise.  No children of this variable will get
// visited if this variable is not visited.  For example, if 'foo' is
// an array, then if the hashcode value of 'foo' is not visited, then
// the actual array value of 'foo[]' won't be visited either.
// This performs string matching in trace_vars_tree based on fullFjalarName
static char interestedInVar(char* fullFjalarName, char* trace_vars_tree) {
  if (fjalar_trace_vars_filename) {
    if (trace_vars_tree) {
      if (!tfind((void*)fullFjalarName, (void**)&trace_vars_tree, compareStrings)) {
        return 0;
      }
    }
    // If trace_vars_tree is kept at 0 on purpose but
    // fjalar_trace_vars_filename is valid, then still punt because we
    // are only supposed to print out variables listed in
    // fjalar_trace_vars_filename and obviously there aren't any
    // relevant variables to print
    else {
      return 0;
    }
  }

  return 1;
}

static
void visitSingleVar(VariableEntry* var,
                    UInt numDereferences,
                    void* pValue,
                    char overrideIsInit,
                    VariableOrigin varOrigin,
                    char* trace_vars_tree,
                    DisambigOverride disambigOverride,
                    UInt numStructsDereferenced,
                    FunctionEntry* varFuncInfo,
                    char isEnter);

static
void visitSequence(VariableEntry* var,
                   UInt numDereferences,
                   void** pValueArray,
                   UInt numElts,
                   VariableOrigin varOrigin,
                   char* trace_vars_tree,
                   DisambigOverride disambigOverride,
                   UInt numStructsDereferenced,
                   FunctionEntry* varFuncInfo,
                   char isEnter);

// This visits a variable by delegating to visitSingleVar()
// Pre: varOrigin != DERIVED_VAR, varOrigin != DERIVED_FLATTENED_ARRAY_VAR
// Pre: The name of the variable is already initialized in fullNameStack
void visitVariable(VariableEntry* var,
                   // Pointer to the location of the variable's
                   // current value in memory:
                   void* pValue,
                   // We only use overrideIsInit when we pass in
                   // things (e.g. return values) that cannot be
                   // checked by the Memcheck A and V bits. Never have
                   // overrideIsInit when you derive variables (make
                   // recursive calls) because their addresses are
                   // different from the original's
                   char overrideIsInit,
                   VariableOrigin varOrigin,
                   FunctionEntry* varFuncInfo,
                   char isEnter) {

  trace_vars_tree* var_tree = 0;

  tl_assert(varOrigin != DERIVED_VAR);
  tl_assert(varOrigin != DERIVED_FLATTENED_ARRAY_VAR);

  // In preparation for a new round of variable visits, initialize a
  // new VisitedStructsTable, freeing an old one if necessary
  if (VisitedStructsTable) {
    genfreehashtable(VisitedStructsTable);
    VisitedStructsTable = 0;
  }
  VisitedStructsTable = genallocatehashtable((unsigned int (*)(void *)) &hashID,
                                             (int (*)(void *,void *)) &equivalentIDs);

  // Also initialize trace_vars_tree based on varOrigin and
  // varFuncInfo:
  if (varOrigin == GLOBAL_VAR) {
    var_tree = (globalFunctionTree ?
                globalFunctionTree->function_variables_tree : 0);
  }
  else {
    var_tree = varFuncInfo->trace_vars_tree;
  }

  // Delegate:
  visitSingleVar(var,
                 0,
                 pValue,
                 overrideIsInit,
                 varOrigin,
                 trace_vars_tree,
                 OVERRIDE_NONE,
                 0,
                 varFuncInfo,
                 isEnter);
}


// Visit a single variable uniquely identified by var and
// numDereferences and then derive additional variables either by
// dereferencing pointers or by visiting struct members
// This function calls visitSingleVar() or visitSequence()
static
void visitSingleVar(VariableEntry* var,
                    UInt numDereferences,
                    // Pointer to the variable's current value
                    void* pValue,
                    // We only use overrideIsInit when we pass in
                    // things (e.g. return values) that cannot be
                    // checked by the Memcheck A and V bits. Never have
                    // overrideIsInit when you derive variables (make
                    // recursive calls) because their addresses are
                    // different from the original's
                    char overrideIsInit,
                    VariableOrigin varOrigin,
                    char* trace_vars_tree,
                    DisambigOverride disambigOverride,
                    // The number of structs we have dereferenced for
                    // a particular call of visitVariable(); Starts at
                    // 0 and increments every time we hit a variable
                    // which is a base struct type
                    // Range: [0, MAX_VISIT_NESTING_DEPTH]
                    UInt numStructsDereferenced,
                    // These uniquely identify the program point
                    FunctionEntry* varFuncInfo,
                    char isEnter) {
  char* fullFjalarName = 0;
  int layersBeforeBase;

  // Initialize these in a group later
  char disambigOverrideArrayAsPointer = 0;
  char derefSingleElement = 0;

  // Only valid for .dtrace - affects pValue
  char variableHasBeenObserved = 0;

  tl_assert(var);
  layersBeforeBase = var->repPtrLevels - numDereferences;
  tl_assert(layersBeforeBase >= 0);

  // Special handling for overriding in the presence of .disambig:
  // Only check this for original (numDereferences == 0) variables
  // to ensure that it's only checked once per variable
  if (0 == numDereferences) {
    disambigOverride = returnDisambigOverride(var);
  }

  if (fjalar_disambig_ptrs) {
    disambigOverride = OVERRIDE_ARRAY_AS_POINTER;
  }

  if ((fjalar_func_disambig_ptrs) &&
      ((varOrigin == FUNCTION_ENTER_FORMAL_PARAM) ||
       (varOrigin == FUNCTION_EXIT_FORMAL_PARAM) ||
       (varOrigin == FUNCTION_RETURN_VAR))) {
    disambigOverride = OVERRIDE_ARRAY_AS_POINTER;
  }

  disambigOverrideArrayAsPointer =
    (OVERRIDE_ARRAY_AS_POINTER == disambigOverride);

  derefSingleElement = disambigOverrideArrayAsPointer;


  // Unless fjalar_output_struct_vars is on,
  // don't print out an entry for base (non-pointer) struct/union
  // variables since they have no substantive meaning for C programs.
  // They are merely represented as hashcode values, and that's kind
  // of deceiving because they aren't really pointer variables either.

  // This means that anywhere inside of this 'if' statement, we should
  // be very careful about mutating state because different state may
  // be mutated based on whether fjalar_output_struct_vars is on,
  // which may lead to different-looking results.
  if (fjalar_output_struct_vars ||
      (!((layersBeforeBase == 0) &&
         (var->varType->isStructUnionType)))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStackSize > 0);
    fullFjalarName = stringStackStrdup(fullNameStack, fullNameStackSize);
    // If we are not interested in visiting this variable or its
    // children, then PUNT:
    if (!interestedInVar(fullFjalarName, trace_vars_tree)) {
      VG_(free)(fullFjalarName);
      return;
    }

    // Perform the actual output depending on outputType:
    switch (outputType) {
    case DECLS_FILE:
      printDeclsEntry(var, fullFjalarName, varOrigin, allowVarDumpToFile,
                      layersBeforeBase, 0, disambigOverride,
                      varFuncInfo, isEnter);
      break;
    case DTRACE_FILE:
      variableHasBeenObserved =
        printDtraceEntry(var,
                         numDereferences,
                         fullFjalarName,
                         pValue,
                         varOrigin,
                         (layersBeforeBase > 0),
                         overrideIsInit,
                         disambigOverride,
                         0, // NOT isSequence
                         0,
                         0,
                         varFuncInfo,
                         isEnter);
      break;
    case DISAMBIG_FILE:
      printDisambigEntry(var, fullFjalarName);
      // DO NOT DERIVE VARIABLES for .disambig.  We are only interested
      // in printing out the variables which are immediately visible
      // to the user.  Thus, we should RETURN out of the function
      // altogether instead of simply breaking out of the switch
      return;
    case DYNCOMP_EXTRA_PROP:
      handleDynCompExtraProp(var, layersBeforeBase, varFuncInfo, isEnter);
      break;
    case FAUX_DECLS_FILE:
      // Chill and do nothing here because we're making a dry run :)
      break;
    default:
      VG_(printf)( "Error! Invalid outputType in visitSingleVar()\n");
      abort();
      break;
    }
  }

  // This is an ugly hack that's required to properly not print out
  // base struct variables but still make sure that derived variables
  // are properly printed out.  We want to set variableHasBeenObserved
  // to 1 if we encounter a base struct variable because we need its
  // member variables to be properly observed:
  if ((layersBeforeBase == 0) &&
      (var->varType->isStructUnionType)) {
    variableHasBeenObserved = 1;
  }

  // We don't need the name anymore since we're done printing
  // everything about this variable by now
  VG_(free)(fullFjalarName);

  // Be very careful about where you increment this!  We want to
  // increment this once per call of either visitSingleVar() or
  // visitSequence():
  g_variableIndex++;

  //  VG_(printf)("    variableHasBeenObserved: %d\n", variableHasBeenObserved);

  // Now comes the fun part of deriving variables!

  // Dereference and keep on printing out derived variables until we
  // hit the base type:
  if (layersBeforeBase > 0) {

    // 1.) Initialize pValue properly and call visitSingleVar() again
    // because we are dereferencing a single element:
    if (derefSingleElement) {
      char derivedIsAllocated = 0;
      char derivedIsInitialized = 0;

      void* pNewValue = 0;

      // Initialize pNewValue if possible, otherwise leave at 0:
      // VERY IMPORTANT: Only derive if variableHasBeenObserved
      if ((DTRACE_FILE == outputType) &&
          pValue &&
          variableHasBeenObserved) {
        derivedIsAllocated = (overrideIsInit ? 1 :
                              addressIsAllocated((Addr)pValue, sizeof(void*)));
        if (derivedIsAllocated) {
          derivedIsInitialized = (overrideIsInit ? 1 :
                                  addressIsInitialized((Addr)pValue, sizeof(void*)));
          // Make a single dereference unless the variable is a static
          // array, in which case we shouldn't make a dereference at
          // all:
          pNewValue = var->isStaticArray ? pValue : *((void **)pValue);
        }
      }

      // Push 1 symbol on stack to represent single elt. dereference:

      //      if (kvasir_repair_format) {
      //        stringStackPush(fullNameStack, &fullNameStackSize, star);
      //      }
      //      else {
      stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt);
        //      }

      visitSingleVar(var,
                     numDereferences + 1,
                     pNewValue,
                     overrideIsInit,
                     (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                     trace_vars_tree,
                     disambigOverride,
                     numStructsDereferenced,
                     varFuncInfo,
                     isEnter);

      // Pop 1 symbol off
      stringStackPop(fullNameStack, &fullNameStackSize);
    }
    // 2.) Sequence dereference (can either be static or dynamic
    // array).  We need to initialize pValueArray and numElts
    // appropriately and call visitSequence()
    else {
      void** pValueArray = 0;
      UInt numElts = 0;
      UInt bytesBetweenElts = getBytesBetweenElts(var);
      UInt i;

      // We only need to set pValueArray and numElts for .dtrace output:
      // VERY IMPORTANT: Only derive if variableHasBeenObserved
      if ((DTRACE_FILE == outputType) &&
          pValue &&
          variableHasBeenObserved) {
        // Static array:
        if (VAR_IS_STATIC_ARRAY(var)) {
          // Flatten multi-dimensional arrays by treating them as one
          // giant single-dimensional array.  Take the products of the
          // sizes of all dimensions (remember to add 1 to each to get
          // from upper bound to size):
          UInt dim;

          // Notice the +1 to convert from upper bound to numElts
          numElts = 1 + var->upperBounds[0];

          // Additional dimensions:
          for (dim = 1; dim < var->numDimensions; dim++) {
            numElts *= (1 + var->upperBounds[dim]);
          }

          pValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

          //          VG_(printf)("Static array - dims: %u, numElts: %u\n",
          //                      var->numDimensions, numElts);

          // Build up pValueArray with pointers to the elements of the
          // static array starting at pValue
          for (i = 0; i < numElts; i++) {
            pValueArray[i] = pValue + (i * bytesBetweenElts);
          }
        }
        // Dynamic array:
        else {
          char derivedIsAllocated = 0;
          char derivedIsInitialized = 0;
          void* pNewStartValue = 0;

          derivedIsAllocated = (overrideIsInit ? 1 :
                                addressIsAllocated((Addr)pValue, sizeof(void*)));
          if (derivedIsAllocated) {
            derivedIsInitialized = (overrideIsInit ? 1 :
                                    addressIsInitialized((Addr)pValue, sizeof(void*)));
            // Make a single dereference to get to the start of the array
            pNewStartValue = *((void **)pValue);
          }

          // We should only initialize pValueArray and numElts if the
          // pointer to the start of the array is valid:
          if (pNewStartValue) {
            // Notice the +1 to convert from upper bound to numElts
            numElts = 1 + returnArrayUpperBoundFromPtr(var, (Addr)pNewStartValue);
            pValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

            // Build up pValueArray with pointers starting at pNewStartValue
            for (i = 0; i < numElts; i++) {
              pValueArray[i] = pNewStartValue + (i * bytesBetweenElts);
            }
          }
        }
      }

      // Push 1 symbol on stack to represent sequence dereference:
      stringStackPush(fullNameStack, &fullNameStackSize, dereference);

      visitSequence(var,
                    numDereferences + 1,
                    pValueArray,
                    numElts,
                    (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                    trace_vars_tree,
                    disambigOverride,
                    numStructsDereferenced,
                    varFuncInfo,
                    isEnter);

      // Pop 1 symbol off
      stringStackPop(fullNameStack, &fullNameStackSize);

      // Only free if necessary
      if (pValueArray) {
        VG_(free)(pValueArray);
        pValueArray = 0;
      }
    }
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (var->varType->isStructUnionType) {
    tl_assert(0 == layersBeforeBase);

    VarList* memberVars;
    VarNode* i;
    VariableEntry* curVar;

    // Check to see if the VisitedStructsTable contains more than
    // MAX_VISIT_STRUCT_DEPTH of the current struct type
    if (gencontains(VisitedStructsTable, (void*)(var->varType))) {
      UInt count = (UInt)(gengettable(VisitedStructsTable, (void*)(var->varType)));

      if (count <= MAX_VISIT_STRUCT_DEPTH) {
        count++;
        genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
      }
      // PUNT because this struct has appeared more than
      // MAX_VISIT_STRUCT_DEPTH times during one call to visitVariable()
      else {
        return;
      }
    }
    // If not found in the table, initialize this entry with 1
    else {
      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)1);
    }

    // If we have dereferenced more than
    // MAX_VISIT_NESTING_DEPTH structs, then simply PUNT and
    // stop deriving variables from it.
    if (numStructsDereferenced > MAX_VISIT_NESTING_DEPTH) {
      return;
    }


    // Walk down the member variables list and visit each one with the
    // current struct variable name as the prefix:
    memberVars = var->varType->memberListPtr;
    i = 0;
    curVar = 0;

    // No member variables
    if(!memberVars || !(memberVars->first))
      return;

    for (i = memberVars->first; i != 0; i = i->next) {
      char* top;
      char numEltsPushedOnStack = 0;
      // Pointer to the value of the current member variable
      void* pCurVarValue = 0;
      curVar = &(i->var);
      assert(curVar);

      // Only flatten static arrays when the --flatten-arrays option
      // is used.  Normally we do not have to flatten static arrays at
      // this point because we can simply visit them as an entire
      // sequence.
      if (VAR_IS_STATIC_ARRAY(curVar) &&
          fjalar_flatten_arrays &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(curVar->isString && (curVar->declaredPtrLevels == 1))) {
        // Only look at the first dimension:
        UInt arrayIndex;
        for (arrayIndex = 0; arrayIndex <= curVar->upperBounds[0]; arrayIndex++) {
          char indexStr[5];
          top = stringStackTop(fullNameStack, fullNameStackSize);

          sprintf(indexStr, "%d", arrayIndex);

          // TODO: Subtract and add is a HACK!  Subtract one from the
          // type of curVar just because we are looping through and
          // expanding the array
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count--;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          // Only derive a pointer value inside of the struct if
          // variableHasBeenObserved; else leave pCurVarValue at 0:
          if (DTRACE_FILE == outputType &&
              variableHasBeenObserved) {
            // The starting address for the member variable is the
            // struct's starting address plus the location of the
            // variable within the struct
            pCurVarValue = pValue + curVar->data_member_location;

            // Very important! Add offset within the flattened array:
            pCurVarValue += (arrayIndex * getBytesBetweenElts(curVar));
          }

          // If the top element is '*', then instead of pushing a
          // '.' to make '*.', erase that element and instead push
          // '->'.  If last element is '->', then we're fine and
          // don't do anything else.  Otherwise, push a '.'
          if (top[0] == '*') {
            stringStackPop(fullNameStack, &fullNameStackSize);
            stringStackPush(fullNameStack, &fullNameStackSize, arrow);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, arrow)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(fullNameStack, &fullNameStackSize, dot);
            numEltsPushedOnStack = 1;
          }

          stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
          stringStackPush(fullNameStack, &fullNameStackSize, "[");
          stringStackPush(fullNameStack, &fullNameStackSize, indexStr);
          stringStackPush(fullNameStack, &fullNameStackSize, "]");

          numEltsPushedOnStack += 4;


          visitSingleVar(curVar,
                         0,
                         pCurVarValue,
                         0,
                         DERIVED_FLATTENED_ARRAY_VAR,
                         trace_vars_tree,
                         OVERRIDE_NONE, // Start over again and read new .disambig entry
                         numStructsDereferenced + 1, // Notice the +1 here
                         varFuncInfo,
                         isEnter);

          // POP all the stuff we pushed on there before
          while ((numEltsPushedOnStack--) > 0) {
            stringStackPop(fullNameStack, &fullNameStackSize);
          }

          // HACK: Add the count back on at the end
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count++;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }
        }
      }
      // Regular member variable (without array flattening):
      else {
        // Only derive a pointer value inside of the struct if
        // variableHasBeenObserved; else leave pCurVarValue at 0:
        if ((DTRACE_FILE == outputType) &&
            pValue &&
            variableHasBeenObserved) {
          // The starting address for the member variable is the
          // struct's starting address plus the location of the variable
          // within the struct TODO: Are we sure that arithmetic on
          // void* basePtrValue adds by 1?  Otherwise, we'd have
          // mis-alignment issues.  (I tried it in gdb and it seems to
          // work, though.)
          pCurVarValue = pValue + curVar->data_member_location;

          // Override for D_DOUBLE types: For some reason, the DWARF2
          // info.  botches the locations of double variables within
          // structs, setting their data_member_location fields to give
          // them only 4 bytes of padding instead of 8 against the next
          // member variable.  If curVar is a double and there exists a
          // next member variable such that the difference in
          // data_member_location of this double and the next member
          // variable is exactly 4, then decrement the double's location
          // by 4 in order to give it a padding of 8:
          if ((D_DOUBLE == curVar->varType->declaredType) &&
              (i->next) &&
              ((i->next->var.data_member_location -
                curVar->data_member_location) == 4)) {
            pCurVarValue -= 4;
          }
        }

        top = stringStackTop(fullNameStack, fullNameStackSize);

        // If the top element is '*' or '[0]', then instead of pushing a
        // '.' to make '*.' or '[0].', erase that element and instead push
        // '->'.  If last element is '->', then we're fine and
        // don't do anything else.  Otherwise, push a '.'
        if ((top[0] == '*') || (VG_STREQ(top, zeroth_elt))) {
          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPush(fullNameStack, &fullNameStackSize, arrow);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, arrow)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, dot);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
        numEltsPushedOnStack++;

        visitSingleVar(curVar,
                       0,
                       pCurVarValue,
                       0,
                       (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                       trace_vars_tree,
                       OVERRIDE_NONE, // Start over again and read new .disambig entry
                       numStructsDereferenced + 1, // Notice the +1 here
                       varFuncInfo,
                       isEnter);

        // POP everything we've just pushed on
        while ((numEltsPushedOnStack--) > 0) {
          stringStackPop(fullNameStack, &fullNameStackSize);
        }
      }
    }
  }
}


// Visit a variable sequence uniquely identified by var and
// numDereferences whose values are referred to by pointers within
// pValueArray (of size numElts), and then derive additional variables
// either by dereferencing pointers or by visiting struct members.
// This function only calls visitSequence() with the same value of
// numElts because Daikon only supports one level of sequences.
// Pre: varOrigin == {DERIVED_VAR, DERIVED_FLATTENED_ARRAY_VAR}
static
void visitSequence(VariableEntry* var,
                   UInt numDereferences,
                   // Array of pointers to the current variable's values
                   void** pValueArray,
                   UInt numElts, // Size of pValueArray
                   VariableOrigin varOrigin,
                   char* trace_vars_tree,
                   DisambigOverride disambigOverride,
                   // The number of structs we have dereferenced for
                   // a particular call of visitVariable(); Starts at
                   // 0 and increments every time we hit a variable
                   // which is a base struct type
                   // Range: [0, MAX_VISIT_NESTING_DEPTH]
                   UInt numStructsDereferenced,
                   // These uniquely identify the program point
                   FunctionEntry* varFuncInfo,
                   char isEnter) {

  char* fullFjalarName = 0;
  int layersBeforeBase;

  tl_assert(var);
  layersBeforeBase = var->repPtrLevels - numDereferences;
  tl_assert(layersBeforeBase >= 0);
  tl_assert((DERIVED_VAR == varOrigin) ||
            (DERIVED_FLATTENED_ARRAY_VAR == varOrigin));

  // Special handling for overriding in the presence of .disambig:
  // Only check this for original (numDereferences == 0) variables
  // to ensure that it's only checked once per variable
  if (0 == numDereferences) {
    disambigOverride = returnDisambigOverride(var);
  }

  // Unless fjalar_output_struct_vars is on,
  // don't print out an entry for base (non-pointer) struct/union
  // variables since they have no substantive meaning for C programs.
  // They are merely represented as hashcode values, and that's kind
  // of deceiving because they aren't really pointer variables either.

  // This means that anywhere inside of this 'if' statement, we should
  // be very careful about mutating state because different state may
  // be mutated based on whether fjalar_output_struct_vars is on,
  // which may lead to different-looking results.
  if (fjalar_output_struct_vars ||
      (!((layersBeforeBase == 0) &&
         (var->varType->isStructUnionType)))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStackSize > 0);
    fullFjalarName = stringStackStrdup(fullNameStack, fullNameStackSize);

    // If we are not interested in visiting this variable or its
    // children, then PUNT:
    if (!interestedInVar(fullFjalarName, trace_vars_tree)) {
      VG_(free)(fullFjalarName);
      return;
    }

    // Perform the actual output depending on outputType:
    switch (outputType) {
    case DECLS_FILE:
      printDeclsEntry(var, fullFjalarName, varOrigin, allowVarDumpToFile,
                      layersBeforeBase, 1, disambigOverride,
                      varFuncInfo, isEnter);
      break;
    case DTRACE_FILE:
      printDtraceEntry(var,
                       numDereferences,
                       fullFjalarName,
                       0,
                       varOrigin,
                       (layersBeforeBase > 0),
                       0,
                       disambigOverride,
                       1, // YES isSequence
                       pValueArray,
                       numElts,
                       varFuncInfo,
                       isEnter);
      break;
    case DISAMBIG_FILE:
      printDisambigEntry(var, fullFjalarName);
      // DO NOT DERIVE VARIABLES for .disambig.  We are only interested
      // in printing out the variables which are immediately visible
      // to the user.  Thus, we should RETURN out of the function
      // altogether instead of simply breaking out of the switch
      return;
    case DYNCOMP_EXTRA_PROP:
      handleDynCompExtraProp(var, layersBeforeBase, varFuncInfo, isEnter);
      break;
    case FAUX_DECLS_FILE:
      // Chill and do nothing here because we're making a dry run :)
      break;
    default:
      VG_(printf)( "Error! Invalid outputType in outputDaikonVar()\n");
      abort();
      break;
    }
  }

  // We don't need the name anymore since we're done printing
  // everything about this variable by now
  VG_(free)(fullFjalarName);

  // Be very careful about where you increment this!  We want to
  // increment this once per call of either visitSingleVar() or
  // visitSequence():
  g_variableIndex++;


  // Now comes the fun part of deriving variables!

  // Dereference and keep on printing out derived variables until we
  // hit the base type.  We want to override the old pointer values
  // within pValueArray with new pointer values ascertained from
  // dereferencing each element of the array.  If a particular element
  // is un-allocated or un-initialized, then mark it with a 0.
  if (layersBeforeBase > 0) {
    // TODO: Implement static array flattening

    // We only need to set pValueArray and numElts for .dtrace output:
    // (If this variable is a static array, then there is no need to
    //  dereference pointers - very important but subtle point!)
    if ((DTRACE_FILE == outputType) &&
        !VAR_IS_STATIC_ARRAY(var)) {
      // Iterate through pValueArray and dereference each pointer
      // value if possible, then override the entries in pValueArray
      // with the dereferenced pointers (use a value of 0 for
      // unallocated or uninit)
      UInt i;
      for (i = 0; i < numElts; i++) {
        char derivedIsAllocated = 0;
        char derivedIsInitialized = 0;
        void** pValueArrayEntry = &pValueArray[i];

        // If this entry is already 0, then skip it
        if (0 == *pValueArrayEntry) {
          continue;
        }

        derivedIsAllocated = addressIsAllocated((Addr)(*pValueArrayEntry), sizeof(void*));
        if (derivedIsAllocated) {
          derivedIsInitialized = addressIsInitialized((Addr)(*pValueArrayEntry), sizeof(void*));
          if (derivedIsInitialized) {
            // Make a single dereference and override pValueArray
            // entry with the dereferenced value:
            *pValueArrayEntry = *((void **)(*pValueArrayEntry));
          }
          else {
            // TODO: We need to somehow mark this entry as 'uninit'
            *pValueArrayEntry = 0;
          }
        }
        else {
          // TODO: We need to somehow mark this entry as 'unallocated'
          *pValueArrayEntry = 0;
        }
      }
    }

    // Push 1 symbol on stack to represent single elt. dereference:

    //    if (kvasir_repair_format) {
    //      stringStackPush(fullNameStack, &fullNameStackSize, star);
    //    }
    //    else {
    stringStackPush(fullNameStack, &fullNameStackSize, zeroth_elt);
      //    }

    visitSequence(var,
                  numDereferences + 1,
                  pValueArray,
                  numElts,
                  (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                  trace_vars_tree,
                  disambigOverride,
                  numStructsDereferenced,
                  varFuncInfo,
                  isEnter);

    // Pop 1 symbol off
    stringStackPop(fullNameStack, &fullNameStackSize);
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (var->varType->isStructUnionType) {
    tl_assert(0 == layersBeforeBase);

    VarList* memberVars;
    VarNode* i;
    VariableEntry* curVar;

    // Check to see if the VisitedStructsTable contains more than
    // MAX_VISIT_STRUCT_DEPTH of the current struct type
    if (gencontains(VisitedStructsTable, (void*)(var->varType))) {
      UInt count = (UInt)(gengettable(VisitedStructsTable, (void*)(var->varType)));

      if (count <= MAX_VISIT_STRUCT_DEPTH) {
        count++;
        genputtable(VisitedStructsTable, (void*)(var->varType), (void*)count);
      }
      // PUNT because this struct has appeared more than
      // MAX_VISIT_STRUCT_DEPTH times during one call to visitVariable()
      else {
        return;
      }
    }
    // If not found in the table, initialize this entry with 1
    else {
      genputtable(VisitedStructsTable, (void*)(var->varType), (void*)1);
    }

    // If we have dereferenced more than
    // MAX_VISIT_NESTING_DEPTH structs, then simply PUNT and
    // stop deriving variables from it.
    if (numStructsDereferenced > MAX_VISIT_NESTING_DEPTH) {
      return;
    }


    // Walk down the member variables list and visit each one with the
    // current struct variable name as the prefix:
    memberVars = var->varType->memberListPtr;
    i = 0;
    curVar = 0;

    // No member variables
    if(!memberVars || !(memberVars->first))
      return;

    for (i = memberVars->first; i != 0; i = i->next) {
      UInt ind;
      void** pCurVarValueArray = 0;
      char* top;
      char numEltsPushedOnStack = 0;
      curVar = &(i->var);
      assert(curVar);

      // If a member variable is a statically-sized array which is
      // smaller than MAXIMUM_ARRAY_SIZE_TO_EXPAND and we have not
      // already performed array flattening, then we must expand the
      // member array and print it out in its flattened form with one
      // set of derived variable for every element in the array:
      if (VAR_IS_STATIC_ARRAY(curVar) &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(curVar->isString && (curVar->declaredPtrLevels == 1))) {
        // Only look at the first dimension:
        UInt arrayIndex;
        for (arrayIndex = 0; arrayIndex <= curVar->upperBounds[0]; arrayIndex++) {
          char indexStr[5];
          top = stringStackTop(fullNameStack, fullNameStackSize);

          sprintf(indexStr, "%d", arrayIndex);

          // TODO: Subtract and add is a HACK!  Subtract one from the
          // type of curVar just because we are looping through and
          // expanding the array
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count--;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          if (DTRACE_FILE == outputType) {
            // Create pCurVarValueArray to be the same size as pValueArray:
            pCurVarValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

            // Iterate though pValueArray and fill up
            // pCurVarValueArray with pointer values offset by the
            // location of the member variable within the struct plus
            // the offset given by the array index of the flattened array:
            for (ind = 0; ind < numElts; ind++) {
              // The starting address for the member variable is the
              // struct's starting address plus the location of the
              // variable within the struct
              if (pValueArray[ind]) {
                void* pCurVarValue = pValueArray[ind] + curVar->data_member_location;

                // Override for D_DOUBLE types: For some reason, the DWARF2
                // info.  botches the locations of double variables within
                // structs, setting their data_member_location fields to give
                // them only 4 bytes of padding instead of 8 against the next
                // member variable.  If curVar is a double and there exists a
                // next member variable such that the difference in
                // data_member_location of this double and the next member
                // variable is exactly 4, then decrement the double's location
                // by 4 in order to give it a padding of 8:
                if ((D_DOUBLE == curVar->varType->declaredType) &&
                    (i->next) &&
                    ((i->next->var.data_member_location -
                      curVar->data_member_location) == 4)) {
                  pCurVarValue -= 4;
                }

                // Very important!  Add the offset within the
                // flattened array:
                pCurVarValue += (arrayIndex * getBytesBetweenElts(curVar));

                // Now assign that value into pCurVarValueArray:
                pCurVarValueArray[ind] = pCurVarValue;
              }
              // If the original entry was 0, then simply copy 0, which
              // propagates uninit/unallocated status from structs to
              // members.
              else {
                pCurVarValueArray[ind] = 0;
              }
            }
          }

          // If the top element is '*', then instead of pushing a
          // '.' to make '*.', erase that element and instead push
          // '->'.  If last element is '->', then we're fine and
          // don't do anything else.  Otherwise, push a '.'
          if (top[0] == '*') {
            stringStackPop(fullNameStack, &fullNameStackSize);
            stringStackPush(fullNameStack, &fullNameStackSize, arrow);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, arrow)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(fullNameStack, &fullNameStackSize, dot);
            numEltsPushedOnStack = 1;
          }

          stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
          stringStackPush(fullNameStack, &fullNameStackSize, "[");
          stringStackPush(fullNameStack, &fullNameStackSize, indexStr);
          stringStackPush(fullNameStack, &fullNameStackSize, "]");

          numEltsPushedOnStack += 4;

          visitSequence(curVar,
                        0,
                        pCurVarValueArray,
                        numElts,
                        DERIVED_FLATTENED_ARRAY_VAR,
                        trace_vars_tree,
                        OVERRIDE_NONE,
                        numStructsDereferenced + 1, // Notice the +1 here
                        varFuncInfo,
                        isEnter);

          // POP all the stuff we pushed on there before
          while ((numEltsPushedOnStack--) > 0) {
            stringStackPop(fullNameStack, &fullNameStackSize);
          }

          // HACK: Add the count back on at the end
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            int count = (int)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count++;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          // Only free if necessary
          if (pCurVarValueArray) {
            VG_(free)(pCurVarValueArray);
            pCurVarValueArray = 0;
          }
        }
      }
      // Regular member variable (without array flattening):
      else {

        if (DTRACE_FILE == outputType) {
          // Create pCurVarValueArray to be the same size as pValueArray:
          pCurVarValueArray = (void**)VG_(malloc)(numElts * sizeof(void*));

          // Iterate though pValueArray and fill up pCurVarValueArray
          // with pointer values offset by the location of the member
          // variable within the struct:
          for (ind = 0; ind < numElts; ind++) {
            // The starting address for the member variable is the
            // struct's starting address plus the location of the
            // variable within the struct TODO: Are we sure that
            // arithmetic on void* basePtrValue adds by 1?  Otherwise,
            // we'd have mis-alignment issues.  (I tried it in gdb and
            // it seems to work, though.)
            if (pValueArray[ind]) {
              void* pCurVarValue = pValueArray[ind] + curVar->data_member_location;

              // Override for D_DOUBLE types: For some reason, the DWARF2
              // info.  botches the locations of double variables within
              // structs, setting their data_member_location fields to give
              // them only 4 bytes of padding instead of 8 against the next
              // member variable.  If curVar is a double and there exists a
              // next member variable such that the difference in
              // data_member_location of this double and the next member
              // variable is exactly 4, then decrement the double's location
              // by 4 in order to give it a padding of 8:
              if ((D_DOUBLE == curVar->varType->declaredType) &&
                  (i->next) &&
                  ((i->next->var.data_member_location -
                    curVar->data_member_location) == 4)) {
                pCurVarValue -= 4;
              }

              // Now assign that value into pCurVarValueArray:
              pCurVarValueArray[ind] = pCurVarValue;
            }
            // If the original entry was 0, then simply copy 0, which
            // propagates uninit/unallocated status from structs to
            // members.
            else {
              pCurVarValueArray[ind] = 0;
            }
          }
        }

        top = stringStackTop(fullNameStack, fullNameStackSize);

        // If the top element is '*' or '[0]', then instead of pushing a
        // '.' to make '*.' or '[0].', erase that element and instead push
        // '->'.  If last element is '->', then we're fine and
        // don't do anything else.  Otherwise, push a '.'
        if ((top[0] == '*') || (VG_STREQ(top, zeroth_elt))) {
          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPush(fullNameStack, &fullNameStackSize, arrow);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, arrow)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, dot);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
        numEltsPushedOnStack++;

        visitSequence(curVar,
                      0,
                      pCurVarValueArray,
                      numElts,
                      (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                      trace_vars_tree,
                      OVERRIDE_NONE,
                      numStructsDereferenced + 1, // Notice the +1 here
                      varFuncInfo,
                      isEnter);

        // POP everything we've just pushed on
        while ((numEltsPushedOnStack--) > 0) {
          stringStackPop(fullNameStack, &fullNameStackSize);
        }

        // Only free if necessary
        if (pCurVarValueArray) {
          VG_(free)(pCurVarValueArray);
          pCurVarValueArray = 0;
        }
      }
    }
  }
}
