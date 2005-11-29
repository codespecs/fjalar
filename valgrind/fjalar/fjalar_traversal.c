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
#include "fjalar_main.h"
#include "fjalar_select.h"
#include "generate_fjalar_entries.h"
#include "disambig.h"
#include "mc_include.h"

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

extern FunctionTree* globalFunctionTree;

// Symbols for Fjalar variable names that are created by concatenating
// together struct, array, and field names:
char* DEREFERENCE = "[]";
char* ZEROTH_ELT = "[0]";
char* DOT = ".";
char* ARROW = "->";
char* STAR = "*";

// This stack represents the full name of the variable that we
// currently want to output (Only puts REFERENCES to strings in
// fullNameStack; does not do any allocations)
#define MAX_STRING_STACK_SIZE 100

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


// Takes a TypeEntry* and a pointer to it, and traverses through all
// of the members of the specified class (or struct/union).  This
// should also traverse inside of the class's superclasses and visit
// variables in them as well.
// Pre: class->decType == {D_STRUCT, D_UNION}
void visitClassMemberVariables(TypeEntry* class,
                               Addr objectAddr,
                               // This function performs an action for each variable visited:
                               TraversalResult (*performAction)(VariableEntry*,
                                                                char*,
                                                                VariableOrigin,
                                                                UInt,
                                                                UInt,
                                                                char,
                                                                DisambigOverride,
                                                                char,
                                                                void*,
                                                                void**,
                                                                UInt,
                                                                FunctionEntry*,
                                                                char)) {
  tl_assert((class->decType == D_STRUCT) ||
            (class->decType == D_UNION));

  // Visit member variables:
  if (class->memberVarList) {
    VarNode* i = NULL;
    for (i = class->memberVarList->first;
         i != NULL;
         i = i->next) {
      VariableEntry* var;
      Addr memberVarAddr = 0;
      var = i->var;

      if (!var->name) {
	VG_(printf)( "  Warning! Weird null member variable name!\n");
	continue;
      }

      // Calculate the offset from the beginning of the structure
      // (Don't bother to calculate the member variable address if we
      // don't even pass in objectAddr):
      if (objectAddr) {
        memberVarAddr = objectAddr + var->data_member_location;
      }

      stringStackPush(fullNameStack, &fullNameStackSize, var->name);

      visitVariable(var,
                    (void*)memberVarAddr,
                    0,
                    1, // This is 1 because we are assuming we've already visited the struct called 'this'
                    performAction,
                    GLOBAL_VAR, // not quite ... but seems to work for now
                    0,
                    0);

      stringStackPop(fullNameStack, &fullNameStackSize);
    }
  }

  // Now traverse inside of all superclasses and visit all of their
  // member variables (while appending a prefix to them):
  if (class->superclassList) {
    SimpleNode* n = NULL;
    for (n = class->superclassList->first;
         n != NULL;
         n = n->next) {
      Superclass* curSuper = (Superclass*)(n->elt);
      tl_assert(curSuper && curSuper->class);

      // Push a name prefix to denote that we are traversing into a
      // superclass:
      stringStackPush(fullNameStack, &fullNameStackSize, curSuper->className);
      stringStackPush(fullNameStack, &fullNameStackSize, "(super).");

      // This recursive call will handle multiple levels of
      // inheritance (e.g., if A extends B, B extends C, and C extends
      // D, then A will get all of its members visited, then visit the
      // members of B, then C, then D):
      visitClassMemberVariables(curSuper->class,
                                // IMPORTANT to add this offset, even
                                // though most of the time, it will be
                                // 0 except when you have multiple
                                // inheritance:
                                objectAddr + curSuper->member_var_offset,
                                performAction);

      stringStackPop(fullNameStack, &fullNameStackSize);
      stringStackPop(fullNameStack, &fullNameStackSize);
    }
  }

  // TODO: Visit static member variables (remember that they have
  // global addresses):
}

// Visits an entire group of variables, depending on the value of varOrigin:
// If varOrigin == GLOBAL_VAR, then visit all global variables
// If varOrigin == FUNCTION_FORMAL_PARAM, then visit all formal parameters
// of the function denoted by funcPtr
// If varOrigin == FUNCTION_RETURN_VAR, then visit the return value variable
// of the function denoted by funcPtr (use visitReturnValue() if you
// want to grab the actual return value at runtime and not just the name)
void visitVariableGroup(VariableOrigin varOrigin,
                        FunctionEntry* funcPtr, // 0 for unspecified function
                        char isEnter,           // 1 for function entrance, 0 for exit
                        char* stackBaseAddr,    // should only be used for FUNCTION_FORMAL_PARAM
                        // This function performs an action for each variable visited:
                        TraversalResult (*performAction)(VariableEntry*,
                                                         char*,
                                                         VariableOrigin,
                                                         UInt,
                                                         UInt,
                                                         char,
                                                         DisambigOverride,
                                                         char,
                                                         void*,
                                                         void**,
                                                         UInt,
                                                         FunctionEntry*,
                                                         char)) {
  VarNode* i = 0;

  VarList* varListPtr = 0;

  // If funcPtr is null, then you better be GLOBAL_VAR
  if (!funcPtr) {
    tl_assert(varOrigin == GLOBAL_VAR);
  }

  // You shouldn't be passing in a stackBaseAddr if you're not
  // interested in visiting function formal params:
  if (stackBaseAddr) {
    tl_assert(varOrigin == FUNCTION_FORMAL_PARAM);
  }

  switch (varOrigin) {
  case GLOBAL_VAR:
    // Punt if we are ignoring globals!
    if (fjalar_ignore_globals) {
      return;
    }
    varListPtr = &globalVars;
    break;
  case FUNCTION_FORMAL_PARAM:
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

  tl_assert(varListPtr);

  for (i = varListPtr->first;
       i != NULL;
       i = i->next) {
      VariableEntry* var;
      void* basePtrValue = 0;

      var = i->var;

      if (!var->name) {
	VG_(printf)( "  Warning! Weird null variable name!\n");
	continue;
      }

      if (varOrigin == FUNCTION_FORMAL_PARAM) {
        basePtrValue = (void*)((int)stackBaseAddr + var->byteOffset);
      }
      else if (varOrigin == GLOBAL_VAR) {
        basePtrValue = (void*)(var->globalLocation);

        // if "--ignore-static-vars" option was selected, do not visit
        // file-static global variables:
        if (!var->isExternal && fjalar_ignore_static_vars) {
          continue;
        }

        // If "--limit-static-vars" option was selected, then:
        // * Only visit file-static variables at program points
        //   in the file in which the variables were declared
        // * Only visit static variables declared within functions
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
      }

      stringStackPush(fullNameStack, &fullNameStackSize, var->name);

      visitVariable(var,
                    basePtrValue,
                    0,
                    0,
                    performAction,
                    varOrigin,
                    funcPtr,
                    isEnter);

      stringStackPop(fullNameStack, &fullNameStackSize);
    }
}


// Grabs the appropriate return value of the function denoted by the
// execution state 'e' from Valgrind simulated registers and visits
// the variables to perform some action.  This differs from calling
// visitVariableGroup() with the FUNCTION_RETURN_VAR parameter because
// it actually grabs the appropriate value from the simulated
// registers.
void visitReturnValue(FunctionExecutionState* e,
                      // This function performs an action for each variable visited:
                      TraversalResult (*performAction)(VariableEntry*,
                                                       char*,
                                                       VariableOrigin,
                                                       UInt,
                                                       UInt,
                                                       char,
                                                       DisambigOverride,
                                                       char,
                                                       void*,
                                                       void**,
                                                       UInt,
                                                       FunctionEntry*,
                                                       char)) {
  VarNode* cur_node;
  FunctionEntry* funcPtr;
  tl_assert(e);

  funcPtr = e->func;
  tl_assert(funcPtr);

  // We need to push the return value name onto the string stack!
  stringStackClear(&fullNameStackSize);

  cur_node = funcPtr->returnValue.first;

  // This happens when there is a void function with no return value:
  if (!cur_node) {
    return;
  }

  tl_assert(cur_node->var);
  tl_assert(cur_node->var->name);
  tl_assert(cur_node->var->varType);

  stringStackPush(fullNameStack, &fullNameStackSize, cur_node->var->name);

  // Struct/union type - use EAX but remember that EAX holds
  // a POINTER to the struct/union so we must dereference appropriately
  // WE NEED TO CHECK THAT declaredPtrLevels == 0 since we need a
  // real struct/union, not just a pointer to one
  // BE CAREFUL WITH declaredType - it may be misleading since all
  // pointers share the same declaredType
  if ((cur_node->var->ptrLevels == 0) &&
      (cur_node->var->varType->isStructUnionType)) {
    // e->EAX is the contents of the virtual EAX, which should be the
    // address of the struct/union, so pass that along ...  NO extra
    // level of indirection needed

    visitVariable(cur_node->var,
                  (void*)e->EAX,
                  // No longer need to overrideIsInitialized
                  // because we now keep shadow V-bits for e->EAX
                  // and friends
                  0, // e->EAXvalid,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  // Floating-point type - use FPU
  else if ((cur_node->var->ptrLevels == 0) &&
	   ((cur_node->var->varType->decType == D_FLOAT) ||
            (cur_node->var->varType->decType == D_DOUBLE) ||
            (cur_node->var->varType->decType == D_LONG_DOUBLE) ||
            (cur_node->var->varType->decType == D_UNSIGNED_FLOAT) ||
            (cur_node->var->varType->decType == D_UNSIGNED_DOUBLE) ||
            // TODO: I dunno if long doubles fit in the FPU registers
            (cur_node->var->varType->decType == D_UNSIGNED_LONG_DOUBLE))) {
    // SPECIAL CASE: The value in FPU must be interpreted as a double
    // even if its true type may be a float
    visitVariable(cur_node->var,
                  &(e->FPU),
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  // Remember that long long int types use EAX as the low 4 bytes
  // and EDX as the high 4 bytes
  // long long ints - create a long long int and pass its address
  else if ((cur_node->var->ptrLevels == 0) &&
           (cur_node->var->varType->decType == D_UNSIGNED_LONG_LONG_INT)) {
    unsigned long long int uLong = (e->EAX) | (((unsigned long long int)(e->EDX)) << 32);

    // Remember to copy A and V-bits over:
    mc_copy_address_range_state((Addr)(&(e->EAX)),
                                (Addr)(&uLong),
                                sizeof(e->EAX));

    mc_copy_address_range_state((Addr)(&(e->EDX)),
                                (Addr)(&uLong) + (Addr)sizeof(e->EAX),
                                sizeof(e->EDX));

    visitVariable(cur_node->var,
                  &uLong,
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  else if ((cur_node->var->ptrLevels == 0) &&
           (cur_node->var->varType->decType == D_LONG_LONG_INT)) {
    long long int signedLong = (e->EAX) | (((long long int)(e->EDX)) << 32);

    // Remember to copy A and V-bits over:
    mc_copy_address_range_state((Addr)(&(e->EAX)),
                                (Addr)(&signedLong),
                                sizeof(e->EAX));

    mc_copy_address_range_state((Addr)(&(e->EDX)),
                                (Addr)(&signedLong) + (Addr)sizeof(e->EAX),
                                sizeof(e->EDX));

    visitVariable(cur_node->var,
                  &signedLong,
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  // All other types (integer and pointer) - use EAX
  else {
    // Need an additional indirection level
    FJALAR_DPRINTF(" RETURN - int/ptr.: cur_node=%p, basePtr=%p\n",
                   cur_node, &(e->EAX));

    visitVariable(cur_node->var,
                  &(e->EAX),
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }

  stringStackPop(fullNameStack, &fullNameStackSize);
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
                    // This function performs an action for each variable visited:
                    TraversalResult (*performAction)(VariableEntry*,
                                                     char*,
                                                     VariableOrigin,
                                                     UInt,
                                                     UInt,
                                                     char,
                                                     DisambigOverride,
                                                     char,
                                                     void*,
                                                     void**,
                                                     UInt,
                                                     FunctionEntry*,
                                                     char),
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
                   // This function performs an action for each variable visited:
                   TraversalResult (*performAction)(VariableEntry*,
                                                    char*,
                                                    VariableOrigin,
                                                    UInt,
                                                    UInt,
                                                    char,
                                                    DisambigOverride,
                                                    char,
                                                    void*,
                                                    void**,
                                                    UInt,
                                                    FunctionEntry*,
                                                    char),
                   VariableOrigin varOrigin,
                   char* trace_vars_tree,
                   DisambigOverride disambigOverride,
                   UInt numStructsDereferenced,
                   FunctionEntry* varFuncInfo,
                   char isEnter);

// This is an example of a function that's valid to be passed in as
// the performAction parameter to visitVariable:
/*
TraversalResult performAction(VariableEntry* var,
                              char* varName,
                              VariableOrigin varOrigin,
                              UInt numDereferences,
                              UInt layersBeforeBase,
                              char overrideIsInit,
                              DisambigOverride disambigOverride,
                              char isSequence,
                              // pValue only valid if isSequence is false
                              void* pValue,
                              // pValueArray and numElts only valid if
                              // isSequence is true
                              void** pValueArray,
                              UInt numElts,
                              FunctionEntry* varFuncInfo,
                              char isEnter);
*/

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
                   // This should almost always be 0, but whenever you
                   // want finer control over struct dereferences, you
                   // can override this with a number representing the
                   // number of structs you have dereferenced so far
                   // to get here (this is useful for the 'this'
                   // parameter of member functions):
                   UInt numStructsDereferenced,
                   // This function performs an action for each variable visited:
                   TraversalResult (*performAction)(VariableEntry*,
                                                    char*,
                                                    VariableOrigin,
                                                    UInt,
                                                    UInt,
                                                    char,
                                                    DisambigOverride,
                                                    char,
                                                    void*,
                                                    void**,
                                                    UInt,
                                                    FunctionEntry*,
                                                    char),
                   VariableOrigin varOrigin,
                   FunctionEntry* varFuncInfo,
                   char isEnter) {

  char* trace_vars_tree = 0;

  tl_assert(varOrigin != DERIVED_VAR);
  tl_assert(varOrigin != DERIVED_FLATTENED_ARRAY_VAR);

  // In preparation for a new round of variable visits, initialize a
  // new VisitedStructsTable, freeing an old one if necessary
  if (VisitedStructsTable) {
    genfreehashtable(VisitedStructsTable);
    VisitedStructsTable = 0;
  }
  VisitedStructsTable = genallocatehashtable(0,
                                             (int (*)(void *,void *)) &equivalentIDs);

  // Also initialize trace_vars_tree based on varOrigin and
  // varFuncInfo:
  if (varOrigin == GLOBAL_VAR) {
    trace_vars_tree = (globalFunctionTree ?
                globalFunctionTree->function_variables_tree : 0);
  }
  else {
    trace_vars_tree = varFuncInfo->trace_vars_tree;
  }

  // Delegate:
  visitSingleVar(var,
                 0,
                 pValue,
                 overrideIsInit,
                 performAction,
                 varOrigin,
                 trace_vars_tree,
                 OVERRIDE_NONE,
                 numStructsDereferenced,
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
                    // This function performs an action for each variable visited:
                    TraversalResult (*performAction)(VariableEntry*,
                                                     char*,
                                                     VariableOrigin,
                                                     UInt,
                                                     UInt,
                                                     char,
                                                     DisambigOverride,
                                                     char,
                                                     void*,
                                                     void**,
                                                     UInt,
                                                     FunctionEntry*,
                                                     char),
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

  TraversalResult tResult = INVALID_RESULT;

  tl_assert(var);
  layersBeforeBase = var->ptrLevels - numDereferences;

  // Special hack for strings:
  if (var->isString && (layersBeforeBase > 0)) {
    layersBeforeBase--;
    //    VG_(printf)("var: %s is string - layersBeforeBase: %d\n",
    //                var->name, layersBeforeBase);
  }

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
      ((varOrigin == FUNCTION_FORMAL_PARAM) ||
       (varOrigin == FUNCTION_RETURN_VAR))) {
    disambigOverride = OVERRIDE_ARRAY_AS_POINTER;
  }

  disambigOverrideArrayAsPointer =
    (OVERRIDE_ARRAY_AS_POINTER == disambigOverride);

  derefSingleElement = disambigOverrideArrayAsPointer;


  // Unless fjalar_output_struct_vars is on, don't perform any action
  // for base (non-pointer) struct/union variables since they have no
  // substantive meaning for C programs.  We are only interested in
  // the fields of the struct, not the struct itself.

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

    // Perform the action action for this particular variable:
    tResult = (*performAction)(var,
                               fullFjalarName,
                               varOrigin,
                               numDereferences,
                               layersBeforeBase,
                               overrideIsInit,
                               disambigOverride,
                               0,
                               pValue,
                               0,
                               0,
                               varFuncInfo,
                               isEnter);

    tl_assert(tResult != INVALID_RESULT);

    // We don't need the name anymore since we're done printing
    // everything about this variable by now
    VG_(free)(fullFjalarName);

    // Punt!
    if (tResult == STOP_TRAVERSAL) {
      return;
    }
  }

  // This is an ugly hack that's required to properly not visit base
  // struct variables but still make sure that derived variables are
  // properly visited.  When we encounter a base struct variable, we
  // need to set DEREF_MORE_POINTERS because we need its member
  // variables to be properly visited:
  if ((layersBeforeBase == 0) &&
      (var->varType->isStructUnionType)) {
    tResult = DEREF_MORE_POINTERS;
  }

  // Be very careful about where you increment this!  We want to
  // increment this once per call of either visitSingleVar() or
  // visitSequence():
  g_variableIndex++;

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
      // VERY IMPORTANT: Only derive by dereferencing pointers if
      // tResult == DEREF_MORE_POINTERS:
      if (pValue && (tResult == DEREF_MORE_POINTERS)) {
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

      // TODO: Re-factor all of this repair tool stuff:
      //      if (kvasir_repair_format) {
      //        stringStackPush(fullNameStack, &fullNameStackSize, STAR);
      //      }
      //      else {
      stringStackPush(fullNameStack, &fullNameStackSize, ZEROTH_ELT);
        //      }

      visitSingleVar(var,
                     numDereferences + 1,
                     pNewValue,
                     overrideIsInit,
                     performAction,
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
      // VERY IMPORTANT: Only derive by dereferencing pointers if
      // tResult == DEREF_MORE_POINTERS:
      if (pValue && (tResult == DEREF_MORE_POINTERS)) {
        // Static array:
        if (var->isStaticArray) {
          // Flatten multi-dimensional arrays by treating them as one
          // giant single-dimensional array.  Take the products of the
          // sizes of all dimensions (remember to add 1 to each to get
          // from upper bound to size):
          int dim;

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
      stringStackPush(fullNameStack, &fullNameStackSize, DEREFERENCE);

      visitSequence(var,
                    numDereferences + 1,
                    pValueArray,
                    numElts,
                    performAction,
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
    memberVars = var->varType->memberVarList;
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
      curVar = i->var;
      assert(curVar);

      // Only flatten static arrays when the --flatten-arrays option
      // is used.  Normally we do not have to flatten static arrays at
      // this point because we can simply visit them as an entire
      // sequence.
      if (curVar->isStaticArray &&
          fjalar_flatten_arrays &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(curVar->isString && (curVar->ptrLevels == 1))) {
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
          // (tResult == DEREF_MORE_POINTERS); else leave pCurVarValue
          // at 0:
          if (tResult == DEREF_MORE_POINTERS) {
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
            stringStackPush(fullNameStack, &fullNameStackSize, ARROW);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, ARROW)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(fullNameStack, &fullNameStackSize, DOT);
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
                         performAction,
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
        // (tResult == DEREF_MORE_POINTERS); else leave pCurVarValue at 0:
        if (pValue && (tResult == DEREF_MORE_POINTERS)) {
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
          if ((D_DOUBLE == curVar->varType->decType) &&
              (i->next) &&
              ((i->next->var->data_member_location -
                curVar->data_member_location) == 4)) {
            pCurVarValue -= 4;
          }
        }

        top = stringStackTop(fullNameStack, fullNameStackSize);

        // If the top element is '*' or '[0]', then instead of pushing a
        // '.' to make '*.' or '[0].', erase that element and instead push
        // '->'.  If last element is '->', then we're fine and
        // don't do anything else.  Otherwise, push a '.'
        if ((top[0] == '*') || (VG_STREQ(top, ZEROTH_ELT))) {
          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPush(fullNameStack, &fullNameStackSize, ARROW);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, ARROW)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, DOT);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
        numEltsPushedOnStack++;

        visitSingleVar(curVar,
                       0,
                       pCurVarValue,
                       0,
                       performAction,
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
// numElts because Fjalar currently only supports one level of sequences.
// Pre: varOrigin == {DERIVED_VAR, DERIVED_FLATTENED_ARRAY_VAR}
static
void visitSequence(VariableEntry* var,
                   UInt numDereferences,
                   // Array of pointers to the current variable's values
                   void** pValueArray,
                   UInt numElts, // Size of pValueArray
                   // This function performs an action for each variable visited:
                   TraversalResult (*performAction)(VariableEntry*,
                                                    char*,
                                                    VariableOrigin,
                                                    UInt,
                                                    UInt,
                                                    char,
                                                    DisambigOverride,
                                                    char,
                                                    void*,
                                                    void**,
                                                    UInt,
                                                    FunctionEntry*,
                                                    char),
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

  TraversalResult tResult = INVALID_RESULT;

  tl_assert(var);
  layersBeforeBase = var->ptrLevels - numDereferences;

  // Special hack for strings:
  if (var->isString && (layersBeforeBase > 0)) {
    layersBeforeBase--;
    //    VG_(printf)("var: %s is string - layersBeforeBase: %d\n",
    //                var->name, layersBeforeBase);
  }

  tl_assert(layersBeforeBase >= 0);
  tl_assert((DERIVED_VAR == varOrigin) ||
            (DERIVED_FLATTENED_ARRAY_VAR == varOrigin));

  // Special handling for overriding in the presence of .disambig:
  // Only check this for original (numDereferences == 0) variables
  // to ensure that it's only checked once per variable
  if (0 == numDereferences) {
    disambigOverride = returnDisambigOverride(var);
  }

  // Unless fjalar_output_struct_vars is on, don't perform any action
  // for base (non-pointer) struct/union variables since they have no
  // substantive meaning for C programs.  We are only interested in
  // the fields of the struct, not the struct itself.

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

    // Perform the action action for this particular variable:
    tResult = (*performAction)(var,
                               fullFjalarName,
                               varOrigin,
                               numDereferences,
                               layersBeforeBase,
                               0, // Do not overrideIsInit
                               disambigOverride,
                               1, // YES isSequence
                               0,
                               pValueArray,
                               numElts,
                               varFuncInfo,
                               isEnter);

    tl_assert(tResult != INVALID_RESULT);

    // We don't need the name anymore since we're done printing
    // everything about this variable by now
    VG_(free)(fullFjalarName);

    // Punt!
    if (tResult == STOP_TRAVERSAL) {
      return;
    }
  }

  // This is an ugly hack that's required to properly not visit base
  // struct variables but still make sure that derived variables are
  // properly visited.  When we encounter a base struct variable, we
  // need to set DEREF_MORE_POINTERS because we need its member
  // variables to be properly visited:
  if ((layersBeforeBase == 0) &&
      (var->varType->isStructUnionType)) {
    tResult = DEREF_MORE_POINTERS;
  }

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

    // (If this variable is a static array, then there is no need to
    //  dereference pointers - very important but subtle point!)
    if (pValueArray && !var->isStaticArray) {
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
    //      stringStackPush(fullNameStack, &fullNameStackSize, STAR);
    //    }
    //    else {
    stringStackPush(fullNameStack, &fullNameStackSize, ZEROTH_ELT);
      //    }

    visitSequence(var,
                  numDereferences + 1,
                  pValueArray,
                  numElts,
                  performAction,
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
    memberVars = var->varType->memberVarList;
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
      curVar = i->var;
      assert(curVar);

      // If a member variable is a statically-sized array which is
      // smaller than MAXIMUM_ARRAY_SIZE_TO_EXPAND and we have not
      // already performed array flattening, then we must expand the
      // member array and print it out in its flattened form with one
      // set of derived variable for every element in the array:
      if (curVar->isStaticArray &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(curVar->isString && (curVar->ptrLevels == 1))) {
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

          if ((tResult == DEREF_MORE_POINTERS) ||
              (tResult == DO_NOT_DEREF_MORE_POINTERS)) {
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
                if ((D_DOUBLE == curVar->varType->decType) &&
                    (i->next) &&
                    ((i->next->var->data_member_location -
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
            stringStackPush(fullNameStack, &fullNameStackSize, ARROW);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, ARROW)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(fullNameStack, &fullNameStackSize, DOT);
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
                        performAction,
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

        if ((tResult == DEREF_MORE_POINTERS) ||
            (tResult == DO_NOT_DEREF_MORE_POINTERS)) {
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
              if ((D_DOUBLE == curVar->varType->decType) &&
                  (i->next) &&
                  ((i->next->var->data_member_location -
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
        if ((top[0] == '*') || (VG_STREQ(top, ZEROTH_ELT))) {
          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPush(fullNameStack, &fullNameStackSize, ARROW);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, ARROW)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(fullNameStack, &fullNameStackSize, DOT);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(fullNameStack, &fullNameStackSize, curVar->name);
        numEltsPushedOnStack++;

        visitSequence(curVar,
                      0,
                      pCurVarValueArray,
                      numElts,
                      performAction,
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
