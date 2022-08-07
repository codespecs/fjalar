/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_traversal.c:
   Functions for traversing through data structures at run time
*/


#include "my_libc.h"

#include "fjalar_traversal.h"
#include "fjalar_main.h"
#include "fjalar_select.h"
#include "generate_fjalar_entries.h"
#include "disambig.h"
#include "mc_include.h"

#include "pub_tool_threadstate.h"

// This increments every time a call to visitSingleVar() or
// visitSequence() is made.  It is up to the caller to reset this
// properly!
int g_variableIndex = 0;

// Somewhat dirty hack. Since superclass parsing is handled recursively
// and by the same function that handles struct parsing, I need to
// differentiate whether or not the current variable belongs to a super
// class.
static int traversing_super = 0;

extern FunctionTree* globalFunctionTree;

// Contains all the arguments needed for one of the visit functions.
// All of the visit functions are recursive. For example for
// the variable:

// struct A {
//   struct B {
//     int c;
//   } b[5]
// } a

// The callgraph would look like:
// visitSingleVar(a) -> visitSequence(b) -> visitSequence(c)

typedef struct _VisitArgs {
  TypeEntry* class; // Only relevant for C++ objects
  VariableEntry* var;
  Bool isSequence;
  UInt numDereferences;

  // Pointer to the location of the variable's
  // current value in memory:
  Addr pValue;
  // Address of value in client program's memory.
  Addr pValueGuest;

  // pValueArray only valid if isSequence is true.
  // contains an array of pointers to values.
  Addr* pValueArray;
  // Address of array in client program's memory.
  Addr* pValueArrayGuest;
  UInt numElts;

  // We only use overrideIsInit when we pass in
  // things (e.g. return values) that cannot be
  // checked by the Memcheck A and V bits. Never have
  // overrideIsInit when you derive variables (make
  // recursive calls) because their addresses are
  // different from the original's
  Bool overrideIsInit;

  // only relevant for C++ reference parameters
  Bool alreadyDerefedCppRef;

  // This function performs an action for each variable visited:
  TraversalAction *performAction;

  VariableOrigin varOrigin;
  char* trace_vars_tree;
  DisambigOverride disambigOverride;

  // The number of structs we have dereferenced for
  // a particular call of visitVariable(); Starts at
  // 0 and increments every time we hit a variable
  // which is a base struct type
  // Range: [0, fjalar_max_visit_nesting_depth]
  UInt numStructsDereferenced;
  // These uniquely identify the program point
  FunctionEntry* varFuncInfo;
  Bool isEnter;
  TraversalResult tResult;
} VisitArgs;


static
void visitSingleVar(VisitArgs* visit_args);

static
void visitSequence(VisitArgs* visit_args);

void visitClassMemberVariables(VisitArgs* args);

// This is an example of a function that's valid to be passed in as
// the performAction parameter to visitVariable:
/*
TraversalResult performAction(VariableEntry* var,
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
                              Bool isEnter);
*/


// Symbols for Fjalar variable names that are created by concatenating
// together struct, array, and field names:
const HChar* DEREFERENCE = "[]";
const HChar* ZEROTH_ELT = "[0]";
const HChar* DOT = ".";
const HChar* ARROW = "->";
const HChar* STAR = "*";

// This stack represents the full name of the variable that we
// currently want to output (Only puts REFERENCES to strings in
// fullNameStack; does not do any allocations)

// This stack keeps track of all components of the full name of the
// variable that's currently being visited.  E.g., for a variable
// "foo->bar[]", this stack may contain something like:
//   {"foo", "->", "bar", "[]"}.

// Doing stringStackStrdup() on this stack will result in a full
// variable name.

StringStack fullNameStack = { {0,}, 0};

// This stack keeps the FULL names of all variables above the current
// one in the stack (that is, all of the current variable's
// ancestors).  For example, for a variable "foo->bar[]", this stack
// may contain something like: {"foo", "foo->bar"}.
StringStack enclosingVarNamesStack = { {0,}, 0};

void stringStackPush(StringStack *stack, const HChar* str1)
{
  tl_assert(str1 && stack->size < MAX_STRING_STACK_SIZE);

  //Don't allow null strings at all:
  if (!str1) {
    printf( "Null string passed to push!\n");
    my_abort();
    str1 = "<null>";
  }

  stack->stack[stack->size] = str1;
  stack->size++;
}

const HChar* stringStackPop(StringStack *stack)
{
  const HChar* temp;
  tl_assert(stack->size > 0);

  temp = stack->stack[stack->size - 1];
  stack->size--;

  return temp;
}

const HChar* stringStackTop(StringStack *stack)
{
  return stack->stack[stack->size - 1];
}

void stringStackClear(StringStack *stack)
{
  (stack->size) = 0;
}

// Returns: Total length of all strings on stringStack
int stringStackStrLen(StringStack *stack)
{
  int i;
  int total = 0;
  for (i = stack->size - 1; i >=0; i--)
    {
      total+=VG_(strlen)(stack->stack[i]);
    }
  return total;
}

void stringStackPrint(StringStack *stack)
{
  int i;
  for (i = stack->size - 1; i >= 0; i--)
    {
      printf("stringStack[%d] = %s\n", i, stack->stack[i]);
    }
}

// Takes all of the strings on stringStack, copies them into a newly
// calloc'ed string (in a queue-like FIFO order), and returns a
// pointer to that string.
const HChar* stringStackStrdup(StringStack *stack)
{
  // Extra 1 for trailing '\0'
  int totalStrLen = stringStackStrLen(stack) + 1;
  char* fullName = (char*)VG_(calloc)("fjalar_traversal.c: sSSd" ,totalStrLen, sizeof(char));
  int i;

  for (i = 0; i < stack->size; i++) {
    VG_(strcat)(fullName, stack->stack[i]);
  }
  return fullName;
}


// Visits all member variables of the class and superclass without
// regard to actually grabbing pointer values.  This is useful for
// printing out names and performing other non-value-dependent
// operations.
void visitClassMembersNoValues(TypeEntry* class,
                               TraversalAction *performAction) {

  VisitArgs new_args;
  const HChar *fullFjalarName = NULL, *top = NULL;

  if (VisitedStructsTable) {
    genfreehashtable(VisitedStructsTable);
    VisitedStructsTable = NULL;
  }

  // Use a small hashtable to save time and space:
  VisitedStructsTable =
    genallocateSMALLhashtable(0, (int (*)(void *,void *)) &equivalentIDs);

  // RUDD 2.0 Making use of EnclosingVarStack to keep track of
  // struct/class members.
  // (comment added 2008)  
  // TODO: Make this less string based
  top = stringStackTop(&fullNameStack);

  FJALAR_DPRINTF("visitClassMembersNoValues top: %s (%p)\n", top, (void *)top);

    //Need a proper enclosing variable name
  if ((top && VG_STREQ(top, DOT)) ||
      (top && VG_STREQ(top, ZEROTH_ELT)) ||
      (top && VG_STREQ(top, ARROW))) {
    stringStackPop(&fullNameStack);
    fullFjalarName = stringStackStrdup(&fullNameStack);
    if (fullFjalarName) {
      stringStackPush(&enclosingVarNamesStack, fullFjalarName);
    }
    stringStackPush(&fullNameStack, top);
  }
  else {
    fullFjalarName = stringStackStrdup(&fullNameStack);
    if (fullFjalarName) {
      stringStackPush(&enclosingVarNamesStack, fullFjalarName);
    }
  }


  new_args.class                  = class;
  new_args.pValue                 = (Addr) NULL;
  new_args.pValueGuest            = (Addr) NULL;
  new_args.isSequence             = False;
  new_args.pValueArray            = NULL;
  new_args.pValueArrayGuest       = NULL;
  new_args.numElts                = 0;
  new_args.performAction          = performAction;
  // This is ignored since there's nothing being printed
  // let's give the value something sane regardless.
  new_args.varOrigin              = GLOBAL_VAR;
  new_args.trace_vars_tree        = NULL;
  new_args.numStructsDereferenced = 0;
  new_args.isEnter                = False;
  new_args.tResult                = INVALID_RESULT;
  new_args.varFuncInfo            = 0;

  visitClassMemberVariables(&new_args);

  if (fullFjalarName) {
    stringStackPop(&enclosingVarNamesStack);
    VG_(free)((void*)fullFjalarName);
  }
}


// Takes a TypeEntry* and a pointer to it (or an array of pointers if
// isSequence), and traverses through all of the members of the
// specified class (or struct/union).  This should also traverse
// inside of the class's superclasses and visit variables in them as
// well.  Pre: class->decType == {D_STRUCT_CLASS, D_UNION}
void visitClassMemberVariables(VisitArgs* args) {
  TypeEntry* class               = args->class;
  UInt numStructsDereferenced    = args->numStructsDereferenced;
  Bool isSequence                = args->isSequence;
  VariableOrigin varOrigin       = args->varOrigin;
  Addr* pValueArray              = args->pValueArray;
  TraversalResult tResult        = args->tResult;
  UInt numElts                   = args->numElts;
  Addr* pValueArrayGuest         = args->pValueArrayGuest;
  Addr pValue                    = args->pValue;
  Addr pValueGuest               = args->pValueGuest;
  TraversalAction *performAction = args->performAction;
  char* trace_vars_tree          = args->trace_vars_tree;
  FunctionEntry* varFuncInfo     = args->varFuncInfo;
  Bool isEnter                   = args->isEnter;

  VisitArgs new_args;

  const HChar* fullFjalarName = NULL;

  tl_assert(((class->decType == D_STRUCT_CLASS) || (class->decType == D_UNION)) &&
            IS_AGGREGATE_TYPE(class));

  FJALAR_DPRINTF("Enter visitClassMemberVariables\n");

  // Check to see if the VisitedStructsTable contains more than
  // fjalar_max_visit_struct_depth of the current struct type
  if (gencontains(VisitedStructsTable, (void*)class)) {
    UWord count = (UWord)(gengettable(VisitedStructsTable, (void*)class));

    if (count <= fjalar_max_visit_struct_depth) {
      count++;
      genputtable(VisitedStructsTable, (void*)class, (void*)count);
    }
    // PUNT because this struct has appeared more than
    // fjalar_max_visit_struct_depth times during one call to visitVariable()
    else {
      return;
    }
  }
  // If not found in the table, initialize this entry with 1
  else {
    genputtable(VisitedStructsTable, (void*)class, (void*)1);
  }

  // If we have dereferenced more than fjalar_max_visit_nesting_depth
  // structs, then simply PUNT and stop deriving variables from it.
  if (numStructsDereferenced > fjalar_max_visit_nesting_depth) {
    return;
  }


  // Visit member variables:
  if (class->aggType->memberVarList) {
    VarNode* i = NULL;
    for (i = class->aggType->memberVarList->first;
         i != NULL;
         i = i->next) {
      VariableEntry* curVar = i->var;

      const HChar* top = NULL;
      char numEltsPushedOnStack = 0;

      // Address of the value of the current member variable (only
      // valid if !isSequence):
      Addr pCurVarValue = (Addr) NULL;
      Addr pCurVarValueGuest = (Addr) NULL;
      // Only used if isSequence:
      Addr* pCurVarValueArray = NULL;
      Addr* pCurVarValueArrayGuest = NULL;

      if (!curVar->name) {
        printf( "  Warning! Weird null member variable name!\n");
        continue;
      }

      tl_assert(IS_MEMBER_VAR(curVar));

      // Only flatten static arrays when the --flatten-arrays option
      // is used.  Normally we do not have to flatten static arrays at
      // this point because we can simply visit them as an entire
      // sequence.
      if (IS_STATIC_ARRAY_VAR(curVar) &&
          // Always flatten if isSequence because we have no other choice:
          (isSequence ? 1 : fjalar_flatten_arrays) &&
          (DERIVED_FLATTENED_ARRAY_VAR != varOrigin) &&
          (curVar->staticArr->upperBounds[0] < MAXIMUM_ARRAY_SIZE_TO_EXPAND) &&
          // Ignore arrays of characters (strings) inside of the struct:
          !(IS_STRING(curVar) && (curVar->ptrLevels == 1))) {
        // Only look at the first dimension:
        UInt arrayIndex;
        for (arrayIndex = 0; arrayIndex <= curVar->staticArr->upperBounds[0]; arrayIndex++) {
          char indexStr[5];
          top = stringStackTop(&fullNameStack);

          sprintf(indexStr, "%u", arrayIndex);

          // (comment added 2005)  
          // TODO: Subtract and add is a HACK!  Subtract one from the
          // type of curVar just because we are looping through and
          // expanding the array
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            UWord count = (UWord)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count--;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          if (isSequence) {
            if (pValueArray &&
                ((tResult == DEREF_MORE_POINTERS) ||
                 (tResult == DO_NOT_DEREF_MORE_POINTERS))) {
              UInt ind;

              // Create pCurVarValueArray to be the same size as pValueArray:
              pCurVarValueArray = (Addr*)VG_(malloc)("fjalar_traversal.c: vCMV.1", numElts * sizeof(Addr));
              pCurVarValueArrayGuest =
                (Addr*)VG_(malloc)("fjalar_traversal.c: vCMV.2", numElts * sizeof(Addr));

              // Iterate though pValueArray and fill up
              // pCurVarValueArray with pointer values offset by the
              // location of the member variable within the struct
              // plus the offset given by the array index of the
              // flattened array:
              for (ind = 0; ind < numElts; ind++) {
                // The starting address for the member variable is the
                // struct's starting address plus the location of the
                // variable within the struct
                if (pValueArray[ind]) {
                  Addr curVal =
                    pValueArray[ind] + curVar->memberVar->data_member_location;
                  Addr curValGuest = pValueArrayGuest[ind] +
                    curVar->memberVar->data_member_location;

                  // Override for D_DOUBLE types: For some reason, the
                  // DWARF2 info.  botches the locations of double
                  // variables within structs, setting their
                  // data_member_location fields to give them only 4
                  // bytes of padding instead of 8 against the next
                  // member variable.  If curVar is a double and there
                  // exists a next member variable such that the
                  // difference in data_member_location of this double
                  // and the next member variable is exactly 4, then
                  // decrement the double's location by 4 in order to
                  // give it a padding of 8:
                  if ((D_DOUBLE == curVar->varType->decType) &&
                      (i->next) &&
                      ((i->next->var->memberVar->data_member_location -
                        curVar->memberVar->data_member_location) == 4)) {
                    curVal -= 4;
                    curValGuest -= 4;
                  }

                  // Very important!  Add the offset within the
                  // flattened array:
                  curVal += (arrayIndex * getBytesBetweenElts(curVar));
                  curValGuest += (arrayIndex * getBytesBetweenElts(curVar));

                  // Now assign that value into pCurVarValueArray:
                  pCurVarValueArray[ind] = curVal;
                  pCurVarValueArrayGuest[ind] = curValGuest;
                }
                // If the original entry was 0, then simply copy 0, which
                // propagates uninit/unallocated status from structs to
                // members.
                else {
                  pCurVarValueArray[ind] = 0;
                  pCurVarValueArrayGuest[ind] = 0;
                }
              }
            }
          }
          else {
            // Only derive a pointer value inside of the struct if
            // (tResult == DEREF_MORE_POINTERS); else leave
            // pCurVarValue at 0:
            if (tResult == DEREF_MORE_POINTERS) {
              // The starting address for the member variable is the
              // struct's starting address plus the location of the
              // variable within the struct
              pCurVarValue = pValue + curVar->memberVar->data_member_location;
              pCurVarValueGuest  =
                pValueGuest + curVar->memberVar->data_member_location;

              // Very important! Add offset within the flattened array:
              pCurVarValue += (arrayIndex * getBytesBetweenElts(curVar));
              pCurVarValueGuest += (arrayIndex * getBytesBetweenElts(curVar));
            }
          }

          // If the top element is already a dot (from a superclass
          // name perhaps) or there is NO top element (e.g., printing
          // disambig) then don't push anything on:
          if (!top ||
              (top && VG_STREQ(top, DOT))) {
            numEltsPushedOnStack = 0;
          }
          // If the top element is '*', then instead of pushing a
          // '.' to make '*.', erase that element and instead push
          // '->'.  If last element is '->', then we're fine and
          // don't do anything else.  Otherwise, push a '.'
          else if (top && top[0] == '*') {
            stringStackPop(&fullNameStack);
            stringStackPush(&fullNameStack, ARROW);
            numEltsPushedOnStack = 0;
          }
          else if (VG_STREQ(top, ARROW)) {
            numEltsPushedOnStack = 0;
          }
          else {
            stringStackPush(&fullNameStack, DOT);
            numEltsPushedOnStack = 1;
          }

          stringStackPush(&fullNameStack, curVar->name);
          stringStackPush(&fullNameStack, "[");
          stringStackPush(&fullNameStack, indexStr);
          stringStackPush(&fullNameStack, "]");

          numEltsPushedOnStack += 4;

          new_args.var                    = curVar;
          new_args.numDereferences         = 0;
          new_args.performAction          = performAction;
          new_args.varOrigin              = DERIVED_FLATTENED_ARRAY_VAR;
          new_args.trace_vars_tree        = trace_vars_tree;
          new_args.disambigOverride       = OVERRIDE_NONE;
          new_args.numStructsDereferenced = numStructsDereferenced + 1; // Notice the +1 here
          new_args.varFuncInfo            = varFuncInfo;
          new_args.isEnter                = isEnter;

          if (isSequence) {
            new_args.pValueArray      = pCurVarValueArray;
            new_args.pValueArrayGuest = pCurVarValueArrayGuest;
            new_args.numElts          = numElts;

            visitSequence(&new_args);
          }
          else {
            new_args.pValue               = pCurVarValue;
            new_args.pValueGuest          = pCurVarValueGuest;
            new_args.overrideIsInit       = False;
            new_args.alreadyDerefedCppRef = False;

            visitSingleVar(&new_args);
          }

          // POP all the stuff we pushed on there before
          while ((numEltsPushedOnStack--) > 0) {
            stringStackPop(&fullNameStack);
          }

          // (comment added 2005)  
          // HACK: Add the count back on at the end
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            UWord count = (UWord)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count++;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          // Only free if necessary
          if (pCurVarValueArray) {
            VG_(free)(pCurVarValueArray);
            pCurVarValueArray = NULL;
            VG_(free)(pCurVarValueArrayGuest);
            pCurVarValueArrayGuest = NULL;
          }
        }
      }
      // Regular member variable (without array flattening):
      else {
        if (isSequence) {
          if (pValueArray &&
              ((tResult == DEREF_MORE_POINTERS) ||
               (tResult == DO_NOT_DEREF_MORE_POINTERS))) {
            UInt ind;
            // Create pCurVarValueArray to be the same size as
            // pValueArray:
            pCurVarValueArray = (Addr*)VG_(malloc)("fjalar_traversal.c: vCMV.3",numElts * sizeof(Addr));
            pCurVarValueArrayGuest =
              (Addr*)VG_(malloc)("fjalar_traversal.c: vCMV.4", numElts * sizeof(Addr));

            // Iterate though pValueArray and fill up
            // pCurVarValueArray with pointer values offset by the
            // location of the member variable within the struct:
            for (ind = 0; ind < numElts; ind++) {
              // The starting address for the member variable is the
              // struct's starting address plus the location of the
              // variable within the struct
              if (pValueArray[ind]) {
                Addr curVal =
                  pValueArray[ind] + curVar->memberVar->data_member_location;
                Addr curValGuest = pValueArrayGuest[ind] +
                  curVar->memberVar->data_member_location;

                // See "Override for D_DOUBLE types" comment above.
                if ((D_DOUBLE == curVar->varType->decType) &&
                    (i->next) &&
                    ((i->next->var->memberVar->data_member_location -
                      curVar->memberVar->data_member_location) == 4)) {
                  curVal -= 4;
                  curValGuest -= 4;
                }

                // Now assign that value into pCurVarValueArray:
                pCurVarValueArray[ind] = curVal;
                pCurVarValueArrayGuest[ind] = curValGuest;
              }
              // If the original entry was 0, then simply copy 0, which
              // propagates uninit/unallocated status from structs to
              // members.
              else {
                pCurVarValueArray[ind] = 0;
                pCurVarValueArrayGuest[ind] = 0;
              }
            }
          }
        }
        else {
          // Only derive a pointer value inside of the struct if
          // (tResult == DEREF_MORE_POINTERS); else leave pCurVarValue
          // at 0:
          if (pValue && (tResult == DEREF_MORE_POINTERS)) {
            // The starting address for the member variable is the
            // struct's starting address plus the location of the
            // variable within the struct
            pCurVarValue = pValue + curVar->memberVar->data_member_location;
            pCurVarValueGuest =
              pValueGuest + curVar->memberVar->data_member_location;

            // See "Override for D_DOUBLE types" comment above.
            if ((D_DOUBLE == curVar->varType->decType) &&
                (i->next) &&
                ((i->next->var->memberVar->data_member_location -
                  curVar->memberVar->data_member_location) == 4)) {
              pCurVarValue -= 4;
              pCurVarValueGuest -= 4;
            }
          }
        }

        top = stringStackTop(&fullNameStack);

        // If the top element is already a dot (from a superclass name
        // perhaps) or there is NO top element (e.g., printing
        // disambig) then don't push anything on:
        if (!top ||
            (top && VG_STREQ(top, DOT))) {
          numEltsPushedOnStack = 0;
        }
        // If the top element is '*' or '[0]', then instead of pushing
        // a '.' to make '*.' or '[0].', erase that element and
        // instead push '->'.  If last element is '->', then we're
        // fine and don't do anything else.  Otherwise, push a '.'
        else if (top &&
                 ((top[0] == '*') || (VG_STREQ(top, ZEROTH_ELT)))) {
          stringStackPop(&fullNameStack);
          stringStackPush(&fullNameStack, ARROW);
          numEltsPushedOnStack = 0;
        }
        else if (VG_STREQ(top, ARROW)) {
          numEltsPushedOnStack = 0;
        }
        else {
          stringStackPush(&fullNameStack, DOT);
          numEltsPushedOnStack = 1;
        }

        stringStackPush(&fullNameStack, curVar->name);
        numEltsPushedOnStack++;

        new_args.var                    = curVar;
        new_args.numDereferences         = 0;
        new_args.performAction          = performAction;
        new_args.varOrigin              = (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ?
                                          varOrigin : DERIVED_VAR;
        new_args.trace_vars_tree        = trace_vars_tree;
        new_args.disambigOverride       = OVERRIDE_NONE;
        // Notice the +1 here indicating that this next variable is one deeper in
        // this nested structure.
        new_args.numStructsDereferenced = numStructsDereferenced + 1;
        new_args.varFuncInfo            = varFuncInfo;
        new_args.isEnter                = isEnter;

        if (isSequence) {
          new_args.pValueArray      = pCurVarValueArray;
          new_args.pValueArrayGuest = pCurVarValueArrayGuest;
          new_args.numElts          = numElts;

          visitSequence(&new_args);
        }
        else {
          new_args.pValue               = pCurVarValue;
          new_args.pValueGuest          = pCurVarValueGuest;
          new_args.overrideIsInit       = False;
          new_args.alreadyDerefedCppRef = False;

          visitSingleVar(&new_args);
        }

        // POP everything we've just pushed on
        while ((numEltsPushedOnStack--) > 0) {
          stringStackPop(&fullNameStack);
        }

        // Only free if necessary
        if (pCurVarValueArray) {
          VG_(free)(pCurVarValueArray);
          pCurVarValueArray = 0;
          VG_(free)(pCurVarValueArrayGuest);
          pCurVarValueArrayGuest = 0;
        }
      }
    }
  }

  // Now traverse inside of all superclasses and visit all of their
  // member variables (while appending a prefix to them):
  if (class->aggType->superclassList) {
    SimpleNode* n = NULL;
    for (n = class->aggType->superclassList->first;
         n != NULL;
         n = n->next) {
      Addr* superclassOffsetPtrValues = NULL;
      Addr* superclassOffsetPtrValuesGuest = NULL;

      const HChar* top = NULL;
      char numEltsPushedOnStack = 0;

      Superclass* curSuper = (Superclass*)(n->elt);
      tl_assert(curSuper && curSuper->class);

      top = stringStackTop(&fullNameStack);

      // If this superclass's member variables are at a non-zero
      // offset from the beginning of this class and isSequence, then
      // we need to build up a new array where each element is offset
      // by that amount and pass it on.
      if (isSequence &&
          (curSuper->member_var_offset > 0)) {
        UInt ind;
        superclassOffsetPtrValues = (Addr*)VG_(malloc)("fjalar_traversal.c: vCMV.5",numElts * sizeof(Addr));
        superclassOffsetPtrValuesGuest =
          (Addr*)VG_(malloc)("fjalar_traversal.c: vCMV.6", numElts * sizeof(Addr));

        // Iterate though pValueArray and fill up superclassOffsetPtrValues
        // with pointer values offset by curSuper->member_var_offset:
        for (ind = 0; ind < numElts; ind++) {
          if (pValueArray[ind]) {
            superclassOffsetPtrValues[ind] =
              pValueArray[ind] + curSuper->member_var_offset;
            superclassOffsetPtrValuesGuest[ind] =
              pValueArrayGuest[ind] + curSuper->member_var_offset;
          }
        }
      }

      // Push an extra dot before superclass name if necessary
      if (!VG_STREQ(DOT, top) && !VG_STREQ(ARROW,top)) {
        stringStackPush(&fullNameStack, DOT);
        numEltsPushedOnStack += 1;
      }

      // Push a name prefix to denote that we are traversing into a
      // superclass:
      stringStackPush(&fullNameStack, curSuper->className);

      // RUDD - 2.0  Trying to make use of EnclosingVar stack for Nested Classes and Structs.
      // Push fullFjalarName onto enclosingVarNamesStack:
      fullFjalarName = stringStackStrdup(&fullNameStack);
      if (fullFjalarName) {
        stringStackPush(&enclosingVarNamesStack, fullFjalarName);
      }


      stringStackPush(&fullNameStack, DOT);
      numEltsPushedOnStack += 2;

      traversing_super++;

      new_args.class                  = curSuper->class;
      new_args.pValue                 = (isSequence ?
                                         0 : pValue + curSuper->member_var_offset);
      new_args.pValueGuest            = (isSequence ?
                                         0 : pValueGuest+curSuper->member_var_offset);
      new_args.isSequence             = isSequence;
      new_args.pValueArray            = (superclassOffsetPtrValues ?
                                         superclassOffsetPtrValues : pValueArray);
      new_args.pValueArrayGuest       = (superclassOffsetPtrValuesGuest ?
                                         superclassOffsetPtrValuesGuest
                                         : pValueArrayGuest);
      new_args.numElts                = numElts;
      new_args.performAction          = performAction;
      new_args.varOrigin              = varOrigin;
      new_args.trace_vars_tree        = trace_vars_tree;
      new_args.numStructsDereferenced = numStructsDereferenced;
      new_args.varFuncInfo            = varFuncInfo;
      new_args.isEnter                = isEnter;
      new_args.tResult                = tResult;


      // This recursive call will handle multiple levels of
      // inheritance (e.g., if A extends B, B extends C, and C extends
      // D, then A will get all of its members visited, then visit the
      // members of B, then C, then D):
      visitClassMemberVariables(&new_args);

      traversing_super = 0;

      if (fullFjalarName) {
        stringStackPop(&enclosingVarNamesStack);
      }

      // POP all the stuff we pushed on there before
      while ((numEltsPushedOnStack--) > 0) {
        stringStackPop(&fullNameStack);
      }

      if (superclassOffsetPtrValues) {
        VG_(free)(superclassOffsetPtrValues);
        VG_(free)(superclassOffsetPtrValuesGuest);
      }
    }
  }

  if (fullFjalarName) {
    VG_(free)((void*)fullFjalarName);
  }

  // (comment added 2005)  
  // TODO: Visit static member variables (remember that they have
  // global addresses):

  FJALAR_DPRINTF("Exit  visitClassMemberVariables\n");
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
                        Bool isEnter,           // 1 for function entrance, 0 for exit
                        Addr stackBaseAddr,     // should only be used for FUNCTION_FORMAL_PARAM
                        Addr stackBaseAddrGuest,// should only be used for FUNCTION_FORMAL_PARAM
                        // This function performs an action for each
                        // variable visited:
                        TraversalAction *performAction) {
  VarList* varListPtr = NULL;
  VarIterator* varIt = NULL;
  Bool overrideIsInit = 0;

  // If funcPtr is null, then you better be GLOBAL_VAR
  if (!funcPtr) {
    tl_assert(varOrigin == GLOBAL_VAR);
  }

  // You shouldn't be passing in a stackBaseAddr if you're not
  // interested in visiting function formal params:
  if (stackBaseAddr) {
    tl_assert(varOrigin == FUNCTION_FORMAL_PARAM);
  }

  FJALAR_DPRINTF("Enter visitVariableGroup\n");

  switch (varOrigin) {
  case GLOBAL_VAR:
    // Punt if we are ignoring globals!
    if (fjalar_ignore_globals) {
      FJALAR_DPRINTF("\t[visitVariableGroup] Ignoring request for global variables\n");
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

  stringStackClear(&fullNameStack);

  tl_assert(varListPtr);
  //RUDD EXCEPTION
  FJALAR_DPRINTF("VarListPtr %p\n", (void *)varListPtr);

  varIt = newVarIterator(varListPtr);

  while (hasNextVar(varIt)) {
    VariableEntry* var = nextVar(varIt);
    Addr basePtrValue = (Addr) NULL;
    Addr basePtrValueGuest = (Addr) NULL;
    
    if (!var->name) {
      printf( "  Warning! Weird null variable name!\n");
      continue;
    }

    FJALAR_DPRINTF("[visitVariableGroup] Preparing [%s] to be visited\n", var->name);

    if(fjalar_ignore_constants && var->isConstant) {
      FJALAR_DPRINTF("\t[visitVariableGroup] Punting constant\n");
      continue;
    }

    if ((varOrigin == FUNCTION_FORMAL_PARAM) && stackBaseAddr) {
      ThreadId tid = VG_(get_running_tid)();

      // (comment added 2009)  
      // HACKISH. needed to work around bad location information in
      // the DWARF tables, while still providing tools with the variables
      // if they care. return is an exception as we figure it out ourself.
      if(!var->validLoc && !VG_STREQ("return", var->name)) {
        FJALAR_DPRINTF("\t[visitVariableGroup] invalid loc, punting\n");
        continue;
      }

      FJALAR_DPRINTF("\t[visitVariableGroup] baseAddr: %p, baseAddrGuest: %p var->byteOffset: %x(%d)\n", (void *)stackBaseAddr, (void *)stackBaseAddrGuest, (unsigned int)var->byteOffset, var->byteOffset);
      FJALAR_DPRINTF("\t[visitVariableGroup] State of Guest Stack [%p - %p] \n", (void *)funcPtr->guestStackStart, (void *)funcPtr->guestStackEnd);
      FJALAR_DPRINTF("\t[visitVariableGroup] State of Virtual Stack [%p - %p] \n", (void *)funcPtr->lowestVirtSP, (void *)(funcPtr->lowestVirtSP + (funcPtr->guestStackEnd - funcPtr->guestStackStart)));
      FJALAR_DPRINTF("\t[visitVariableGroup] State of Frame Pointer: %p\n", (void *)stackBaseAddrGuest);
      FJALAR_DPRINTF("\t[visitVariableGroup] Size of DWARF location stack: %u\n", var->location_expression_size);

      if(var->location_expression_size) {
        Addr var_loc = (Addr) NULL;
        unsigned int i = 0;

        // MAIN STACK LAYOUT
        // (comment added 2009)  
        // HACK - Main has a very strange stack layout. The stack
        // layout for a standard function is as follows:

        // |                   |
        // |    arguments      |
        // |-------------------|
        // |                   |
        // |  return address   |
        // |-------------------|
        // |                   |
        // |     old ebp       |
        // |-------------------| <------ Top of stack frame.
        // |                   |         ebp points to this if available.
        // |      locals       |
        // |-------------------|

        // The stack layout of main is follows:

        // |                   |
        // |    arguments      |
        // |-------------------|
        // |                   |
        // |  return address   |
        // |-------------------|
        // |                   |
        // |     old ebp       |
        // |-------------------| <------ Top of unaligned stack frame.
        // |                   |
        // |     Padding       |
        // |-------------------|
        // |                   |
        // | unaligned frame   |
        // |-------------------| <------ Top of aligned stack frame. This is
        // |                   |         16-byte aligned. ebp points to this
        // |     locals        |         if available

        // A problem arises due to the fact GCC accesses the arguments using
        // very indirect calculations (usually a pointer in one of the
        // architectural registers. ) Unfortunately, the calculation tended to produce incorrect
        // results for main if attempted at the 'ret' instruction. A hacky way to get around this
        // is to just use the same location as your caculated at entry. This would fail if GCC
        // ever starts using location lists for more than just the frame base.

        if(!isEnter && VG_STREQ("main", funcPtr->name) &&
           (VG_STREQ("argc", var->name) ||
            VG_STREQ("argv", var->name))) {
          FJALAR_DPRINTF("\t[visitVariableGroup] int main(argc/argv) DETECTED, using entry locations isntead of recalculating\n");
          basePtrValue = var->entryLoc;
          basePtrValueGuest = var->entryLocGuest;
        }
        else {

          // Dwarf Locations are implemented as a sequence of operations to be performed.
          for(i = 0; i < var->location_expression_size; i++ ) {
            dwarf_location *dloc  = &(var->location_expression[i]);
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
              FJALAR_DPRINTF("\tObtaining register value: [%%%s]: %x\n", dwarf_reg_string[dloc->atom - DW_OP_reg0],
                             (unsigned int)reg_val);
              var_loc = (Addr)&reg_val;

            } else if((op >= DW_OP_breg0) && (op <= DW_OP_breg31)) {
              // Get value pointed to by architectural register
              reg_val = (*get_reg[dloc->atom - DW_OP_breg0])(tid);
              FJALAR_DPRINTF("\tObtaining register value: [%%%s]: %x\n", dwarf_reg_string[dloc->atom - DW_OP_breg0],
                             (unsigned int) reg_val);
              var_loc = reg_val + dloc->atom_offset;
              FJALAR_DPRINTF("\tAdding %lld to the register value for %p\n", dloc->atom_offset, (void *)var_loc);
              tl_assert(var_loc);

            } else if(op == DW_OP_fbreg) {
              // Get value located at an offset from the FRAME_BASE.
              FJALAR_DPRINTF("atom offset: %lld vs. byteOffset: %d\n", dloc->atom_offset, var->byteOffset);
              var_loc = stackBaseAddrGuest + dloc->atom_offset;

            } else {
              // There's a fair number of DWARF operations still unsupported. There is a full list
              // in fjalar_debug.h
              FJALAR_DPRINTF("\tUnsupported DWARF stack OP: %s\n", location_expression_to_string(op));
              tl_assert(0);
            }
            FJALAR_DPRINTF("\tApplying DWARF Stack Operation %s - %p\n",location_expression_to_string(op), (void *)var_loc);
          }

          if((var_loc >= funcPtr->guestStackStart) &&
              (var_loc <= funcPtr->guestStackEnd)) {

#if defined(VGA_amd64)
          if(!isEnter) {
            //            overrideIsInit = 1;
          }
#endif


          //int virt_offset = var_loc - funcPtr->lowestSP;
          int virt_offset = var_loc - funcPtr->guestStackStart;

            FJALAR_DPRINTF("\t[visitVariableGroup] stackBaseAddr: %p\n\tREDZONE: %d,\n\tFP: %p\n\tvar_loc %p\n\tOffset(virt): %d\n",
                           (void *)funcPtr->guestStackStart, VG_STACK_REDZONE_SZB, (void *)funcPtr->FP, (void *)var_loc, virt_offset);

            var->byteOffset = var_loc - funcPtr->FP;
            // + VG_STACK_REDZONE_SZB;
            basePtrValue = funcPtr->lowestVirtSP + virt_offset;
            var->entryLoc = basePtrValue;
            var->entryLocGuest = var_loc;
            basePtrValueGuest = var_loc; }
          else {
            basePtrValue = var_loc;
            var->entryLoc = var_loc;
          }
        }
      }

      else {
        // Standard offset of the framebase.
        basePtrValue = stackBaseAddr + var->byteOffset;
        basePtrValueGuest = stackBaseAddrGuest + var->byteOffset;
      }
    }
    else if (varOrigin == GLOBAL_VAR) {
      tl_assert(IS_GLOBAL_VAR(var));
      basePtrValue = basePtrValueGuest = var->globalVar->globalLocation;

      if(!basePtrValue && var->isConstant) {
        FJALAR_DPRINTF("[visitVariableGroup] Invalid globalLocation, but has a constant value (%ld). Overriding address.\n", 
                       var->constValue);
        basePtrValue = (Addr)&var->constValue;
        overrideIsInit = True;
      }

      // if "--ignore-static-vars" option was selected, do not visit
      // file-static global variables:
      if (!var->globalVar->isExternal && fjalar_ignore_static_vars) {
        continue;
      }

      // If "--all-static-vars" option was NOT selected (default), then:
      // * Only visit file-static variables at program points
      //   in the file in which the variables were declared
      // * Only visit static variables declared within functions
      //   at program points of that particular function
      if (!var->globalVar->isExternal && (!fjalar_all_static_vars) && funcPtr) {
        // Declared within a function
        if (var->globalVar->functionStartPC) {
          if (funcPtr->startPC != var->globalVar->functionStartPC) {
            continue;
          }
        }
        // Declared globally
        else if (!VG_STREQ(funcPtr->filename, var->globalVar->fileName)) {
          continue;
        }
      }
    }

    stringStackPush(&fullNameStack, var->name);

    visitVariable(var,
                  basePtrValue,
                  basePtrValueGuest,
                  overrideIsInit,
                  0,
                  performAction,
                  varOrigin,
                  funcPtr,
                  isEnter);

    stringStackPop(&fullNameStack);
  }

  deleteVarIterator(varIt);

  FJALAR_DPRINTF("Exit  visitVariableGroup\n");
}


// Grabs the appropriate return value of the function denoted by the
// execution state 'e' from Valgrind simulated registers and visits
// the variables to perform some action.  This differs from calling
// visitVariableGroup() with the FUNCTION_RETURN_VAR parameter because
// it actually grabs the appropriate value from the simulated
// registers.
void visitReturnValue(FunctionExecutionState* e,
                      // This function performs an action for each variable visited:
                      TraversalAction *performAction) {
  VarNode* cur_node;
  FunctionEntry* funcPtr;
  tl_assert(e);

  funcPtr = e->func;
  tl_assert(funcPtr);
  cur_node = funcPtr->returnValue.first;

  // This happens when there is a void function with no return value:
  if (!cur_node) {
    FJALAR_DPRINTF("Enter/Exit visitReturnValue - void return\n");
    return;
  }

  FJALAR_DPRINTF("Enter visitReturnValue - var: %s\n", cur_node->var->name);

  // We need to push the return value name onto the string stack!
  stringStackClear(&fullNameStack);

  tl_assert(cur_node->var);
  tl_assert(cur_node->var->name);
  tl_assert(cur_node->var->varType);

  stringStackPush(&fullNameStack, cur_node->var->name);

  // Struct/union type - use xAX but remember that xAX holds
  // a POINTER to the struct/union so we must dereference appropriately
  // WE NEED TO CHECK THAT declaredPtrLevels == 0 since we need a
  // real struct/union, not just a pointer to one
  // BE CAREFUL WITH declaredType - it may be misleading since all
  // pointers share the same declaredType
  // RUDD - Need an extra indirection level for references.
  if ((cur_node->var->ptrLevels == 0) &&
      (IS_AGGREGATE_TYPE(cur_node->var->varType)) && !cur_node->var->referenceLevels) {


    // AMD64 special case: If the size of the the struct is <= the size
    // of 2 architectural registers, it is passed via RAX and RDX.
    // We're going to express this by creating a 16 byte buffer and
    // copying the contents of RAX and EDX to it and passing a pointer
    // to it.
#if defined(VGA_amd64)
    if(cur_node->var->varType->byteSize <= 16) {
      char returnBuffer[16];

      VG_(memcpy)(returnBuffer                       ,  &e->xAX, 8);
      VG_(memcpy)(returnBuffer + (Addr)sizeof(e->xAX),  &e->xDX, 8);

      unsigned long long int uLong = (e->xAX);
      FJALAR_DPRINTF("tiny struct\n");

      // Copy A and V bits over:
      mc_copy_address_range_state((Addr)(&(e->xAX)),
                                  (Addr)(&returnBuffer),
                                  sizeof(e->xAX));

      mc_copy_address_range_state((Addr)(&(e->xDX)),
                                  (Addr)(&returnBuffer) + (Addr)sizeof(e->xAX),
                                  sizeof(e->xDX));

      // Remember to copy A and V-bits over:
      mc_copy_address_range_state((Addr)(&(e->xAX)),
                                  (Addr)(&uLong),
                                  sizeof(e->xAX));

      visitVariable(cur_node->var,
                    (Addr) returnBuffer,
                    0,
                    1, // e->xAXvalid,
                    0,
                    performAction,
                    FUNCTION_RETURN_VAR,
                    funcPtr,
                    0);
    } else
#endif

    // e->xAX is the contents of the virtual xAX, which should be the
    // address of the struct/union, so pass that along ...  NO extra
    // level of indirection needed
    visitVariable(cur_node->var,
                  (Addr)e->xAX,
                  0, /* register, no guest location*/
                  // No longer need to overrideIsInitialized
                  // because we now keep shadow V-bits for e->xAX
                  // and friends
                  0, // e->xAXvalid,
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
            (cur_node->var->varType->decType == D_LONG_DOUBLE))) {
    // SPECIAL CASE: The value in FPU must be interpreted as a double
    // even if its true type may be a float
    FJALAR_DPRINTF("RETURN - floating point: cur_node=%p, basePtr=%p, value=%.16g\n",
                   cur_node, &(e->FPU), (double)e->FPU);
    visitVariable(cur_node->var,
                  (Addr)&(e->FPU),
                  0, /* register, no guest location */
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  // Remember that x86 long long int types use xAX as the low 4 bytes
  // and xDX as the high 4 bytes
  // long long ints - create a long long int and pass its address
  /* XXX shouldn't do this for 64-bit long long on AMD64 */
  else if ((sizeof(UWord) == 4) && (cur_node->var->ptrLevels == 0) &&
           (cur_node->var->varType->decType == D_UNSIGNED_LONG_LONG_INT)) {
    unsigned long long int uLong = (e->xAX) | (((unsigned long long int)(e->xDX)) << 32);
    FJALAR_DPRINTF("long long int type\n");

    // Remember to copy A and V-bits over:
    mc_copy_address_range_state((Addr)(&(e->xAX)),
                                (Addr)(&uLong),
                                sizeof(e->xAX));

    mc_copy_address_range_state((Addr)(&(e->xDX)),
                                (Addr)(&uLong) + (Addr)sizeof(e->xAX),
                                sizeof(e->xDX));

    visitVariable(cur_node->var,
                  (Addr)&uLong,
                  0, /* registers, no guest location */
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  else if ((sizeof(UWord) == 4) && (cur_node->var->ptrLevels == 0) &&
           (cur_node->var->varType->decType == D_LONG_LONG_INT)) {
    long long int signedLong = (e->xAX) | (((long long int)(e->xDX)) << 32);

    // Remember to copy A and V-bits over:
    mc_copy_address_range_state((Addr)(&(e->xAX)),
                                (Addr)(&signedLong),
                                sizeof(e->xAX));

    mc_copy_address_range_state((Addr)(&(e->xDX)),
                                (Addr)(&signedLong) + (Addr)sizeof(e->xAX),
                                sizeof(e->xDX));

    visitVariable(cur_node->var,
                  (Addr)&signedLong,
                  0, /* registers, no guest location */
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }
  // All other types (integer and pointer) - use xAX
  else {
    FJALAR_DPRINTF("int or pointer type\n");
    // Need an additional indirection level
    FJALAR_DPRINTF(" RETURN - int/ptr.: cur_node=%p, basePtr=%p, value in xAX: %d\n",
                   cur_node, &(e->xAX), (int)e->xAX);

    visitVariable(cur_node->var,
                  (Addr)&(e->xAX),
                  0, /* register, no guest location */
                  0,
                  0,
                  performAction,
                  FUNCTION_RETURN_VAR,
                  funcPtr,
                  0);
  }

  stringStackPop(&fullNameStack);

  FJALAR_DPRINTF("Exit  visitReturnValue - var: %s\n", cur_node->var->name);
}


/* Functions for visiting variables at every program point */

// Returns 1 if we are interested in visiting this variable and its
// children, 0 otherwise.  No children of this variable will get
// visited if this variable is not visited.  For example, if 'foo' is
// an array, then if the hashcode value of 'foo' is not visited, then
// the actual array value of 'foo[]' won't be visited either.
// This performs string matching in trace_vars_tree based on fullFjalarName
static char interestedInVar(const HChar* fullFjalarName, char* trace_vars_tree) {
  if (fjalar_trace_vars_filename) {
    if (trace_vars_tree) {
      //      printf("Checking if %s is in var list\n", fullFjalarName);
      if (!tfind((void*)fullFjalarName, (void**)&trace_vars_tree, compareStrings)) {        
        return 0;
      }
      //      printf("Found it\n", fullFjalarName);
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


// This visits a variable by delegating to visitSingleVar()
// Pre: varOrigin != DERIVED_VAR, varOrigin != DERIVED_FLATTENED_ARRAY_VAR
// Pre: The name of the variable is already initialized in fullNameStack
void visitVariable(VariableEntry* var,
                   // Pointer to the location of the variable's
                   // current value in memory:
                   Addr pValue,
                   Addr pValueGuest,
                   // We only use overrideIsInit when we pass in
                   // things (e.g. return values) that cannot be
                   // checked by the Memcheck A and V bits. Never have
                   // overrideIsInit when you derive variables (make
                   // recursive calls) because their addresses are
                   // different from the original's
                   Bool overrideIsInit,
                   // This should almost always be 0, but whenever you
                   // want finer control over struct dereferences, you
                   // can override this with a number representing the
                   // number of structs you have dereferenced so far
                   // to get here (this is useful for the 'this'
                   // parameter of member functions):
                   UInt numStructsDereferenced,
                   // This function performs an action for each
                   // variable visited:
                   TraversalAction *performAction,
                   VariableOrigin varOrigin,
                   FunctionEntry* varFuncInfo,
                   Bool isEnter) {

  // (comment added 2009)  
  // TODO: This function should be changed to take in a VisitArgs*
  // instead of this list of arguments. This would require a change
  // in the Fjalar API however.
  VisitArgs new_args;
  char* trace_vars_tree = NULL;
  
  tl_assert(varOrigin != DERIVED_VAR);
  tl_assert(varOrigin != DERIVED_FLATTENED_ARRAY_VAR);

  FJALAR_DPRINTF("Enter visitVariable - var: %s\n", var->name);

  // In preparation for a new round of variable visits, initialize a
  // new VisitedStructsTable, freeing an old one if necessary

  // Profiling has shown that allocation of this hashtable takes a lot
  // of the total execution time because it is called very often, so
  // we should only do it if this variable is a struct/union type
  // (otherwise, it's not necessary because there are no derived
  // variables):
  if (IS_AGGREGATE_TYPE(var->varType)) {

    if (VisitedStructsTable) {
      genfreehashtable(VisitedStructsTable);
      VisitedStructsTable = NULL;
    }

    // Use a small hashtable to save time and space:
    VisitedStructsTable =
      genallocateSMALLhashtable(0, (int (*)(void *,void *)) &equivalentIDs);
  }

  // Also initialize trace_vars_tree based on varOrigin and
  // varFuncInfo:
  if (varOrigin == GLOBAL_VAR) {
    
    if (varFuncInfo == 0 || varFuncInfo->trace_global_vars_tree == 0){
      trace_vars_tree = (globalFunctionTree ?
                         globalFunctionTree->function_variables_tree : 0);
    }else{
      //Use the user-specified globals list if possible
      //trace_global_vars_tree holds all the global variables specified in the globals
      //section as well as those specified in the functions section of vars-file

      trace_vars_tree = varFuncInfo->trace_global_vars_tree;
    }
  }
  else {
    trace_vars_tree = varFuncInfo->trace_vars_tree;
  }

  // Delegate:
  new_args.var                    = var;
  new_args.numDereferences        = 0;
  new_args.pValue                 = pValue;
  new_args.pValueGuest            = pValueGuest;
  new_args.overrideIsInit         = overrideIsInit;
  new_args.alreadyDerefedCppRef   = False;
  new_args.performAction          = performAction;
  new_args.varOrigin              = varOrigin;
  new_args.trace_vars_tree        = trace_vars_tree;
  new_args.disambigOverride       = OVERRIDE_NONE;
  new_args.numStructsDereferenced = numStructsDereferenced;
  new_args.varFuncInfo            = varFuncInfo;
  new_args.isEnter                = isEnter;

  visitSingleVar(&new_args);

  FJALAR_DPRINTF("Exit  visitVariable - var: %s\n", var->name);
}


// Visit a single variable uniquely identified by var and
// numDereferences and then derive additional variables either by
// dereferencing pointers or by visiting struct members
// This function calls visitSingleVar() or visitSequence()
static
void visitSingleVar(VisitArgs* args) {
  VariableEntry*  var               = args->var;
  UInt numDereferences              = args->numDereferences;
  DisambigOverride disambigOverride = args->disambigOverride;
  UInt numStructsDereferenced       = args->numStructsDereferenced;
  VariableOrigin varOrigin          = args->varOrigin;
  Addr pValue                       = args->pValue;
  Addr pValueGuest                  = args->pValueGuest;
  Bool overrideIsInit               = args->overrideIsInit;
  Bool alreadyDerefedCppRef         = args->alreadyDerefedCppRef;
  TraversalAction *performAction    = args->performAction;
  char* trace_vars_tree             = args->trace_vars_tree;
  FunctionEntry* varFuncInfo        = args->varFuncInfo;
  Bool isEnter                      = args->isEnter;

  VisitArgs new_args;

  const HChar* fullFjalarName = NULL;
  int layersBeforeBase;

  // Initialize these in a group later
  Bool disambigOverrideArrayAsPointer;
  Bool derefSingleElement;
  Bool needToDerefCppRef;

  TraversalResult tResult = INVALID_RESULT;
  tl_assert(var);
  
  FJALAR_DPRINTF("Enter visitSingleVar - var: %s\n", var->name);

  needToDerefCppRef = ((var->referenceLevels > 0) && (numDereferences == 0));

  // Reset this counter to get C++ reference parameter variables to work properly:
  if (alreadyDerefedCppRef) {
    numDereferences = 0;
  }

  layersBeforeBase = var->ptrLevels - numDereferences;

  // Special hack for strings:
  if (IS_STRING(var) && (layersBeforeBase > 0)) {
    layersBeforeBase--;
    //    printf("var: %s is string - layersBeforeBase: %d\n",
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

  // Remember to dereference a single element if we are dereferencing
  // the contents of a C++ reference parameter:
  derefSingleElement = (disambigOverrideArrayAsPointer || needToDerefCppRef);


  // Unless fjalar_output_struct_vars is on, don't perform any action
  // for base (non-pointer) struct/union variables since they have no
  // substantive meaning for C programs.  We are only interested in
  // the fields of the struct, not the struct itself.

  // For C++, do NOT output anything for reference parameter variables
  // - e.g., "foo(int& a)" - because they are immutable and
  // un-interesting pointer values.  Instead, we want to dereference
  // one level of pointers and print the resulting value:

  // This means that anywhere inside of this 'if' statement, we should
  // be very careful about mutating state because different state may
  // be mutated based on whether fjalar_output_struct_vars is on,
  // which may lead to different-looking results.
  if (!needToDerefCppRef &&
      (fjalar_output_struct_vars ||
       (!((layersBeforeBase == 0) && IS_AGGREGATE_TYPE(var->varType))))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStack.size > 0);
    fullFjalarName = stringStackStrdup(&fullNameStack);

    // For disambig: While observing the runtime values, set
    // pointerHasEverBeenObserved to 1 if the contents of a pointer
    // variable is initialized (very conservative - only check whether
    // the 1st byte has been initialized)
    if (fjalar_smart_disambig &&
        (1 == numDereferences) && // is pointer variable
        (!var->pointerHasEverBeenObserved) && // haven't been observed yet
        // check whether 1st byte is initialized
        pValue &&
        (overrideIsInit ? 1 :
         addressIsInitialized(pValue, sizeof(char)))) {
      var->pointerHasEverBeenObserved = 1;
    }

    FJALAR_DPRINTF("Callback for single variable %s\n",
                   fullFjalarName);
    FJALAR_DPRINTF("overideisInit? %d\n", overrideIsInit);
    FJALAR_DPRINTF("pValue: %p\n", (void *)pValue);

    // rudd: PARTIAL_STRUCT_TRAVERSAL
    // We used to return upon seeing an "uninteresting" 
    // variable (one that is not in the variable); this is
    // problematic as members or members of members may be
    // interesting. Now we will not return, but simply not
    // pass uninteresting variables to the tool.
    
    if (interestedInVar(fullFjalarName, trace_vars_tree)) {

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
                                 pValueGuest,
                                 0,
                                 0,
                                 0,
                                 varFuncInfo,
                                 isEnter);

      tl_assert(tResult != INVALID_RESULT);

      // Punt!
      if (tResult == STOP_TRAVERSAL) {
        VG_(free)((void*)fullFjalarName);
        return;
      }
    }
  }


  // This is an ugly hack that's required to properly not visit base
  // struct variables but still make sure that derived variables are
  // properly visited.  When we encounter a base struct variable, we
  // need to set DEREF_MORE_POINTERS because we need its member
  // variables to be properly visited:
  // Same thing with a C++ reference variable
  if (needToDerefCppRef ||
      ((layersBeforeBase == 0) && IS_AGGREGATE_TYPE(var->varType))) {
    tResult = DEREF_MORE_POINTERS;
  }

  // Be very careful about where you increment this!  We want to
  // increment this once per call of either visitSingleVar() or
  // visitSequence():
  g_variableIndex++;

  // Now comes the fun part of deriving variables!

  // Dereference and keep on printing out derived variables until we
  // hit the base type:
  // (Remember to dereference C++ reference parameter variables exactly ONCE)
  if ((layersBeforeBase > 0) || needToDerefCppRef) {

    // 1.) Initialize pValue properly and call visitSingleVar() again
    // because we are dereferencing a single element:
    if (derefSingleElement) {
      char derivedIsAllocated = 0;

      Addr pNewValue = 0;
      // The default is DERIVED_VAR.  Tweak later if necessary.
      VariableOrigin newVarOrigin = DERIVED_VAR;

      // Initialize pNewValue if possible, otherwise leave at 0:
      // VERY IMPORTANT: Only derive by dereferencing pointers if
      // tResult == DEREF_MORE_POINTERS:
      if (pValue && (tResult == DEREF_MORE_POINTERS)) {
        derivedIsAllocated = (overrideIsInit ? 1 :
                              addressIsAllocated((Addr)pValue, sizeof(void*)));
        if (derivedIsAllocated) {
          // Make a single dereference unless the variable is a static
          // array, in which case we shouldn't make a dereference at
          // all:
          pNewValue = IS_STATIC_ARRAY_VAR(var) ? pValue : *((Addr*)pValue);
        }
      }

      // This is so --func-disambig-ptrs can work properly:
      if (needToDerefCppRef &&
          ((varOrigin == FUNCTION_FORMAL_PARAM) ||
           (varOrigin == FUNCTION_RETURN_VAR))) {
        newVarOrigin = varOrigin;
      }
      else if (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) {
        newVarOrigin = DERIVED_FLATTENED_ARRAY_VAR;
      }

      // Push 1 symbol on stack to represent single elt. dereference:
      if (!needToDerefCppRef) {
        stringStackPush(&fullNameStack, ZEROTH_ELT);
      }

      // Push fullFjalarName onto enclosingVarNamesStack:
      if (fullFjalarName) {
        stringStackPush(&enclosingVarNamesStack, fullFjalarName);
      }

      new_args.var                    = var;
      new_args.numDereferences        = numDereferences + 1;
      new_args.pValue                 = pNewValue;
      new_args.pValueGuest            = pNewValue;
      new_args.overrideIsInit         = overrideIsInit;
      new_args.alreadyDerefedCppRef   = needToDerefCppRef;
      new_args.performAction          = performAction;
      new_args.varOrigin              = newVarOrigin;
      new_args.trace_vars_tree        = trace_vars_tree;
      new_args.disambigOverride       = disambigOverride;
      new_args.numStructsDereferenced = numStructsDereferenced;
      new_args.varFuncInfo            = varFuncInfo;
      new_args.isEnter                = isEnter;

      visitSingleVar(&new_args);

      // Pop fullFjalarName from stack
      if (fullFjalarName) {
        stringStackPop(&enclosingVarNamesStack);
      }

      // Pop 1 symbol off
      if (!((var->referenceLevels > 0) && (numDereferences == 0))) {
        stringStackPop(&fullNameStack);
      }
    }
    // 2.) Sequence dereference (can either be static or dynamic
    // array).  We need to initialize pValueArray and numElts
    // appropriately and call visitSequence()
    else {
      Addr* pValueArray = NULL;
      Addr* pValueArrayGuest = NULL;
      UInt numElts = 0;
      UInt bytesBetweenElts = getBytesBetweenElts(var);
      UInt i;

      // We only need to set pValueArray and numElts for .dtrace output:
      // VERY IMPORTANT: Only derive by dereferencing pointers if
      // tResult == DEREF_MORE_POINTERS:
      if (pValue && (tResult == DEREF_MORE_POINTERS)) {
        // Static array:
        if (IS_STATIC_ARRAY_VAR(var)) {
          // Flatten multi-dimensional arrays by treating them as one
          // giant single-dimensional array.  Take the products of the
          // sizes of all dimensions (remember to add 1 to each to get
          // from upper bound to size):
          UInt dim;

          // Notice the +1 to convert from upper bound to numElts
          numElts = 1 + var->staticArr->upperBounds[0];

          // Additional dimensions:
          FJALAR_DPRINTF("Static Array\n");
          for (dim = 1; dim < var->staticArr->numDimensions; dim++) {
            numElts *= (1 + var->staticArr->upperBounds[dim]);
          }

          pValueArray = (Addr*)VG_(malloc)("fjalar_traversal.c: vSV.1" , numElts * sizeof(Addr));
          pValueArrayGuest = (Addr*)VG_(malloc)("fjalar_traversal.c: vSV.2", numElts * sizeof(Addr));

          FJALAR_DPRINTF("Static array - dims: %u, numElts: %u\n", var->staticArr->numDimensions, numElts);

          // Build up pValueArray with pointers to the elements of the
          // static array starting at pValue
          for (i = 0; i < numElts; i++) {
            pValueArray[i] = pValue + (i * bytesBetweenElts);
            pValueArrayGuest[i] = pValueGuest + (i * bytesBetweenElts);
          }
        }
        // Dynamic array:
        else {
          char derivedIsAllocated = 0;
          Addr pNewStartValue = (Addr) NULL;

          FJALAR_DPRINTF("Dynamic Array\n");

          if (overrideIsInit)
            derivedIsAllocated = 1;
          else if (!pValueGuest)
            /* This has no address, because it was somewhere like a
               register. No need to check A bits. */
            derivedIsAllocated = 1;
          else
            derivedIsAllocated = addressIsAllocated(pValue, sizeof(void*));

          if (derivedIsAllocated) {
            // Make a single dereference to get to the start of the array
            pNewStartValue = *((Addr*)pValue);
          }

          // We should only initialize pValueArray and numElts if the
          // pointer to the start of the array is valid:
          if (pNewStartValue) {
            // Notice the +1 to convert from upper bound to numElts

            numElts = 1 + returnArrayUpperBoundFromPtr(var, (Addr)pNewStartValue);
            pValueArray = (Addr*)VG_(malloc)("fjalar_traversal.c: vSV.3", numElts * sizeof(Addr));
            pValueArrayGuest = (Addr*)VG_(malloc)("fjalar_traversal.c: vSV.4" ,numElts * sizeof(Addr));

                FJALAR_DPRINTF("numElts is %u\n", numElts);

            // Build up pValueArray with pointers starting at pNewStartValue
            for (i = 0; i < numElts; i++) {
              pValueArray[i] = pNewStartValue + (i * bytesBetweenElts);
              pValueArrayGuest[i] = pNewStartValue + (i * bytesBetweenElts);
            }
          }
        }
      }

      // Push 1 symbol on stack to represent sequence dereference:
      stringStackPush(&fullNameStack, DEREFERENCE);

      // Push fullFjalarName onto enclosingVarNamesStack:
      if (fullFjalarName) {
        stringStackPush(&enclosingVarNamesStack, fullFjalarName);
      }

      FJALAR_DPRINTF("Callback for Sequence variable %s\n",
                     fullFjalarName);

      new_args.var                    = var;
      new_args.numDereferences        = numDereferences + 1;
      new_args.pValueArray            = pValueArray;
      new_args.pValueArrayGuest       = pValueArrayGuest;
      new_args.numElts                = numElts;
      new_args.performAction          = performAction;
      new_args.varOrigin              = (varOrigin == DERIVED_FLATTENED_ARRAY_VAR)
                                        ? varOrigin : DERIVED_VAR;
      new_args.trace_vars_tree        = trace_vars_tree;
      new_args.disambigOverride       = disambigOverride;
      new_args.numStructsDereferenced = numStructsDereferenced;
      new_args.varFuncInfo            = varFuncInfo;
      new_args.isEnter                = isEnter;

      visitSequence(&new_args);

      // Pop fullFjalarName from stack
      if (fullFjalarName) {
        stringStackPop(&enclosingVarNamesStack);
      }

      // Pop 1 symbol off
      stringStackPop(&fullNameStack);

      // Only free if necessary
      if (pValueArray) {
        VG_(free)(pValueArray);
        pValueArray = NULL;
        VG_(free)(pValueArrayGuest);
        pValueArrayGuest = NULL;
      }
    }
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), thenSvisit
  // all derived member variables:
  else if (IS_AGGREGATE_TYPE(var->varType)) {
    const HChar* top = NULL;

    tl_assert(0 == layersBeforeBase);


    // RUDD 2.0 Trying to make use of EnclosingVar stack for Nested Classes and Structs.
    // Push fullFjalarName onto enclosingVarNamesStack:
    top = stringStackTop(&fullNameStack);

    //Need a proper enclosing variable name
    if (!top ||
        (top && VG_STREQ(top, DOT)) ||
        (top && VG_STREQ(top, ZEROTH_ELT)) ||
        (top && VG_STREQ(top, ARROW))) {
      stringStackPop(&fullNameStack);
      fullFjalarName = stringStackStrdup(&fullNameStack);

      if (fullFjalarName) {
        stringStackPush(&enclosingVarNamesStack, fullFjalarName);
      }
      stringStackPush(&fullNameStack, top);
    }
    else {
      fullFjalarName = stringStackStrdup(&fullNameStack);
      if (fullFjalarName) {
        stringStackPush(&enclosingVarNamesStack, fullFjalarName);
      }
    }

    new_args.class = var->varType;
    new_args.pValue = pValue;
    new_args.pValueGuest = pValueGuest;
    new_args.isSequence = False;
    new_args.pValueArray = NULL;
    new_args.pValueArrayGuest = NULL;
    new_args.numElts = 0;
    new_args.performAction = performAction;
    new_args.varOrigin = varOrigin;
    new_args.trace_vars_tree = trace_vars_tree;
    new_args.numStructsDereferenced = numStructsDereferenced;
    new_args.varFuncInfo = varFuncInfo;
    new_args.isEnter = isEnter;
    new_args.tResult = tResult;

    visitClassMemberVariables(&new_args);

  if (fullFjalarName) {
    stringStackPop(&enclosingVarNamesStack);
  }


  }
  if (fullFjalarName)
    VG_(free)((void*)fullFjalarName);
  
  FJALAR_DPRINTF("Exit  visitSingleVar - var: %s\n", var->name);
}


// Visit a variable sequence uniquely identified by var and
// numDereferences whose values are referred to by pointers within
// pValueArray (of size numElts), and then derive additional variables
// either by dereferencing pointers or by visiting struct members.
// This function only calls visitSequence() with the same value of
// numElts because Fjalar currently only supports one level of sequences.
// Pre: varOrigin == {DERIVED_VAR, DERIVED_FLATTENED_ARRAY_VAR}
static
void visitSequence(VisitArgs* args) {
  VariableEntry*  var               = args->var;
  UInt numDereferences              = args->numDereferences;
  DisambigOverride disambigOverride = args->disambigOverride;
  UInt numStructsDereferenced       = args->numStructsDereferenced;
  VariableOrigin varOrigin          = args->varOrigin;
  Addr* pValueArray                 = args->pValueArray;
  UInt numElts                      = args->numElts;
  Addr* pValueArrayGuest            = args->pValueArrayGuest;
  TraversalAction *performAction    = args->performAction;
  char* trace_vars_tree             = args->trace_vars_tree;
  FunctionEntry* varFuncInfo        = args->varFuncInfo;
  Bool isEnter                      = args->isEnter;

  VisitArgs new_args;

  const HChar* fullFjalarName = NULL;
  int layersBeforeBase;

  TraversalResult tResult = INVALID_RESULT;

  tl_assert(var);

  FJALAR_DPRINTF("Enter visitSequence - var: %s\n", var->name);

  layersBeforeBase = var->ptrLevels - numDereferences;

  // Special hack for strings:
  if (IS_STRING(var) && (layersBeforeBase > 0)) {
    layersBeforeBase--;
    //    printf("var: %s is string - layersBeforeBase: %d\n",
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
      (!((layersBeforeBase == 0) && IS_AGGREGATE_TYPE(var->varType)))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStack.size > 0);
    fullFjalarName = stringStackStrdup(&fullNameStack);

    // For disambig: While observing the runtime values, set
    // var->disambigMultipleElts and var->pointerHasEverBeenObserved
    // depending on whether upperBound == 0 (1 element) or not and
    // whether variableHasBeenObserved: We do this only when
    // numDereferences == 1 because we want to see if the target of a
    // particular pointer has been observed and whether it refers to 1
    // or multiple elements.
    if (fjalar_smart_disambig &&
        (1 == numDereferences) && // is pointer variable
        pValueArray && numElts) {
      Bool someEltNonZero = False;
      UInt i;

      // If all elements of pValueArray are 0, then this also means
      // nonsensical because there is no content to dereference:
      for (i = 0; i < numElts; i++) {
        if (pValueArray[i]) {
          someEltNonZero = True;
          break;
        }
      }
      if (someEltNonZero) {
        Bool someEltInit = False;
        // Make sure there is at least 1 initialized elt in pValueArray
        for (i = 0; i < numElts; i++) {
          Addr pCurValue = pValueArray[i];
          char eltInit = addressIsInitialized(pCurValue, sizeof(char));
          if (eltInit) {
            someEltInit = True;
            break;
          }
        }

        if (someEltInit) {
          // Only do this if some element is initialized:
          if (numElts > 1) {
            var->disambigMultipleElts = True;
          }

          // If pointerHasEverBeenObserved is not set, then set it
          if (!var->pointerHasEverBeenObserved) {
            var->pointerHasEverBeenObserved = True;
          }
        }
      }
    }

    FJALAR_DPRINTF("Callback for sequence variable %s\n",
                   fullFjalarName);

    // See: PARTIAL_STRUCT_TRAVERSAL
    if (interestedInVar(fullFjalarName, trace_vars_tree)) {

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
                                 0,
                                 pValueArray,
                                 pValueArrayGuest,
                                 numElts,
                                 varFuncInfo,
                                 isEnter);

      tl_assert(tResult != INVALID_RESULT);

      // Punt!
      if (tResult == STOP_TRAVERSAL) {
        VG_(free)((void*)fullFjalarName);
        return;
      }
    }
  }

  // This is an ugly hack that's required to properly not visit base
  // struct variables but still make sure that derived variables are
  // properly visited.  When we encounter a base struct variable, we
  // need to set DEREF_MORE_POINTERS because we need its member
  // variables to be properly visited:
  if ((layersBeforeBase == 0) && IS_AGGREGATE_TYPE(var->varType)) {
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
    // (comment added 2005)  
    // TODO: Implement static array flattening

    // (If this variable is a static array, then there is no need to
    //  dereference pointers - very important but subtle point!)
    if (pValueArray && !IS_STATIC_ARRAY_VAR(var)) {
      // Iterate through pValueArray and dereference each pointer
      // value if possible, then override the entries in pValueArray
      // with the dereferenced pointers (use a value of 0 for
      // unallocated or uninit)
      UInt i;
      for (i = 0; i < numElts; i++) {
        char derivedIsAllocated = 0;
        char derivedIsInitialized = 0;
        Addr* pValueArrayEntry = &pValueArray[i];
        Addr* pValueArrayEntryGuest = &pValueArrayGuest[i];

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
            *pValueArrayEntryGuest = *pValueArrayEntry =
              *((Addr*)(*pValueArrayEntry));
          }
          else {
            // (comment added 2005)  
            // TODO: We need to somehow mark this entry as 'uninit'
            *pValueArrayEntryGuest = *pValueArrayEntry = 0;
          }
        }
        else {
          // (comment added 2005)  
          // TODO: We need to somehow mark this entry as 'unallocated'
          *pValueArrayEntryGuest = *pValueArrayEntry = 0;
        }
      }
    }

    // Push 1 symbol on stack to represent single elt. dereference:

    stringStackPush(&fullNameStack, ZEROTH_ELT);

    // Push fullFjalarName onto enclosingVarNamesStack:
    if (fullFjalarName) {
      stringStackPush(&enclosingVarNamesStack, fullFjalarName);
    }

    new_args.var                    = var;
    new_args.numDereferences        = numDereferences + 1;
    new_args.pValueArray            = pValueArray;
    new_args.pValueArrayGuest       = pValueArrayGuest;
    new_args.numElts                = numElts;
    new_args.performAction          = performAction;
    new_args.varOrigin              = (varOrigin == DERIVED_FLATTENED_ARRAY_VAR)
                                      ? varOrigin : DERIVED_VAR;
    new_args.trace_vars_tree        = trace_vars_tree;
    new_args.disambigOverride       = disambigOverride;
    new_args.numStructsDereferenced = numStructsDereferenced;
    new_args.varFuncInfo            = varFuncInfo;
    new_args.isEnter                = isEnter;

    visitSequence(&new_args);

    // Pop fullFjalarName from stack
    if (fullFjalarName) {
      stringStackPop(&enclosingVarNamesStack);
    }

    // Pop 1 symbol off
    stringStackPop(&fullNameStack);
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (IS_AGGREGATE_TYPE(var->varType)) {
    tl_assert(0 == layersBeforeBase);

    // Push fullFjalarName onto enclosingVarNamesStack:
    if (fullFjalarName) {
      stringStackPush(&enclosingVarNamesStack, fullFjalarName);
    }

    new_args.class = var->varType;
    new_args.pValue = (Addr) NULL;
    new_args.pValueGuest = (Addr) NULL;
    new_args.isSequence = True;
    new_args.pValueArray = pValueArray;
    new_args.pValueArrayGuest = pValueArrayGuest;
    new_args.numElts = numElts;
    new_args.performAction = performAction;
    new_args.varOrigin = varOrigin;
    new_args.trace_vars_tree = trace_vars_tree;
    new_args.numStructsDereferenced = numStructsDereferenced;
    new_args.varFuncInfo = varFuncInfo;
    new_args.isEnter = isEnter;
    new_args.tResult = tResult;

    visitClassMemberVariables(&new_args);

    // Pop fullFjalarName from stack
    if (fullFjalarName) {
      stringStackPop(&enclosingVarNamesStack);
    }

  }
  if (fullFjalarName)
    VG_(free)((void*)fullFjalarName);

  FJALAR_DPRINTF("Exit  visitSequence - var: %s\n", var->name);
}
