/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

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

// This increments every time a call to visitSingleVar() or
// visitSequence() is made.  It is up to the caller to reset this
// properly!
int g_variableIndex = 0;

extern FunctionTree* globalFunctionTree;



static
void visitSingleVar(VariableEntry* var,
                    UInt numDereferences,
                    Addr pValue,
                    Addr pValueGuest,
                    Bool overrideIsInit,
                    Bool alreadyDerefedCppRef, // only relevant for C++ reference parameters
                    // This function performs an action for each variable visited:
                    TraversalAction *performAction,
                    VariableOrigin varOrigin,
                    char* trace_vars_tree,
                    DisambigOverride disambigOverride,
                    UInt numStructsDereferenced,
                    FunctionEntry* varFuncInfo,
                    Bool isEnter);

static
void visitSequence(VariableEntry* var,
                   UInt numDereferences,
                   Addr* pValueArray,
                   Addr* pValueArrayGuest,
                   UInt numElts,
                   // This function performs an action for each variable visited:
		   TraversalAction *performAction,
                   VariableOrigin varOrigin,
                   char* trace_vars_tree,
                   DisambigOverride disambigOverride,
                   UInt numStructsDereferenced,
                   FunctionEntry* varFuncInfo,
                   Bool isEnter);

// This is an example of a function that's valid to be passed in as
// the performAction parameter to visitVariable:
/*
TraversalResult performAction(VariableEntry* var,
                              char* varName,
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
char* DEREFERENCE = "[]";
char* ZEROTH_ELT = "[0]";
char* DOT = ".";
char* ARROW = "->";
char* STAR = "*";

// This stack represents the full name of the variable that we
// currently want to output (Only puts REFERENCES to strings in
// fullNameStack; does not do any allocations)
#define MAX_STRING_STACK_SIZE 100

// This stack keeps track of all components of the full name of the
// variable that's currently being visited.  E.g., for a variable
// "foo->bar[]", this stack may contain something like:
//   {"foo", "->", "bar", "[]"}.
// Doing stringStackStrdup() on this stack will result in a full
// variable name.
char* fullNameStack[MAX_STRING_STACK_SIZE];
int fullNameStackSize = 0;

// This stack keeps the FULL names of all variables above the current
// one in the stack (that is, all of the current variable's
// ancestors).  For example, for a variable "foo->bar[]", this stack
// may contain something like: {"foo", "foo->bar"}.
char* enclosingVarNamesStackArray[MAX_STRING_STACK_SIZE];
char **enclosingVarNamesStack = enclosingVarNamesStackArray;
int enclosingVarNamesStackSize = 0;

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


// Visits all member variables of the class and superclass without
// regard to actually grabbing pointer values.  This is useful for
// printing out names and performing other non-value-dependent
// operations.
void visitClassMembersNoValues(TypeEntry* class,
			       TraversalAction *performAction) {

  if (VisitedStructsTable) {
    genfreehashtable(VisitedStructsTable);
    VisitedStructsTable = 0;
  }

  // Use a small hashtable to save time and space:
  VisitedStructsTable =
    genallocateSMALLhashtable(0, (int (*)(void *,void *)) &equivalentIDs);

  visitClassMemberVariables(class,
                            0,
			    0,
                            0,
                            0,
                            0,
			    0,
                            performAction,
                            GLOBAL_VAR, // doesn't matter, I don't think
                            0,
                            0,
                            0,
                            0,
                            INVALID_RESULT);
}


// Takes a TypeEntry* and a pointer to it (or an array of pointers if
// isSequence), and traverses through all of the members of the
// specified class (or struct/union).  This should also traverse
// inside of the class's superclasses and visit variables in them as
// well.  Pre: class->decType == {D_STRUCT_CLASS, D_UNION}
void visitClassMemberVariables(TypeEntry* class,
                               Addr pValue,
                               Addr pValueGuest,
                               Bool isSequence,
                               // An array of pointers to values (only
                               // valid if isSequence non-null):
                               Addr* pValueArray,
                               Addr* pValueArrayGuest,
                               UInt numElts, // Size of pValueArray
                               // This function performs an action for each variable visited:
			       TraversalAction *performAction,
                               VariableOrigin varOrigin,
                               char* trace_vars_tree,
                               // The number of structs we have dereferenced for
                               // a particular call of visitVariable(); Starts at
                               // 0 and increments every time we hit a variable
                               // which is a base struct type
                               // Range: [0, MAX_VISIT_NESTING_DEPTH]
                               UInt numStructsDereferenced,
                               // These uniquely identify the program point
                               FunctionEntry* varFuncInfo,
                               Bool isEnter,
                               TraversalResult tResult) {
  tl_assert(((class->decType == D_STRUCT_CLASS) || (class->decType == D_UNION)) &&
            IS_AGGREGATE_TYPE(class));


  // Check to see if the VisitedStructsTable contains more than
  // MAX_VISIT_STRUCT_DEPTH of the current struct type
  if (gencontains(VisitedStructsTable, (void*)class)) {
    UWord count = (UWord)(gengettable(VisitedStructsTable, (void*)class));

    if (count <= MAX_VISIT_STRUCT_DEPTH) {
      count++;
      genputtable(VisitedStructsTable, (void*)class, (void*)count);
    }
    // PUNT because this struct has appeared more than
    // MAX_VISIT_STRUCT_DEPTH times during one call to visitVariable()
    else {
      return;
    }
  }
  // If not found in the table, initialize this entry with 1
  else {
    genputtable(VisitedStructsTable, (void*)class, (void*)1);
  }

  // If we have dereferenced more than MAX_VISIT_NESTING_DEPTH
  // structs, then simply PUNT and stop deriving variables from it.
  if (numStructsDereferenced > MAX_VISIT_NESTING_DEPTH) {
    return;
  }


  // Visit member variables:
  if (class->aggType->memberVarList) {
    VarNode* i = NULL;
    for (i = class->aggType->memberVarList->first;
         i != NULL;
         i = i->next) {
      VariableEntry* curVar = i->var;

      char* top = 0;
      char numEltsPushedOnStack = 0;

      // Address of the value of the current member variable (only
      // valid if !isSequence):
      Addr pCurVarValue = 0;
      Addr pCurVarValueGuest = 0;
      // Only used if isSequence:
      Addr* pCurVarValueArray = 0;
      Addr* pCurVarValueArrayGuest = 0;

      if (!curVar->name) {
	VG_(printf)( "  Warning! Weird null member variable name!\n");
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
          !(curVar->isString && (curVar->ptrLevels == 1))) {
        // Only look at the first dimension:
        UInt arrayIndex;
        for (arrayIndex = 0; arrayIndex <= curVar->staticArr->upperBounds[0]; arrayIndex++) {
          char indexStr[5];
          top = stringStackTop(fullNameStack, fullNameStackSize);

          sprintf(indexStr, "%d", arrayIndex);

          // TODO: Subtract and add is a HACK!  Subtract one from the
          // type of curVar just because we are looping through and
          // expanding the array
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            Word count = (Word)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count--;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
          }

          if (isSequence) {
            if (pValueArray &&
                ((tResult == DEREF_MORE_POINTERS) ||
                 (tResult == DO_NOT_DEREF_MORE_POINTERS))) {
              UInt ind;

              // Create pCurVarValueArray to be the same size as pValueArray:
              pCurVarValueArray = (Addr*)VG_(malloc)(numElts * sizeof(Addr));
              pCurVarValueArrayGuest =
		(Addr*)VG_(malloc)(numElts * sizeof(Addr));

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

          if (isSequence) {
            visitSequence(curVar,
                          0,
                          pCurVarValueArray,
                          pCurVarValueArrayGuest,
                          numElts,
                          performAction,
                          DERIVED_FLATTENED_ARRAY_VAR,
                          trace_vars_tree,
                          OVERRIDE_NONE,
                          numStructsDereferenced + 1, // Notice the +1 here
                          varFuncInfo,
                          isEnter);
          }
          else {
            visitSingleVar(curVar,
                           0,
                           pCurVarValue,
                           pCurVarValueGuest,
                           0,
                           0,
                           performAction,
                           DERIVED_FLATTENED_ARRAY_VAR,
                           trace_vars_tree,
                           OVERRIDE_NONE, // Start over again and read new .disambig entry
                           numStructsDereferenced + 1, // Notice the +1 here
                           varFuncInfo,
                           isEnter);
          }

          // POP all the stuff we pushed on there before
          while ((numEltsPushedOnStack--) > 0) {
            stringStackPop(fullNameStack, &fullNameStackSize);
          }

          // HACK: Add the count back on at the end
          if (gencontains(VisitedStructsTable, (void*)(curVar->varType))) {
            Word count = (Word)(gengettable(VisitedStructsTable, (void*)(curVar->varType)));
            count++;
            genputtable(VisitedStructsTable, (void*)(curVar->varType), (void*)count);
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
      // Regular member variable (without array flattening):
      else {
        if (isSequence) {
          if (pValueArray &&
              ((tResult == DEREF_MORE_POINTERS) ||
               (tResult == DO_NOT_DEREF_MORE_POINTERS))) {
            UInt ind;
            // Create pCurVarValueArray to be the same size as
            // pValueArray:
            pCurVarValueArray = (Addr*)VG_(malloc)(numElts * sizeof(Addr));
            pCurVarValueArrayGuest = 
	      (Addr*)VG_(malloc)(numElts * sizeof(Addr));

            // Iterate though pValueArray and fill up
            // pCurVarValueArray with pointer values offset by the
            // location of the member variable within the struct:
            for (ind = 0; ind < numElts; ind++) {
              // The starting address for the member variable is the
              // struct's starting address plus the location of the
              // variable within the struct TODO: Are we sure that
              // arithmetic on void* basePtrValue adds by 1?
              // Otherwise, we'd have mis-alignment issues.  (I tried
              // it in gdb and it seems to work, though.)
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

            // Override for D_DOUBLE types: For some reason, the
            // DWARF2 info.  botches the locations of double variables
            // within structs, setting their data_member_location
            // fields to give them only 4 bytes of padding instead of
            // 8 against the next member variable.  If curVar is a
            // double and there exists a next member variable such
            // that the difference in data_member_location of this
            // double and the next member variable is exactly 4, then
            // decrement the double's location by 4 in order to give
            // it a padding of 8:
            if ((D_DOUBLE == curVar->varType->decType) &&
                (i->next) &&
                ((i->next->var->memberVar->data_member_location -
                  curVar->memberVar->data_member_location) == 4)) {
              pCurVarValue -= 4;
              pCurVarValueGuest -= 4;
            }
          }
        }

        top = stringStackTop(fullNameStack, fullNameStackSize);

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

        if (isSequence) {
          visitSequence(curVar,
                        0,
                        pCurVarValueArray,
                        pCurVarValueArrayGuest,
                        numElts,
                        performAction,
                        (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                        trace_vars_tree,
                        OVERRIDE_NONE,
                        numStructsDereferenced + 1, // Notice the +1 here
                        varFuncInfo,
                        isEnter);
        }
        else {
          visitSingleVar(curVar,
                         0,
                         pCurVarValue,
                         pCurVarValueGuest,
                         0,
                         0,
                         performAction,
                         (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                         trace_vars_tree,
                         OVERRIDE_NONE, // Start over again and read new .disambig entry
                         numStructsDereferenced + 1, // Notice the +1 here
                         varFuncInfo,
                         isEnter);
        }

        // POP everything we've just pushed on
        while ((numEltsPushedOnStack--) > 0) {
          stringStackPop(fullNameStack, &fullNameStackSize);
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
      Addr* superclassOffsetPtrValues = 0;
      Addr* superclassOffsetPtrValuesGuest = 0;

      char* top = 0;
      char numEltsPushedOnStack = 0;

      Superclass* curSuper = (Superclass*)(n->elt);
      tl_assert(curSuper && curSuper->class);

      top = stringStackTop(fullNameStack, fullNameStackSize);

      // If this superclass's member variables are at a non-zero
      // offset from the beginning of this class and isSequence, then
      // we need to build up a new array where each element is offset
      // by that amount and pass it on.
      if (isSequence &&
          (curSuper->member_var_offset > 0)) {
        UInt ind;
        superclassOffsetPtrValues = (Addr*)VG_(malloc)(numElts * sizeof(Addr));
        superclassOffsetPtrValuesGuest =
	  (Addr*)VG_(malloc)(numElts * sizeof(Addr));

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
        stringStackPush(fullNameStack, &fullNameStackSize, DOT);
        numEltsPushedOnStack += 1;
      }

      // Push a name prefix to denote that we are traversing into a
      // superclass:
      stringStackPush(fullNameStack, &fullNameStackSize, curSuper->className);
      stringStackPush(fullNameStack, &fullNameStackSize, DOT);
      numEltsPushedOnStack += 2;

      // This recursive call will handle multiple levels of
      // inheritance (e.g., if A extends B, B extends C, and C extends
      // D, then A will get all of its members visited, then visit the
      // members of B, then C, then D):
      visitClassMemberVariables(curSuper->class,
                                // IMPORTANT to add this offset, even
                                // though most of the time, it will be
                                // 0 except when you have multiple
                                // inheritance:
                                (isSequence ?
                                 0 : pValue + curSuper->member_var_offset),
                                (isSequence ?
                                 0 : pValueGuest+curSuper->member_var_offset),
                                isSequence,
                                // Use the offset one if available,
                                // otherwise use the regular one if
                                // member_var_offset is 0:
                                (superclassOffsetPtrValues ?
                                 superclassOffsetPtrValues : pValueArray),
                                (superclassOffsetPtrValuesGuest ?
                                 superclassOffsetPtrValuesGuest 
				 : pValueArrayGuest),
                                numElts,
                                performAction,
                                varOrigin,
                                trace_vars_tree,
                                numStructsDereferenced,
                                varFuncInfo,
                                isEnter,
                                tResult);

      // POP all the stuff we pushed on there before
      while ((numEltsPushedOnStack--) > 0) {
        stringStackPop(fullNameStack, &fullNameStackSize);
      }

      if (superclassOffsetPtrValues) {
        VG_(free)(superclassOffsetPtrValues);
        VG_(free)(superclassOffsetPtrValuesGuest);
      }
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
                        Bool isEnter,           // 1 for function entrance, 0 for exit
                        Addr stackBaseAddr,     // should only be used for FUNCTION_FORMAL_PARAM
                        Addr stackBaseAddrGuest,// should only be used for FUNCTION_FORMAL_PARAM
                        // This function performs an action for each
                        // variable visited:
			TraversalAction *performAction) {
  VarList* varListPtr = 0;
  VarIterator* varIt = 0;

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

  varIt = newVarIterator(varListPtr);

  while (hasNextVar(varIt)) {
    VariableEntry* var = nextVar(varIt);
    Addr basePtrValue = 0;
    Addr basePtrValueGuest = 0;

    if (!var->name) {
      VG_(printf)( "  Warning! Weird null variable name!\n");
      continue;
    }

    if ((varOrigin == FUNCTION_FORMAL_PARAM) && stackBaseAddr) {
      /* Note that it's OK for byteOffset to be negative here, since
	 stackBaseAddr is the fake %ebp, pointing in the middle of
	 the virtualStack frame. */
      basePtrValue = stackBaseAddr + var->byteOffset;
      basePtrValueGuest = stackBaseAddrGuest + var->byteOffset;
    }
    else if (varOrigin == GLOBAL_VAR) {
      tl_assert(IS_GLOBAL_VAR(var));
      basePtrValue = basePtrValueGuest = var->globalVar->globalLocation;

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

    stringStackPush(fullNameStack, &fullNameStackSize, var->name);

    visitVariable(var,
		  basePtrValue,
		  basePtrValueGuest,
		  0,
		  0,
		  performAction,
		  varOrigin,
		  funcPtr,
		  isEnter);

    stringStackPop(fullNameStack, &fullNameStackSize);
  }

  deleteVarIterator(varIt);
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

  // Struct/union type - use xAX but remember that xAX holds
  // a POINTER to the struct/union so we must dereference appropriately
  // WE NEED TO CHECK THAT declaredPtrLevels == 0 since we need a
  // real struct/union, not just a pointer to one
  // BE CAREFUL WITH declaredType - it may be misleading since all
  // pointers share the same declaredType
  if ((cur_node->var->ptrLevels == 0) &&
      (IS_AGGREGATE_TYPE(cur_node->var->varType))) {
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
  else if ((cur_node->var->ptrLevels == 0) &&
           (cur_node->var->varType->decType == D_UNSIGNED_LONG_LONG_INT)) {
    unsigned long long int uLong = (e->xAX) | (((unsigned long long int)(e->xDX)) << 32);

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
  else if ((cur_node->var->ptrLevels == 0) &&
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
    // Need an additional indirection level
    FJALAR_DPRINTF(" RETURN - int/ptr.: cur_node=%p, basePtr=%p\n",
                   cur_node, &(e->xAX));

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

  char* trace_vars_tree = 0;

  tl_assert(varOrigin != DERIVED_VAR);
  tl_assert(varOrigin != DERIVED_FLATTENED_ARRAY_VAR);

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
      VisitedStructsTable = 0;
    }

    // Use a small hashtable to save time and space:
    VisitedStructsTable =
      genallocateSMALLhashtable(0, (int (*)(void *,void *)) &equivalentIDs);
  }

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
		 pValueGuest,
                 overrideIsInit,
                 0,
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
                    Addr pValue,
                    Addr pValueGuest,
                    // We only use overrideIsInit when we pass in
                    // things (e.g. return values) that cannot be
                    // checked by the Memcheck A and V bits. Never have
                    // overrideIsInit when you derive variables (make
                    // recursive calls) because their addresses are
                    // different from the original's
                    Bool overrideIsInit,
                    Bool alreadyDerefedCppRef, // only relevant for C++ reference parameters
                    // This function performs an action for each
                    // variable visited:
		    TraversalAction *performAction,
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
                    Bool isEnter) {
  char* fullFjalarName = 0;
  int layersBeforeBase;

  // Initialize these in a group later
  char disambigOverrideArrayAsPointer = 0;
  char derefSingleElement = 0;
  char needToDerefCppRef = 0;
  TraversalResult tResult = INVALID_RESULT;

  tl_assert(var);

  needToDerefCppRef = ((var->referenceLevels > 0) && (numDereferences == 0));

  // Reset this counter to get C++ reference parameter variables to work properly:
  if (alreadyDerefedCppRef) {
    numDereferences = 0;
  }

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
    tl_assert(fullNameStackSize > 0);
    fullFjalarName = stringStackStrdup(fullNameStack, fullNameStackSize);

    // If we are not interested in visiting this variable or its
    // children, then PUNT:
    if (!interestedInVar(fullFjalarName, trace_vars_tree)) {
      VG_(free)(fullFjalarName);
      return;
    }

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
      VG_(free)(fullFjalarName);
      return;
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
      char derivedIsInitialized = 0;

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
          derivedIsInitialized = (overrideIsInit ? 1 :
                                  addressIsInitialized((Addr)pValue, sizeof(void*)));
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
        stringStackPush(fullNameStack, &fullNameStackSize, ZEROTH_ELT);
      }

      // Push fullFjalarName onto enclosingVarNamesStack:
      if (fullFjalarName) {
        stringStackPush(enclosingVarNamesStack, &enclosingVarNamesStackSize, fullFjalarName);
      }

      visitSingleVar(var,
                     numDereferences + 1,
                     pNewValue,
		     pNewValue,
                     overrideIsInit,
                     needToDerefCppRef,
                     performAction,
                     newVarOrigin,
                     trace_vars_tree,
                     disambigOverride,
                     numStructsDereferenced,
                     varFuncInfo,
                     isEnter);

      // Pop fullFjalarName from stack
      if (fullFjalarName) {
        stringStackPop(enclosingVarNamesStack, &enclosingVarNamesStackSize);
      }

      // Pop 1 symbol off
      if (!((var->referenceLevels > 0) && (numDereferences == 0))) {
        stringStackPop(fullNameStack, &fullNameStackSize);
      }
    }
    // 2.) Sequence dereference (can either be static or dynamic
    // array).  We need to initialize pValueArray and numElts
    // appropriately and call visitSequence()
    else {
      Addr* pValueArray = 0;
      Addr* pValueArrayGuest = 0;
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
          for (dim = 1; dim < var->staticArr->numDimensions; dim++) {
            numElts *= (1 + var->staticArr->upperBounds[dim]);
          }

          pValueArray = (Addr*)VG_(malloc)(numElts * sizeof(Addr));
          pValueArrayGuest = (Addr*)VG_(malloc)(numElts * sizeof(Addr));

          //          VG_(printf)("Static array - dims: %u, numElts: %u\n",
          //                      var->numDimensions, numElts);

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
          Addr pNewStartValue = 0;

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
            pValueArray = (Addr*)VG_(malloc)(numElts * sizeof(Addr));
            pValueArrayGuest = (Addr*)VG_(malloc)(numElts * sizeof(Addr));

            // Build up pValueArray with pointers starting at pNewStartValue
            for (i = 0; i < numElts; i++) {
              pValueArray[i] = pNewStartValue + (i * bytesBetweenElts);
              pValueArrayGuest[i] = pNewStartValue + (i * bytesBetweenElts);
            }
          }
        }
      }

      // Push 1 symbol on stack to represent sequence dereference:
      stringStackPush(fullNameStack, &fullNameStackSize, DEREFERENCE);

      // Push fullFjalarName onto enclosingVarNamesStack:
      if (fullFjalarName) {
        stringStackPush(enclosingVarNamesStack, &enclosingVarNamesStackSize, fullFjalarName);
      }

      visitSequence(var,
                    numDereferences + 1,
                    pValueArray,
		    pValueArrayGuest,
                    numElts,
                    performAction,
                    (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                    trace_vars_tree,
                    disambigOverride,
                    numStructsDereferenced,
                    varFuncInfo,
                    isEnter);

      // Pop fullFjalarName from stack
      if (fullFjalarName) {
        stringStackPop(enclosingVarNamesStack, &enclosingVarNamesStackSize);
      }

      // Pop 1 symbol off
      stringStackPop(fullNameStack, &fullNameStackSize);

      // Only free if necessary
      if (pValueArray) {
        VG_(free)(pValueArray);
        pValueArray = 0;
        VG_(free)(pValueArrayGuest);
        pValueArrayGuest = 0;
      }
    }
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (IS_AGGREGATE_TYPE(var->varType)) {
    tl_assert(0 == layersBeforeBase);

    visitClassMemberVariables(var->varType,
                              pValue,
                              pValueGuest,
                              0,
			      0,
                              0,
                              0,
                              performAction,
                              varOrigin,
                              trace_vars_tree,
                              numStructsDereferenced,
                              varFuncInfo,
                              isEnter,
                              tResult);
  }
  if (fullFjalarName)
    VG_(free)(fullFjalarName);
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
                   Addr* pValueArray,
                   Addr* pValueArrayGuest,
                   UInt numElts, // Size of pValueArray
                   // This function performs an action for each variable visited:
		   TraversalAction *performAction,
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
                   Bool isEnter) {

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
      (!((layersBeforeBase == 0) && IS_AGGREGATE_TYPE(var->varType)))) {

    // (Notice that this uses strdup to allocate on the heap)
    tl_assert(fullNameStackSize > 0);
    fullFjalarName = stringStackStrdup(fullNameStack, fullNameStackSize);

    // If we are not interested in visiting this variable or its
    // children, then PUNT:
    if (!interestedInVar(fullFjalarName, trace_vars_tree)) {
      VG_(free)(fullFjalarName);
      return;
    }

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
      VG_(free)(fullFjalarName);
      return;
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
            // TODO: We need to somehow mark this entry as 'uninit'
            *pValueArrayEntryGuest = *pValueArrayEntry = 0;
          }
        }
        else {
          // TODO: We need to somehow mark this entry as 'unallocated'
          *pValueArrayEntryGuest = *pValueArrayEntry = 0;
        }
      }
    }

    // Push 1 symbol on stack to represent single elt. dereference:

    stringStackPush(fullNameStack, &fullNameStackSize, ZEROTH_ELT);

    // Push fullFjalarName onto enclosingVarNamesStack:
    if (fullFjalarName) {
      stringStackPush(enclosingVarNamesStack, &enclosingVarNamesStackSize, fullFjalarName);
    }

    visitSequence(var,
                  numDereferences + 1,
                  pValueArray,
                  pValueArrayGuest,
                  numElts,
                  performAction,
                  (varOrigin == DERIVED_FLATTENED_ARRAY_VAR) ? varOrigin : DERIVED_VAR,
                  trace_vars_tree,
                  disambigOverride,
                  numStructsDereferenced,
                  varFuncInfo,
                  isEnter);

    // Pop fullFjalarName from stack
    if (fullFjalarName) {
      stringStackPop(enclosingVarNamesStack, &enclosingVarNamesStackSize);
    }

    // Pop 1 symbol off
    stringStackPop(fullNameStack, &fullNameStackSize);
  }
  // If this is the base type of a struct/union variable after all
  // dereferences have been done (layersBeforeBase == 0), then visit
  // all derived member variables:
  else if (IS_AGGREGATE_TYPE(var->varType)) {
    tl_assert(0 == layersBeforeBase);

    // Push fullFjalarName onto enclosingVarNamesStack:
    if (fullFjalarName) {
      stringStackPush(enclosingVarNamesStack, &enclosingVarNamesStackSize, fullFjalarName);
    }

    visitClassMemberVariables(var->varType,
                              0,
			      0,
                              1,
                              pValueArray,
                              pValueArrayGuest,
                              numElts,
                              performAction,
                              varOrigin,
                              trace_vars_tree,
                              numStructsDereferenced,
                              varFuncInfo,
                              isEnter,
                              tResult);

    // Pop fullFjalarName from stack
    if (fullFjalarName) {
      stringStackPop(enclosingVarNamesStack, &enclosingVarNamesStackSize);
    }

  }
  VG_(free)(fullFjalarName);
}
