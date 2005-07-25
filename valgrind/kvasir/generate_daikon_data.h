/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* generate_daikon_data.h:
   Contains the type declarations that generates daikon-specific data
   structures from parsing dwarf_entry_array
*/

#ifndef GENERATE_DAIKON_DATA_H
#define GENERATE_DAIKON_DATA_H

#include "typedata.h"
#include "GenericHashtable.h"
#include "dyncomp_main.h"
#include "union_find.h"

//#define SHOW_DEBUG

typedef enum DaikonDeclaredType
{
  D_NO_TYPE, // Create padding
  D_UNSIGNED_CHAR,
  D_CHAR,
  D_UNSIGNED_SHORT,
  D_SHORT,
  D_UNSIGNED_INT,
  D_INT,
  D_UNSIGNED_LONG_LONG_INT,
  D_LONG_LONG_INT,
  D_UNSIGNED_FLOAT, // currently unused
  D_FLOAT,
  D_UNSIGNED_DOUBLE, // currently unused
  D_DOUBLE,
  D_UNSIGNED_LONG_DOUBLE, // currently unused
  D_LONG_DOUBLE,
  D_ENUMERATION,
  D_STRUCT,
  D_UNION,
  D_FUNCTION,
  D_VOID,
  D_CHAR_AS_STRING, // when .disambig 'C' option is used with chars
  D_BOOL            // C++ only
} DaikonDeclaredType;

typedef enum DaikonRepType {
  R_NO_TYPE, // Create padding
  R_INT,
  R_DOUBLE,
  R_HASHCODE,
  R_STRING
} DaikonRepType;

typedef struct _VarList VarList;
typedef struct _VarNode VarNode;

// Describes the type of a DaikonVariable
// THIS TYPE SHOULD BE IMMUTABLE SINCE IT IS SHARED!!!
// The only DaikonTypes that exist are for structs and base types (NOT pointers)
typedef struct _DaikonType {

  char* collectionName; // Only valid if declaredType == D_ENUMERATION,
                        // D_STRUCT, or D_UNION
  DaikonDeclaredType declaredType;
  DaikonRepType repType;

  int byteSize; // Number of bytes that this type takes up

  char isStructUnionType;
  VarList* memberListPtr;

  // Shared with the corresponding collection_type entry
  unsigned long num_member_funcs;
  dwarf_entry** member_funcs; // Array of size num_members; Each element is a
                              // POINTER to a dwarf_entry of type = {function}

} DaikonType;

// Hash table containing DaikonType entries
// Keys: ID from dwarf_entry
// Values: DaikonType corresponding to the ID
struct genhashtable* DaikonTypesTable;


// Hash table containing structs already visited while
// deriving Daikon variables
// Keys: address of struct DaikonType
// Values: number of times that this type has been hit while deriving
//         variables
struct genhashtable* VisitedStructsTable;

// (Used along with VisitedStructsTable)
// The maximum number of times that a certain struct should appear
// when deriving types from a certain variable
// This prevents infinite loops that occur when A has a B* within it
// and B has an A* within it, thus leading to A.B, A.B.A, A.B.A, etc...
// This number limits the maximum number of A's and B's to a certain amount:

// This is adjustable via the --struct-depth=N option:
extern int MAX_STRUCT_INSTANCES;

unsigned int hashID(int ID);
int equivalentIDs(int ID1, int ID2);

// The most basic variable available for Daikon analysis
// THIS TYPE IS IMMUTABLE AFTER INITIALIZATION (DO NOT TRY TO MODIFY IT
// UNLESS YOU ARE STILL IN THE PROCESS OF GENERATING IT)
// - EXCEPT: for the disambigMultipleElts and pointerHasEverBeenObserved fields,
//           which are only relevant in pointer variables and can be
//           modified every time this particular variable is accessed
typedef struct _DaikonVariable {

  char* name; // This name gets initialized to a full-fledged name (with
              // filename and function names appended)
              // in updateAllGlobalVariableNames if this is a global variable

  char* fileName; // ONLY USED by global variables

  char isInitialized; // 0 if uninitialized, 1 if initialized

  int byteOffset; // Byte offset for function parameters and local variables

  // Global variable information:
  char isGlobal;
  char isExternal; // False if it's file static
  unsigned long globalLocation; // The location of this variable (if isGlobal)

  unsigned long functionStartPC; // The start PC address of the function which
                                 // this variable belongs to - THIS IS ONLY
                                 // VALID (non-null) FOR FILE STATIC VARIABLES
                                 // WHICH ARE DECLARED WITHIN FUNCTIONS -
                                 // see extractOneGlobalVariable()

  // varType refers to the type of the variable after all pointer dereferences
  // are done ... so don't directly use varType->byteSize ... use
  // getBytesBetweenElts() instead
  DaikonType* varType;
  // Pointer levels in Daikon Variable representation:
  int repPtrLevels; // number of pointer dereferences before reaching varType
  // Pointer levels as declared
  int declaredPtrLevels; // same as repPtrLevels except for strings:
                         // char* and char[] have
                         // repPtrLevels = 0 but declaredPtrLevels = 1

  char isString; // 1 if varType == D_CHAR and it represents a string

  // Statically-allocated array information:
  // (isStaticArray == true) <==> (ptrLevels == 1)
  char isStaticArray;

  int numDimensions; // The number of dimensions of this array
  // This is an array of size numDimensions:
  unsigned long* upperBounds; // The upper bound in each dimension
  // e.g. myArray[30][40][50] would have numDimensions = 3
  // and upperBounds = {30, 40, 50}

  // Only relevant for pointer variables (repPtrLevels > 0):
  // 1 if this particular variable has ever pointed to
  // more than 1 element, 0 otherwise.
  // These are the only two fields of this struct which should
  // EVER be modified after their creation.
  // They are used to generate a .disambig file
  char disambigMultipleElts;
  char pointerHasEverBeenObserved;

  // Struct member information
  char isStructUnionMember;

  // The offset from the beginning of the struct/union
  // (0 for unions)
  unsigned long data_member_location;

  // For bit-fields (not yet implemented)
  int internalByteSize;
  int internalBitOffset;  // Bit offset from the start of byteOffset
  int internalBitSize;    // Bit size for bitfields

  DaikonType* structParentType; // This is active (along with isGlobal) for C++ class static
                                // member variables, or it's also active (without isGlobal)
                                // for all struct member variables

  // For .disambig option:
  // 0 for no disambig info,
  // 'A' for array, 'P' for pointer, 'C' for char, 'I' for integer, 'S' for string
  // (Automatically set a 'P' disambig for the C++ 'this' parameter
  //  since it will always point to one thing)
  char ppt_enter_disambig;
  char ppt_exit_disambig;

} DaikonVariable;

// A bunch of macro predicates for determining types
// for DaikonVariable objects
#define VAR_IS_STRUCT(var) \
  ((var->repPtrLevels == 0) && (var->varType->isStructUnionType))
#define VAR_IS_STATIC_ARRAY(var) \
  ((var->isStaticArray) && (var->numDimensions >= 1))

// Defines a doubly-linked list of Daikon variables

struct _VarNode {
     DaikonVariable var;
     VarNode* prev;
     VarNode* next;
};

struct _VarList {
     VarNode* first;
     VarNode* last;
     unsigned int numVars;
};

void insertNewNode(VarList* varListPtr);
void deleteTailNode(VarList* varListPtr);

// Contains a block of information about a particular function
typedef struct _DaikonFunctionInfo {
  char* name;           // The standard C name for a function - i.e. "sum"
  char* mangled_name;// The mangled name (C++ only)

  char* demangled_name; // mangled_name becomes demangled (C++ only)
                        // after running updateAllDaikonFunctionInfoEntries()
                        // i.e. "sum(int*, int)"

  char* filename;
  /* daikon_name is like name, but made unique by prepending a munged copy
     of filename */
  char *daikon_name; // This is initialized once when the DaikonFuncionInfo
                     // entry is created from the corresponding dwarf_entry
                     // but it is deleted and re-initialized to a full function
                     // name with parameters and de-munging (for C++) in
                     // updateAllDaikonFunctionInfoEntries()
  unsigned long startPC;
  char isExternal; // 1 if it's globally visible, 0 if it's file static
  VarList formalParameters; // Daikon variables for formal parameters
  VarList localArrayVariables;   // keep only locally-declared STATIC ARRAYS
  VarList returnValue;      // Daikon variables for return value

  DaikonType* parentClass; // only non-null if this is a C++ member function;
                           // points to the class which this function belongs to

  // To support command-line options

  // GNU Binary tree of variables to trace within this function - only valid when
  // Kvasir is run with the --trace-vars-in-file command-line option:
  // This is initialized in updateAllDaikonFunctionInfoEntries()
  char* trace_vars_tree;
  char trace_vars_tree_already_initialized; // Has trace_vars_tree been initialized?

  char accessibility; // 0 if none - ASSUMED TO BE PUBLIC!!!
                      // 1 (DW_ACCESS_public) if public,
                      // 2 (DW_ACCESS_protected) if protected,
                      // 3 (DW_ACCESS_private) if private

  // For DynComp - union-find data structures for all relevant variables
  //               at the entry and exit program points of this function

  // Important! Make sure to only initialize these only ONCE (when you
  // are outputting .decls) or else you'll get nasty duplicate
  // variable names and sets!!!

  // TODO: WARNING!  This hashtable-within-hashtable structure may
  // blow up in my face and cause a huge memory overload!!!  Remember
  // that each hashtable is initialized to a constant number!  I'll
  // try to keep them fairly small by calling
  // genallocateSMALLhashtable, but they still take up room
  // nonetheless.

  // var_uf_map:
  // Key: tag which is the leader of some entry in val_uf
  // Value: uf_object

  // Define a function (implemented as a non-null hashtable get)
  // var_uf_map.exists(val_uf leader entry) returns true if entry from
  // val_uf exists in var_uf_map.

  // var_uf_map is the variable analogue to val_uf, which is the union-find
  // for all values ever created in a program.
  struct genhashtable* ppt_entry_var_uf_map;
  struct genhashtable* ppt_exit_var_uf_map;

  // var_tags: A fixed-sized array (indexed by the serial # of Daikon
  // variables at that program point) which contains tags which are the
  // leaders of the comparability sets of their value's tags at that
  // program point.
  UInt* ppt_entry_var_tags;
  UInt* ppt_exit_var_tags;

  // new_tags: A fixed-sized array (also indexed by # of Daikon variables)
  // of the tags extracted by a certain Daikon variable's value at this
  // program point.  This structure is updated EVERY TIME the program
  // executes a program point by querying val_uf with the address of the
  // variable's value being observed and getting back the tag.
  UInt* ppt_entry_new_tags;
  UInt* ppt_exit_new_tags;

  // The size of var_tags and new_tags can be initialized during the .decls
  // run because we can count up how many Daikon variables exist at that
  // program point.  The number of Daikon variables as well as their order
  // is maintained during all program point executions in the .dtrace run
  // because the same traversal function is executing for both .decls and
  // .dtrace (and more importantly, because Daikon expects the front-end
  // output to maintain these variables in the same order).

  // This tells the sizes of ppt_[entry|exit]_[var|new]_tags
  UInt num_daikon_vars;

} DaikonFunctionInfo;

// Hashtable that holds information about all functions
// Key: (unsigned int) address of the function
// Value: (DaikonFunctionInfo*) pointer to DaikonFunctionInfo entry
struct genhashtable* DaikonFunctionInfoTable;

DaikonFunctionInfo* findFunctionInfoByNameSlow(char* name, char isDaikonName);
inline DaikonFunctionInfo* findFunctionInfoByAddr(unsigned int addr);

// List of all global variables
// (including C++ static member variables - these have structParentType initialized
//  so DON'T TRY TO PRINT THEM AT ALL PROGRAM POINTS OR ELSE WE WILL SEGFAULT OFTEN!
//  only try to print them during program points whose DaikonFunctionInfo::parentClass ==
//  DaikonVariable::structParentType
VarList globalVars;

// Range of global variable addresses
unsigned long highestGlobalVarAddr; // The location of the highest-addr member of globalVars + its byte size
unsigned long lowestGlobalVarAddr;  // The location of the lowest-addr member of globalVars

void daikon_preprocess_entry_array();
void initializeDaikonFunctionInfoTable();
void initializeGlobalVarsList();

void initializeAllClassMemberFunctions();

void printDaikonFunctionInfoTable();
void printDaikonGlobalVars();
void printOneDaikonVariable(DaikonVariable* var, char doNotRecurse, char firstTimePrinting);
void printVariablesInList(VarList* varListPtr, int leadingSpaces, DaikonType* structType);

void verifyStackParamWordAlignment(DaikonFunctionInfo* daikonEntry);
void extractFormalParameterVars(DaikonFunctionInfo* daikonEntry, function* dwarfFunctionEntry);
void extractLocalArrayAndStructVariables(DaikonFunctionInfo* daikonEntry,
                                         function* dwarfFunctionEntry);
void extractOneLocalArrayOrStructVariable(DaikonFunctionInfo* daikonEntry,
                                          dwarf_entry* dwarfParamEntry);

void extractOneFormalParameterVar(DaikonFunctionInfo* daikonEntry, dwarf_entry* dwarfParamEntry);
void extractReturnVar(DaikonFunctionInfo* daikonEntry, function* dwarfFunctionEntry);
void extractOneGlobalVariable(dwarf_entry* e, unsigned long functionStartPC);

void extractOneVariable(VarList* varListPtr,
			dwarf_entry* typePtr,
			char* variableName,
			char* fileName,
			unsigned long byteOffset,
			char isGlobal,
			char isExternal,
			unsigned long globalLocation,
			unsigned long functionStartPC,
			char isStructUnionMember,
			unsigned long data_member_location,
			int internalByteSize,
			int internalBitOffset,
			int internalBitSize,
			DaikonType* structParentType,
                        char isFormalParam);


dwarf_entry* extractModifierType(modifier_type* modifierPtr);
dwarf_entry* extractArrayType(DaikonVariable* varPtr, array_type* arrayPtr);

void extractBaseType(DaikonType* t, base_type* basePtr);
void extractEnumerationType(DaikonType* t, collection_type* collectionPtr);
void extractSubroutineType(DaikonType* t, function_type* functionPtr);
void extractVoidType(DaikonType* t);
void extractStructUnionType(DaikonType* t, dwarf_entry* e);

int determineDaikonVariableByteSize(DaikonVariable* var);
int determineFormalParametersStackByteSize(DaikonFunctionInfo* daikonEntry);
//char isAddrInGlobalSpace(unsigned long a, int numBytes);

unsigned int hashString(char* str);
int equivalentStrings(char* str1, char* str2);

#endif
