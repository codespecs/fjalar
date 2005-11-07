/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* generate_fjalar_entries.h:

   After typedata.c parses the DWARF debug. info. passed in by
   readelf, this simplifies the info. and packages it into data
   structures that tools can access.
*/

#ifndef GENERATE_FJALAR_ENTRIES_H
#define GENERATE_FJALAR_ENTRIES_H

#include "typedata.h"
#include "GenericHashtable.h"

/*

The three main types here are: FunctionEntry, VariableEntry, and
TypeEntry.  All of these should be allowed to be 'sub-classed', so we
need to make sure to be careful when creating these entries to make
sure that we allocate enough space for them.

Perhaps we can use 'constructor' functions that the user must
implement for FunctionEntry, VariableEntry, and TypeEntry.

*/

typedef enum DeclaredType
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
} DeclaredType;

typedef struct _VarList VarList;
typedef struct _VarNode VarNode;

// THIS TYPE SHOULD BE IMMUTABLE SINCE IT IS SHARED!!!  TypeEntry only
// exist for structs and base types and NOT pointer types.  Pointers
// are represented using the ptr_levels field of the VariableEntry
// object.
typedef struct _TypeEntry {

  char* collectionName; // Only valid if declaredType == D_ENUMERATION,
                        // D_STRUCT, or D_UNION
  DeclaredType decType;

  int byteSize; // Number of bytes that this type takes up

  char isStructUnionType;
  VarList* memberListPtr;

  // Shared with the corresponding collection_type entry
  unsigned long num_member_funcs;
  dwarf_entry** member_funcs; // Array of size num_members; Each element is a
                              // POINTER to a dwarf_entry of type = {function}

} TypeEntry;

// Default constructor that the user has to implement, which should
// return a particular sub-class of an object.  This should call
// VG_(calloc) the proper amount of space for the object and
// initialize it with whatever initial state is necessary.
VariableEntry* constructVariableEntry();
TypeEntry* constructTypeEntry();
FunctionEntry* constructFunctionEntry();

// Destructors that should call VG_(free) on the respective entries.
void destroyVariableEntry(VariableEntry* v);
void destroyTypeEntry(TypeEntry* t);
void destroyFunctionEntry(FunctionEntry* f);

// Hash table containing structs already visited while
// deriving variables
// Keys: address of struct TypeEntry
// Values: number of times that this type has been hit while deriving
//         variables
struct genhashtable* VisitedStructsTable;

// Trivial hash and comparison functions:
unsigned int hashID(int ID);
int equivalentIDs(int ID1, int ID2);

// THIS TYPE IS IMMUTABLE AFTER INITIALIZATION (DO NOT TRY TO MODIFY
// IT UNLESS YOU ARE STILL IN THE PROCESS OF GENERATING IT)
typedef struct _VariableEntry {
  char* name; // This name gets initialized to a full-fledged name (with
              // filename and function names appended)
              // in updateAllGlobalVariableNames if this is a global variable

  char isInitialized; // 0 if uninitialized, 1 if initialized

  int byteOffset; // Byte offset for function parameters and local variables

  // Global variable information:
  char isGlobal;
  char isExternal; // False if it's file static
  unsigned long globalLocation; // The location of this variable (if isGlobal)
  char* fileName; // ONLY USED by global variables
  unsigned long functionStartPC; // The start PC address of the function which
                                 // this variable belongs to - THIS IS ONLY
                                 // VALID (non-null) FOR FILE STATIC VARIABLES
                                 // WHICH ARE DECLARED WITHIN FUNCTIONS -
                                 // see extractOneGlobalVariable()

  // varType refers to the type of the variable after all pointer
  // dereferences are completed ... so don't directly use
  // varType->byteSize ... use getBytesBetweenElts() instead
  TypeEntry* varType;

  // Levels of pointer indirection until we reach varType
  int ptrLevels;

  // Statically-allocated array information:
  char isStaticArray;
  int numDimensions; // The number of dimensions of this array
  // This is an array of size numDimensions:
  unsigned long* upperBounds; // The upper bound in each dimension
  // e.g. myArray[30][40][50] would have numDimensions = 3
  // and upperBounds = {30, 40, 50}

  // Struct member information
  char isStructUnionMember;

  // The offset from the beginning of the struct/union
  // (0 for unions)
  unsigned long data_member_location;

  TypeEntry* structParentType; // This is active (along with isGlobal) for C++ class static
                                // member variables, or it's also active (without isGlobal)
                                // for all struct member variables
} VariableEntry;

// Macro predicates for determining types for VariableEntry objects
#define VAR_IS_STRUCT(var)                                            \
  ((var->ptrLevels == 0) && (var->varType->isStructUnionType))
#define VAR_IS_STATIC_ARRAY(var) \
  ((var->isStaticArray) && (var->numDimensions >= 1))


// Defines a doubly-linked list of VariableEntry objects - each node
// contains a POINTER to an entry so that it can be sub-classed.
struct _VarNode {
  // dynamically-allocated - must be destroyed with
  // destroyVariableEntry()
  VariableEntry* var;
  VarNode* prev;
  VarNode* next;
};

struct _VarList {
  VarNode* first;
  VarNode* last;
  unsigned int numVars;
};

void clearVarList(VarList* varListPtr);
void insertNewNode(VarList* varListPtr);
void deleteTailNode(VarList* varListPtr);


// Contains a block of information about a particular function
typedef struct _FunctionEntry {
  char* name;           // The standard C name for a function - i.e. "sum"
  char* mangled_name;// The mangled name (C++ only)

  char* demangled_name; // mangled_name becomes demangled (C++ only)
                        // after running updateAllDaikonFunctionInfoEntries()
                        // i.e. "sum(int*, int)"
                        // this is like 'name' except with a full
                        // function signature

  // Using VG_(get_fnname) and VG_(get_fnname_if_entry), Valgrind
  // returns function names that are either regular ole' names which
  // match 'name' or demangled C++ names which match 'demangled_name'.
  // We are using a very simple heuristic to tell which one has been
  // returned.  If the last character is a ')', then it's a demangled
  // C++ name; otherwise, it's a regular C name.

  char* filename;
  /* fjalar_name is like name, but made unique by prepending a munged copy
     of filename */
  char *fjalar_name; // This is initialized once when the
                     // FunctionEntry entry is created from the
                     // corresponding dwarf_entry in
                     // initializeFunctionTable() but it is
                     // deleted and re-initialized to a full function
                     // name with parameters and de-munging (for C++)
                     // in updateAllDaikonFunctionInfoEntries()

  // All instructions within the function are between
  // startPC and endPC, inclusive I believe)
  unsigned long startPC;
  unsigned long endPC;

  char isExternal; // 1 if it's globally visible, 0 if it's file static
  VarList formalParameters; // Variables for formal parameters
  VarList localArrayVariables;   // keep only locally-declared STATIC ARRAYS
  VarList returnValue;      // Variables for return value

  TypeEntry* parentClass; // only non-null if this is a C++ member function;
                          // points to the class which this function belongs to

  char accessibility; // 0 if none - ASSUMED TO BE PUBLIC!!!
                      // 1 (DW_ACCESS_public) if public,
                      // 2 (DW_ACCESS_protected) if protected,
                      // 3 (DW_ACCESS_private) if private

  // GNU Binary tree of variables to trace within this function - only valid when
  // Kvasir is run with the --var-list-file command-line option:
  // This is initialized in updateAllDaikonFunctionInfoEntries()
  char* trace_vars_tree;
  char trace_vars_tree_already_initialized; // Has trace_vars_tree been initialized?
} FunctionEntry;

// Hashtable that holds information about all functions
// Key: (unsigned int) address of the function
// Value: (FunctionEntry*) Pointer to FunctionEntry
struct genhashtable* FunctionTable;

FunctionEntry* findFunctionEntryByFjalarNameSlow(char* unique_name);
inline FunctionEntry* findFunctionEntryByStartAddr(unsigned int startPC);
FunctionEntry* findFunctionEntryByAddrSlow(unsigned int addr);


// WARNING: The only entries in TypesTable are for types that are
// actually associated with variables used in the program.  If no
// variable in your program uses a certain type, then it does not have
// an entry in here!!!  This prevents us from including all sorts of
// junky types from libraries in this table (which have entries in the
// debug. info.) and ensures that we only have types in here that are
// referenced by variables that we are tracing.  The one down-side of
// this strategy is that when you are coercing types using a .disambig
// file, you must coerce it to a type that is used by some other
// variable, or else it doesn't appear in this table.

// Hash table containing TypeEntry entries
// Keys: ID from dwarf_entry
// Values: TypeEntry corresponding to the ID
//         (Hopefully, if all goes well, the only TypeEntry values
//          in this table are REAL entries whose dwarf_entry has
//          is_declaration NULL, not fake declaration entries)
struct genhashtable* TypesTable;
TypeEntry* findTypeEntryByName(char* name);


// List of all global variables
// (including C++ static member variables - these have structParentType initialized
//  so DON'T TRY TO PRINT THEM AT ALL PROGRAM POINTS OR ELSE WE WILL SEGFAULT OFTEN!
//  only try to print them during program points whose FunctionEntry::parentClass ==
//  VariableEntry::structParentType
VarList globalVars;

// Range of global variable addresses
unsigned long highestGlobalVarAddr; // The location of the highest-addr member of globalVars + its byte size
unsigned long lowestGlobalVarAddr;  // The location of the lowest-addr member of globalVars


void initializeAllFjalarData(); //daikon_preprocess_entry_array();

int determineFormalParametersStackByteSize(FunctionEntry* f);
//char isAddrInGlobalSpace(unsigned long a, int numBytes);

unsigned int hashString(char* str);
int equivalentStrings(char* str1, char* str2);


// TODO: Perhaps we can print out variables and stuff in XML format?
// It would be much easier for humans to read through with a graphical
// browser:
void printFunctionTable();
void printGlobalVars();
void printOneVariable(VariableEntry* var, char doNotRecurse, char firstTimePrinting);
void printVariablesInList(VarList* varListPtr, int leadingSpaces, TypeEntry* structType);

#endif
