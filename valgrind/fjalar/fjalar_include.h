/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_include.h

These are the Fjalar functions that should be directly available for
tools to access.

*/

#ifndef FJALAR_INCLUDE_H
#define FJALAR_INCLUDE_H

#include "GenericHashtable.h"
#include "tool.h"

typedef enum {
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
  D_STRUCT,         // This includes C++ classes as well!!!
  D_UNION,
  D_FUNCTION,
  D_VOID,
  D_CHAR_AS_STRING, // when .disambig 'C' option is used with chars
  D_BOOL            // C++ only
} DeclaredType;


typedef enum VisibilityType {
  PUBLIC_VISIBILITY,
  PROTECTED_VISIBILITY,
  PRIVATE_VISIBILITY
} VisibilityType;


typedef struct _VarList VarList;
typedef struct _VarNode VarNode;

typedef struct _SimpleList SimpleList;
typedef struct _SimpleNode SimpleNode;

typedef struct _FunctionEntry FunctionEntry;
typedef struct _Superclass Superclass;



/*

The three main types here are: FunctionEntry, VariableEntry, and
TypeEntry.  All of these should be allowed to be 'sub-classed', so we
need to make sure to be careful when creating these entries to make
sure that we allocate enough space for them.

*/

// THIS TYPE SHOULD BE IMMUTABLE SINCE IT IS SHARED!!!  TypeEntry only
// exist for structs and base types and NOT pointer types.  Pointers
// are represented using the ptrLevels field of the VariableEntry
// object.  Thus, arbitrary levels of pointers to a particular type
// can be represented by one TypeEntry instance.
typedef struct _TypeEntry {

  DeclaredType decType;
  char* collectionName; // Only valid if decType ==
                        // {D_ENUMERATION, D_STRUCT, D_UNION}

  int byteSize; // Number of bytes that this type takes up

  char isStructUnionType;
  // Everything below here is only valid if isStructUnionType:

  // Non-static (instance) member variables (only non-null if at least
  // 1 exists):
  VarList* memberVarList;

  // Static (class) member variables (only non-null if at least 1
  // exists):
  // Remember that static member variables are actually allocated
  // at statically-fixed locations like global variables
  // (All VariableEntry instances in this list are also aliased in the
  // globalVars list because static member variables are really
  // globals albeit with limited scoping)
  VarList* staticMemberVarList;

  // For C++: List of pointers to member functions of this class:
  // Every elt is a FunctionEntry* so this is like List<FunctionEntry>
  // (Only non-null if there is at least 1 member function)
  SimpleList* /* FunctionEntry* */ memberFunctionList;

  // Special member functions that are constructors/destructors:
  // (Only non-null if there is at least 1 of them)
  SimpleList* /* FunctionEntry* */ constructorList;
  SimpleList* /* FunctionEntry* */ destructorList;

  // A list of classes that are the superclasses of this class
  // Every elt is a Superclass* so this is like List<Superclass>
  // (Only non-null if there is at least 1 superclass)
  // (We never free the dynamically-allocated Superclass entries,
  //  but that shouldn't really matter in practice - oh well...)
  SimpleList* /* Superclass* */ superclassList;
} TypeEntry;

// Return a type entry, given the name of the type:
TypeEntry* getTypeEntry(char* typeName);

typedef struct {
  struct geniterator* it;
} TypeIterator;

TypeIterator* newTypeIterator();
char hasNextType(TypeIterator* typeIt);
TypeEntry* nextType(TypeIterator* typeIt);
void deleteTypeIterator(TypeIterator* typeIt);


struct _Superclass {
  char* className;
  TypeEntry* class;
  VisibilityType inheritance;
  // All the member vars of this superclass are located within the
  // subclass starting at location member_var_offset.  This means that
  // we must add member_var_offset to the data_member_location of
  // member variables in 'class' in order to find them in the
  // sub-class:
  unsigned long member_var_offset;
};


// THIS TYPE IS IMMUTABLE AFTER INITIALIZATION (DO NOT TRY TO MODIFY
// IT UNLESS YOU ARE STILL IN THE PROCESS OF GENERATING IT)
// (with the exception of the disambigMultipleElts and
// pointerHasEverBeenObserved fields)
typedef struct _VariableEntry {
  char* name; // For non-global variables, this name is how it appears
              // in the program, but for globals and file-static
              // variables, it is made into a unique identifier by
              // appending filename and function names if necessary.

  int byteOffset; // Byte offset for function parameters and local variables

  // Global variable information:
  char isGlobal;   // True if it's either global or file-static
  char isExternal; // True if visible outside of fileName;
                   // False if it's file-static

  char isStaticArray; // Is the variable a statically-sized array?
		      // (Placed here so that the compiler can
		      // hopefully pack all the chars together to save
		      // space)

  char isString; // Does this variable look like a C-style string (or
		 // a pointer to a string, or a pointer to a pointer
		 // to a string, etc)?  True iff varType == D_CHAR and
		 // ptrLevels > 0

  char* fileName; // ONLY USED by global variables

  Addr globalLocation; // The compiled location of this global variable
  Addr functionStartPC; // The start PC address of the function which
                        // this variable belongs to - THIS IS ONLY
                        // VALID (non-null) FOR FILE STATIC VARIABLES
                        // WHICH ARE DECLARED WITHIN FUNCTIONS -
                        // see extractOneGlobalVariable()

  // varType refers to the type of the variable after all pointer
  // dereferences are completed ... so don't directly use
  // varType->byteSize ... use getBytesBetweenElts() instead
  TypeEntry* varType;

  // Levels of pointer indirection until we reach varType.  This
  // allows a single VarType instance to be able to represent
  // variables that are pointers to that type.
  // If something is an array, that increments ptrLevels as well.
  // [For C++, this does NOT take reference (&) modifiers into account]
  char ptrLevels;

  // For C++ only, this is 1 if this variable is a reference to the
  // type denoted by varType (this shouldn't really increase above 1
  // because you can't have multiple levels of references, I don't
  // think)
  char referenceLevels;

  // Statically-allocated array information
  // (Only valid if isStaticArray)
  char numDimensions; // The number of dimensions of this array
  // This is an array of size numDimensions:
  unsigned int* upperBounds; // The upper bound in each dimension
  // e.g. myArray[30][40][50] would have numDimensions = 3
  // and upperBounds = {30, 40, 50}

  // For .disambig option: 0 for no disambig info, 'A' for array, 'P'
  // for pointer, 'C' for char, 'I' for integer, 'S' for string
  // (Automatically set a 'P' disambig for the C++ 'this' parameter
  // since it will always point to one element)
  char disambig;

  // Only relevant for pointer variables (ptrLevels > 0):
  // 1 if this particular variable has ever pointed to
  // more than 1 element, 0 otherwise.
  // These are the only two fields of this struct which should
  // EVER be modified after their creation.
  // They are used to generate a .disambig file using --smart-disambig
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

  TypeEntry* structParentType; // This is active (along with isGlobal) for C++ class static
                                // member variables, or it's also active (without isGlobal)
                                // for all struct member variables

  VisibilityType visibility; // Only relevant for C++ member variables

} VariableEntry;


#define VAR_IS_STRUCT(var)                                            \
  ((var->ptrLevels == 0) && (var->varType->isStructUnionType))

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

void clearVarList(VarList* varListPtr, char destroyVariableEntries);
void insertNewNode(VarList* varListPtr);
void deleteTailNode(VarList* varListPtr);

typedef struct {
  VarNode* curNode;
} VarIterator;

VarIterator* newVarIterator(VarList* vlist);
char hasNextVar(VarIterator* varIt);
VariableEntry* nextVar(VarIterator* varIt);
void deleteVarIterator(VarIterator* varIt);


// Ultra generic singly-linked list with a void* element
// Only meant to support forward traversal
// Doesn't do any dynamic memory allocation or de-allocation

struct _SimpleNode {
  void* elt;
  SimpleNode* next;
};

struct _SimpleList {
  SimpleNode* first;
  SimpleNode* last;
  UInt numElts;
};

void SimpleListInsert(SimpleList* lst, void* elt);
void* SimpleListPop(SimpleList* lst);
void SimpleListClear(SimpleList* lst);
void SimpleListInit(SimpleList* lst);

// Contains a block of information about a particular function
struct _FunctionEntry {
  // The standard C name for a function (i.e. "sum")
  char* name;

  char* mangled_name;   // The mangled name (C++ only)
  char* demangled_name;   // The de-mangled name (C++ only)

  char* filename;
  /* fjalar_name is like name, but made unique by prepending a munged copy
     of filename */
  char *fjalar_name; // This is initialized once when the
                     // FunctionEntry entry is created from the
                     // corresponding dwarf_entry in
                     // initializeFunctionTable()

  // All instructions within the function are between
  // startPC and endPC, inclusive I believe)
  Addr startPC;
  Addr endPC;

  char isExternal; // 1 if it's globally visible, 0 if it's file static
  VarList formalParameters; // Variables for formal parameters
  VarList localArrayAndStructVars; // Locally-declared structs and static array variables
  VarList returnValue;      // Variable for return value (should contain at most 1)

  TypeEntry* parentClass; // only non-null if this is a C++ member function;
                          // points to the class which this function belongs to

  char accessibility; // 0 if none - ASSUMED TO BE PUBLIC!!!
                      // 1 (DW_ACCESS_public) if public,
                      // 2 (DW_ACCESS_protected) if protected,
                      // 3 (DW_ACCESS_private) if private

  // GNU Binary tree of variables to trace within this function - only valid when
  // Kvasir is run with the --var-list-file command-line option:
  // This is initialized in initializeFunctionTable()
  char* trace_vars_tree;
  char trace_vars_tree_already_initialized; // Has trace_vars_tree been initialized?
};

FunctionEntry* getFunctionEntryFromFjalarName(char* fjalar_name);
__inline__ FunctionEntry* getFunctionEntryFromStartAddr(unsigned int startPC);
FunctionEntry* getFunctionEntryFromAddr(unsigned int addr);

typedef struct {
  struct geniterator* it;
} FuncIterator;

FuncIterator* newFuncIterator();
char hasNextFunc(FuncIterator* funcIt);
FunctionEntry* nextFunc(FuncIterator* funcIt);
void deleteFuncIterator(FuncIterator* funcIt);

// Global singleton entries for basic types.  These do not need to be
// placed in TypesTable because they are un-interesting.
TypeEntry UnsignedCharType;
TypeEntry CharType;
TypeEntry UnsignedShortType;
TypeEntry ShortType;
TypeEntry UnsignedIntType;
TypeEntry IntType;
TypeEntry UnsignedLongLongIntType;
TypeEntry LongLongIntType;
TypeEntry UnsignedFloatType;
TypeEntry FloatType;
TypeEntry UnsignedDoubleType;
TypeEntry DoubleType;
TypeEntry UnsignedLongDoubleType;
TypeEntry LongDoubleType;
TypeEntry FunctionType;
TypeEntry VoidType;
TypeEntry BoolType;


// Dynamic entries for tracking state at function entrances and exits
// (used mainly by FunctionExecutionStateStack in fjalar_main.c)
// THIS CANNOT BE SUB-CLASSED RIGHT NOW because it is placed inline
// into FunctionExecutionStateStack
typedef struct {
  FunctionEntry* func; // The function whose state we are tracking

  Addr  EBP; // %ebp as calculated from %esp at function entrance time

  Addr  lowestESP; // The LOWEST value of %ESP that is encountered
                   // while we are in this function -
                   // We need this to see how deep a function penetrates
                   // into the stack to see what is safe to dereference
                   // when this function exits

  // Return values of function exit -
  // These should NOT be valid on the stack, they should
  // only be valid right after popping an entry off the
  // stack upon function exit:
  // (TODO: What does this mean?  Is this still valid?)

  // As of Valgrind 3.0, we now keep V-bits for all of these
  // in the shadow memory:
  int EAX; // %EAX
  int EDX; // %EDX
  double FPU; // FPU %st(0)

  // This is a copy of the portion of the Valgrind stack
  // that is above EBP - it holds function formal parameter
  // values that was passed into this function upon entrance.
  // We reference this virtualStack at function exit in order
  // to print out the SAME formal parameter values upon exit
  // as upon entrance.
  char* virtualStack;
  int virtualStackByteSize; // Number of 1-byte entries in virtualStack

} FunctionExecutionState;



typedef enum {
  DERIVED_VAR, // Always switches to this after one recursive call
  DERIVED_FLATTENED_ARRAY_VAR, // A derived variable as a result of flattening an array
  GLOBAL_VAR,
  FUNCTION_FORMAL_PARAM,
  FUNCTION_RETURN_VAR // Only relevant for function exits
} VariableOrigin;

// These result values control the actions of the data structure
// traversal machinery:
typedef enum {
  INVALID_RESULT = 0,
  // When we don't really care about pointer dereferences at all
  // (not the same as DO_NOT_DEREF_MORE_POINTERS!)
  DISREGARD_PTR_DEREFS,

  // When we don't want to derive further values by dereferencing
  // pointers.  All values of variables derived from the visited
  // variable will simply be null.  However, we will still continue to
  // derive variables by traversing inside of structs and arrays:
  DO_NOT_DEREF_MORE_POINTERS,
  // Attempt to derive more values by dereferencing pointers after
  // visiting the current variable:
  DEREF_MORE_POINTERS,

  // Stop the traversal after this variable and do not derive anything
  // further:
  STOP_TRAVERSAL
} TraversalResult;


typedef enum DisambigOverride {
  OVERRIDE_NONE,
  OVERRIDE_CHAR_AS_STRING, // 'C' for base "char" and "unsigned char" types
  OVERRIDE_STRING_AS_ONE_CHAR_STRING, // 'C' for pointer to "char" and "unsigned char"
  OVERRIDE_STRING_AS_INT_ARRAY, // 'A' for pointer to "char" and "unsigned char"
  OVERRIDE_STRING_AS_ONE_INT,   // 'P' for pointer to "char" and "unsigned char"
  OVERRIDE_ARRAY_AS_POINTER     // 'P' for pointer to anything
} DisambigOverride;


// This increments every time a call to visitSingleVar() or
// visitSequence() is made.  It is up to the caller to reset this
// properly!
int g_variableIndex;

void visitClassMembersNoValues(TypeEntry* class,
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
                                                                char));

// Takes a TypeEntry* and (optionally, a pointer to its memory
// location), and traverses through all of the members of the
// specified class (or struct/union).  This should also traverse
// inside of the class's superclasses and visit variables in them:
void visitClassMemberVariables(TypeEntry* class,
                               void* pValue,
                               char isSequence,
                               // An array of pointers to values (only
                               // valid if isSequence non-null):
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
                               // The number of structs we have dereferenced for
                               // a particular call of visitVariable(); Starts at
                               // 0 and increments every time we hit a variable
                               // which is a base struct type
                               // Range: [0, MAX_VISIT_NESTING_DEPTH]
                               UInt numStructsDereferenced,
                               // These uniquely identify the program point
                               FunctionEntry* varFuncInfo,
                               char isEnter,
                               TraversalResult tResult);


// Visits an entire group of variables, depending on the value of varOrigin:
// If varOrigin == GLOBAL_VAR, then visit all global variables
// If varOrigin == FUNCTION_FORMAL_PARAM, then visit all formal parameters
// of the function denoted by funcPtr
// If varOrigin == FUNCTION_RETURN_VAR, then visit the return value variable
// of the function denoted by funcPtr
void visitVariableGroup(VariableOrigin varOrigin,
                        FunctionEntry* funcPtr, // 0 for unspecified function
                        char isEnter,           // 1 for function entrance, 0 for exit
                        char* stackBaseAddr,
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
                                                         char));

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
                                                       char));

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
                   char isEnter);



// Returns true iff the address is within a global area as specified
// by the executable's symbol table (it lies within the .data, .bss,
// or .rodata sections):
char addressIsGlobal(unsigned int addr);



// This queries FunctionSymbolTable:
// (Accepts regular name for C and mangled name for C++)
Addr getFunctionStartAddr(char* name);
// This queries ReverseFunctionSymbolTable:
// (Returns regular name for C and mangled name for C++)
char* getFunctionName(Addr startAddr);
// This queries VariableSymbolTable:
// (Accepts regular name for C and mangled name for C++)
Addr getGlobalVarAddr(char* name);

int returnArrayUpperBoundFromPtr(VariableEntry* var, Addr varLocation);
int getBytesBetweenElts(VariableEntry* var);

#define addressIsAllocated(addressInQuestion, numBytes) addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 1)
#define addressIsInitialized(addressInQuestion, numBytes) addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 0)

char addressIsAllocatedOrInitialized(Addr addressInQuestion, unsigned int numBytes, char allocatedOrInitialized);
char are_some_bytes_init(Addr addressInQuestion, unsigned int numBytes);

char* DEREFERENCE;
char* ZEROTH_ELT;
char* DOT;
char* ARROW;
char* STAR;



// Global variables that are set by command-line options

// Boolean flags
Bool fjalar_debug;
Bool fjalar_with_gdb;
Bool fjalar_ignore_globals;
Bool fjalar_ignore_static_vars;
Bool fjalar_limit_static_vars;
Bool fjalar_default_disambig;
Bool fjalar_smart_disambig;
Bool fjalar_output_struct_vars;
Bool fjalar_flatten_arrays;
Bool fjalar_func_disambig_ptrs;
Bool fjalar_disambig_ptrs;
int  fjalar_array_length_limit;

UInt MAX_VISIT_STRUCT_DEPTH;
UInt MAX_VISIT_NESTING_DEPTH;

// These are used as both strings and boolean flags -
// They are initialized to 0 upon initiation so if they are
// never filled with values by the respective command-line
// options, then they can be treated as False
char* fjalar_dump_prog_pt_names_filename;
char* fjalar_dump_var_names_filename;
char* fjalar_trace_prog_pts_filename;
char* fjalar_trace_vars_filename;
char* fjalar_disambig_filename;
char* fjalar_program_stdout_filename;
char* fjalar_program_stderr_filename;
char* fjalar_xml_output_filename;

// The filename of the target executable:
char* executable_filename;


// Trivial comparison functions:
int equivalentIDs(int ID1, int ID2);

unsigned int hashString(char* str);
int equivalentStrings(char* str1, char* str2);

char* stringStackPop(char** stringStack, int* pStringStackSize);
void stringStackPush(char** stringStack, int* pStringStackSize, char* str);


char prog_pts_tree_entry_found(FunctionEntry* cur_entry);


#endif
