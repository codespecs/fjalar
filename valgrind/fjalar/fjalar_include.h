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

__inline__ TypeEntry* findTypeEntryByName(char* name);


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
// into FunctionExecutionStateStacka
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
