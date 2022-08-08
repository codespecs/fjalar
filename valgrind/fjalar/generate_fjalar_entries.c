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

/* generate_fjalar_entries.c:

   After typedata.c parses the DWARF debug. info. passed in by
   readelf, this simplifies the info. and packages it into data
   structures that tools can access.
*/

#include "my_libc.h"
#include "fjalar_main.h"
#include "generate_fjalar_entries.h"
#include "fjalar_include.h"
#include "fjalar_select.h"
#include "GenericHashtable.h"
#include "../coregrind/m_demangle/demangle.h"
extern char * cplus_demangle_v3 (const char *, int);

#include "fjalar_tool.h"

// Cast an intger to a void pointer in a architecture independent way. (markro)
#define VoidPtr(arg)  (void*)(ptrdiff_t)(arg)

static void initializeFunctionTable(void);
static void initializeGlobalVarsList(void);
static void initFunctionFjalarNames(void);
static void updateAllGlobalVariableNames(void);
static void initMemberFuncs(void);
static void initConstructorsAndDestructors(void);
static void createNamesForUnnamedDwarfEntries(void);
static void updateAllVarTypes(void);
static void processFunctions(void);

int determineFormalParametersStackByteSize(FunctionEntry* f);
int determineFormalParametersLowerStackByteSize(FunctionEntry* f);

static void extractFormalParameterVars(FunctionEntry* f, function* dwarfFunctionEntry);
static void extractLocalArrayAndStructVariables(FunctionEntry* f, function* dwarfFunctionEntry);
static void extractOneLocalArrayOrStructVariable(FunctionEntry* f, dwarf_entry* dwarfVariableEntry);
static void extractReturnVar(FunctionEntry* f, function* dwarfFunctionEntry);

static int determineVariableByteSize(VariableEntry* var);
static void verifyStackParamWordAlignment(FunctionEntry* f, int replace);
static char* getDeclaredFile(compile_unit* comp_unit, unsigned long offset);

static VariableEntry*
extractOneVariable(VarList* varListPtr,
                   dwarf_entry* typePtr,
                   const char* variableName,
                   char* fileName,
                   char isGlobal,
                   char isExternal,
                   char isConstant,
                   long constantValue,
                   unsigned long globalLocation,
                   unsigned long functionStartPC,
                   char isStructUnionMember,
                   unsigned long data_member_location,
                   int internalByteSize,
                   int internalBitOffset,
                   int internalBitSize,
                   TypeEntry* structParentType,
                   unsigned long dwarf_accessibility,
                   char isFormalParam,
                   char* declared_in);

static void repCheckOneVariable(VariableEntry* var);

static void XMLprintGlobalVars(void);
static void XMLprintFunctionTable(void);
static void XMLprintTypesTable(void);
static void XMLprintVariablesInList(VarList* varListPtr);
static void XMLprintOneVariable(VariableEntry* var);

FILE* xml_output_fp = 0;

// The indices to this array must match the DeclaredType enum
const int DecTypeByteSizes[] = {
  sizeof(char),                   // D_NO_TYPE, // Create padding

  sizeof(unsigned char),          // D_UNSIGNED_CHAR,
  sizeof(char),                   // D_CHAR,
  sizeof(unsigned short),         // D_UNSIGNED_SHORT,
  sizeof(short),                  // D_SHORT,
  sizeof(unsigned int),           // D_UNSIGNED_INT,
  sizeof(int),                    // D_INT,
  sizeof(unsigned long),          // D_UNSIGNED_LONG,
  sizeof(long),                   // D_INT,
  sizeof(unsigned long long int), // D_UNSIGNED_LONG_LONG_INT,
  sizeof(long long int),          // D_LONG_LONG_INT,

  sizeof(float),                  // D_FLOAT,
  sizeof(double),                 // D_DOUBLE,
  sizeof(long double),            // D_LONG_DOUBLE,

  sizeof(int),                    // D_ENUMERATION,

  sizeof(void*),                  // D_STRUCT_CLASS, // currently unused
  sizeof(void*),                  // D_UNION, // currently unused
  sizeof(void*),                  // D_FUNCTION, // currently unused
  sizeof(void*),                  // D_VOID // currently unused

  sizeof(char),                   // D_CHAR_AS_STRING
  sizeof(char),                   // D_BOOL
};

// Global singleton entries for basic types.  These do not need to be
// placed in TypesTable because they are un-interesting.
TypeEntry UnsignedCharType = {D_UNSIGNED_CHAR, 0, sizeof(unsigned char), 0};
TypeEntry CharType = {D_CHAR, 0, sizeof(char), 0};
TypeEntry UnsignedShortType = {D_UNSIGNED_SHORT, 0, sizeof(unsigned short), 0};
TypeEntry ShortType = {D_SHORT, 0, sizeof(short), 0};
TypeEntry UnsignedIntType = {D_UNSIGNED_INT, 0, sizeof(unsigned int), 0};
TypeEntry IntType = {D_INT, 0, sizeof(int), 0};
TypeEntry UnsignedLongType = {D_UNSIGNED_LONG, 0, sizeof(unsigned long), 0};
TypeEntry LongType = {D_LONG, 0, sizeof(long), 0};
TypeEntry UnsignedLongLongIntType = {D_UNSIGNED_LONG_LONG_INT, 0, sizeof(unsigned long long int), 0};
TypeEntry LongLongIntType = {D_LONG_LONG_INT, 0, sizeof(long long int), 0};
TypeEntry FloatType = {D_FLOAT, 0, sizeof(float), 0};
TypeEntry DoubleType = {D_DOUBLE, 0, sizeof(double), 0};
TypeEntry LongDoubleType = {D_LONG_DOUBLE, 0, sizeof(long double), 0};
TypeEntry FunctionType = {D_FUNCTION, 0, sizeof(void*), 0};
TypeEntry VoidType = {D_VOID, 0, sizeof(void*), 0};
TypeEntry BoolType = {D_BOOL, 0, sizeof(char), 0};

// Array indexed by DeclaredType where each entry is a pointer to one
// of the above singleton entries:
TypeEntry* BasicTypesArray[] = {
  0,                        //  D_NO_TYPE, // Create padding

  &UnsignedCharType,        //  D_UNSIGNED_CHAR,
  &CharType,                //  D_CHAR,
  &UnsignedShortType,       //  D_UNSIGNED_SHORT,
  &ShortType,               //  D_SHORT,
  &UnsignedIntType,         //  D_UNSIGNED_INT,
  &IntType,                 //  D_INT,
  &UnsignedLongType,        //  D_UNSIGNED_LONG,
  &LongType,                //  D_LONG,
  &UnsignedLongLongIntType, //  D_UNSIGNED_LONG_LONG_INT,
  &LongLongIntType,         //  D_LONG_LONG_INT,

  &FloatType,               //  D_FLOAT,
  &DoubleType,              //  D_DOUBLE,
  &LongDoubleType,          //  D_LONG_DOUBLE,

  0,                        //  D_ENUMERATION,
  0,                        //  D_STRUCT_CLASS,
  0,                        //  D_UNION,

  &FunctionType,            //  D_FUNCTION,
  &VoidType,                //  D_VOID,
  0,                        //  D_CHAR_AS_STRING
  &BoolType                 //  D_BOOL
};

// This array can be indexed using the DelaredType enum
const char* DeclaredTypeString[] = {
  "no_declared_type",       // D_NO_TYPE, // Create padding

  "unsigned char",          // D_UNSIGNED_CHAR,
  "char",                   // D_CHAR,
  "unsigned short",         // D_UNSIGNED_SHORT,
  "short",                  // D_SHORT,
  "unsigned int",           // D_UNSIGNED_INT,
  "int",                    // D_INT,
  "unsigned long",          // D_UNSIGNED_LONG,
  "long",                   // D_LONG,
  "unsigned long long int", // D_UNSIGNED_LONG_LONG_INT,
  "long long int",          // D_LONG_LONG_INT,

  "float",                  // D_FLOAT,
  "double",                 // D_DOUBLE,
  "long double",            // D_LONG_DOUBLE,

  // This should NOT be used unless you created an unnamed struct/union!
  // Use TypeEntry::typeName instead
  "enumeration",            // D_ENUMERATION
  "struct",                 // D_STRUCT_CLASS
  "union",                  // D_UNION

  "function",               // D_FUNCTION
  "void",                   // D_VOID
  "char",                   // D_CHAR_AS_STRING
  "bool",                   // D_BOOL
};

// To figure out if a certain DeclaredType t is a basic type, simply
// query whether its entry in BasicTypesArray is non-null:
#define IS_BASIC_TYPE(t) (BasicTypesArray[t])

// You need to define global variables in a .c file and init. it to 0
// or else Valgrind places it in some bizarre place ... I dunno???
struct genhashtable* TypesTable = 0;
struct genhashtable* FunctionTable = 0;
struct genhashtable* FunctionTable_by_entryPC = 0;
struct genhashtable* VisitedStructsTable = 0;

// Data structure to check for duplicate function names in the
// debugging information.
struct genhashtable* FuncNameTable = 0;

// A temporary data structure of variables that need to have their
// varType entries updated after TypesTable has been initialized.
// This is used for variables whose type entries are 'fake'
// (is_declaration == 1) so we want to fill them in with 'real' values
// of the same name later.  All variables in this list have their
// varType initialized to a dynamically-allocated TypeEntry whose
// typeName is initialized properly, but all other fields in
// this TypeEntry are empty.  During updateAllVarTypes(), we scan
// through this list, look at the varType entries, look them up in
// TypesTable, replace the entries with the real versions, and free
// the faux TypeEntry:
VarList varsToUpdateTypes = {0, 0, 0};

// Global strings

static const char* RETURN_VALUE_NAME = "return";

// For printing:
// Corresponds to DeclaredType enum:
const char* DeclaredTypeNames[] = {"D_NO_TYPE", // Create padding
                             "D_UNSIGNED_CHAR",
                             "D_CHAR",
                             "D_UNSIGNED_SHORT",
                             "D_SHORT",
                             "D_UNSIGNED_INT",
                             "D_INT",
                             "D_UNSIGNED_LONG",           // not used if 32 bit
                             "D_LONG",                    // not used if 32 bit
                             "D_UNSIGNED_LONG_LONG_INT",  // not used if 64 bit
                             "D_LONG_LONG_INT",           // not used if 64 bit
                             "D_UNSIGNED_FLOAT", // currently unused
                             "D_FLOAT",
                             "D_UNSIGNED_DOUBLE", // currently unused
                             "D_DOUBLE",
                             "D_UNSIGNED_LONG_DOUBLE", // currently unused
                             "D_LONG_DOUBLE",
                             "D_ENUMERATION",
                             "D_STRUCT_CLASS",
                             "D_UNION",
                             "D_FUNCTION",
                             "D_VOID",
                             "D_CHAR_AS_STRING",
                             "D_BOOL"};

// This is a list of function names to avoid -
// mostly as a result of weirdo C++ compiler stuff:
// (This was all done by empirical observation)
// Note: DON'T IGNORE FUNCTIONS WITH NO NAMES
// Addenda Mar 3, 2014 (markro):
// Not allowing template class member names (?)
// was causing failures.  I removed the check
// for "_M_" and all seems to be okay.
static char ignore_function_with_name(char* name) {

  FJALAR_DPRINTF("  *ppt_name: %s\n", name);

  if (!name) {
    return 0;
  }

  if ((0 == VG_(strncmp)(name, "__static_initialization_and_destruction", 39)) ||
      VG_STREQ(name, "_Alloc_hider") ||
      VG_STREQ(name, "~_Alloc_hider") ||
      VG_STREQ(name, "_Rep") ||
      (0 == VG_(strncmp)(name, "._", 2)) ||
//    (0 == VG_(strncmp)(name, "_S_", 3)) ||
//    (0 == VG_(strncmp)(name, "_M_", 3)) ||
      (0 == VG_(strncmp)(name, "_GLOBAL", 7)) ||
      (0 == VG_(strncmp)(name, "__tcf", 5)) ||
      // Hopefully the target program doesn't have this function that you want to track
      (0 == VG_(strncmp)(name, "min<size_t>", 11)) ||
      // g++-3.4 seems to show this:
      (0 == VG_(strncmp)(name, "__verify_grouping", 17))) {
    return 1;
  }
  else {
    return 0;
  }
}

// Ignores some weirdo C++ variables such as vtable function pointers
// and friends
// g++-3.4 seems to create variable names prefixed with '__gnu_cxx'
// so we will ignore these.
// (This was all done by empirical observation)
// Note: DON'T IGNORE VARIABLES WITH NO NAMES
static char ignore_variable_with_name(const char* name) {

  FJALAR_DPRINTF("\t*name: %s\n", name);

  if (!name) {
    return 0;
  }

  if (VG_STREQ(name, "__ioinit") ||
      (0 == VG_(strncmp)(name, "_vptr.", 6)) ||
      (0 == VG_(strncmp)(name, "_ZTI", 4)) ||
      (0 == VG_(strncmp)(name, "_ZTS", 4)) ||
      // libstdc++ stuff (demangled is something like '__gnu_cxx::')
      (0 == VG_(strncmp)(name, "_ZN9__gnu_cxx10", 15)) ||
      // ignore std::string stuff
      (0 == VG_(strncmp)(name, "_ZNSs4", 6)) ||
      // Found in C++ destructors
      (VG_STREQ(name, "__in_chrg"))) {
    return 1;
  }
  else {
    return 0;
  }
}

// This makes sure that we don't print out variables which
// are pointers to type _IO_FILE, etc...
// Instead, we treat these as generic void pointers
// Notice that this function only compares names but doesn't
// check whether the variable is a POINTER to this type
// Note: DON'T IGNORE TYPES WITH NO NAMES
static char ignore_type_with_name(char* name) {
  if (!name) {
    return 0;
  }

  if (0 == VG_(strncmp)(name, "_IO", 3))
    return 1;
  else
    return 0;
}

// Grabs the C++ function name after tearing off all of the '::'
// scope-resolution operators in the function name - BEFORE the first
// '(' because anything inside the paren is part of the arguments, not
// the function name (does NOT allocate a new buffer, simply moves the
// input char* cppFnName to a new location and returns it)
//
// Input:  Stack::Link::initialize(char*, Stack::Link*)
// Output: initialize(char*, Stack::Link*)
char* getRawCppFunctionName(char* cppFnName) {
  // This works by looking for the last '::' and returning a pointer
  // to the letter right after it (or returning the original pointer
  // if no '::' found.
  int i, len;
  char* rawNameStart;
  tl_assert(cppFnName);
  len = VG_(strlen)(cppFnName);

  rawNameStart = cppFnName;

  for (i = 1; i < len; i++) {
    char prev = cppFnName[i-1];
    char cur = cppFnName[i];

    if (cur == '(') {
      break;
    }

    if ((prev == ':') && (cur == ':') && (i < (len - 1))) {
      rawNameStart = &cppFnName[i+1];
    }
  }

  return rawNameStart;
}

// Super simple list - doesn't do any dynamic allocation or
// deallocation of elt - just stores pointers:

// Insert elt at the END of lst, allocating a new SimpleNode
void SimpleListInsert(SimpleList* lst, void* elt) {
  SimpleNode* newNode;
  tl_assert(lst);
  newNode = VG_(calloc)("generate_fjalar_entries.c: SimpleListInsert", 1, sizeof(*newNode));
  newNode->elt = elt;
  newNode->next = NULL;

  if (lst->first) {
    tl_assert(lst->numElts > 0 &&
              lst->last &&
              (lst->last->next == NULL));
    lst->last->next = newNode;
    lst->last = newNode;
  }
  else {
    tl_assert(lst->numElts == 0 &&
              !lst->last);
    lst->first = lst->last = newNode;
  }

  lst->numElts++;
}

// Pops off head element and returns it.
// Returns 0 if no more stuff to pop
void* SimpleListPop(SimpleList* lst) {
  if (lst->first) {
    SimpleNode* curNode;
    void* ret;
    tl_assert(lst->numElts > 0);

    curNode = lst->first;
    ret = curNode->elt;
    lst->first = curNode->next;
    lst->numElts--;
    VG_(free)(curNode);
    return ret;
  }
  else {
    tl_assert(lst->numElts == 0);
    printf(" Warning - SimpleListPop() attempting to pop an empty list\n");
    return 0;
  }
}

// Clears all elts in lst, freeing all SimpleNode(s)
void SimpleListClear(SimpleList* lst) {
  while (lst->first) {
    SimpleNode* tmp = lst->first;
    lst->first = tmp->next;
    VG_(free)(tmp);
    lst->numElts--;
  }
  lst->last = NULL;
  tl_assert(lst->numElts == 0);
}

void SimpleListInit(SimpleList* lst) {
  lst->first = NULL;
  lst->last = NULL;
  lst->numElts = 0;
}

// Inserts a new node at the end of varListPtr
void insertNewNode(VarList* varListPtr)
{
  if (varListPtr->last)
    {
      varListPtr->last->next = VG_(calloc)("generate_fjalar_entries.c: insertNewNode.1", 1, sizeof(VarNode));
      varListPtr->last->next->prev = varListPtr->last;
      varListPtr->last = varListPtr->last->next;
      varListPtr->numVars++;
    }
  else
    {
      varListPtr->last = varListPtr->first = VG_(calloc)("generate_fjalar_entries.c: insertNewNode.2", 1, sizeof(VarNode));
      varListPtr->numVars = 1;
    }

  // Construct a new VariableEntry:
  varListPtr->last->var = constructVariableEntry();
}

// Deletes the last node in *varListPtr
void deleteTailNode(VarList* varListPtr)
{
  if (varListPtr->last)
    {
      // Destroy the last VariableEntry:
      destroyVariableEntry(varListPtr->last->var);

      if (varListPtr->numVars == 1)
        {
          tl_assert(varListPtr->first == varListPtr->last);
          VG_(free)(varListPtr->last);
          //  VG_(free)(varListPtr->first);
          varListPtr->first = varListPtr->last = 0;
          varListPtr->numVars = 0;
        }
      else
        {
          varListPtr->last = varListPtr->last->prev;
          VG_(free)(varListPtr->last->next);
          varListPtr->last->next = 0;
          varListPtr->numVars--;
        }
    }
}

// Clears the list and FREEs the var contents if
// destroyVariableEntries is 1:
void clearVarList(VarList* varListPtr, Bool destroyVariableEntries) {
  VarNode* node = varListPtr->first;
  VarNode* nextNode = 0;

  while (node) {
    nextNode = node->next;
    if (destroyVariableEntries) {
      destroyVariableEntry(node->var);
    }
    VG_(free)(node);
    node = nextNode;
  }

  varListPtr->first = 0;
  varListPtr->last = 0;
  varListPtr->numVars = 0;
}

// Traverses through dwarf_entry_array and initializes all global data
// that this file exports.
// (THIS SHOULD ONLY BE CALLED ONCE DURING EACH EXECUTION or else we
//  will probably get lots of memory leaks.)
void initializeAllFjalarData(void)
{
  tl_assert(globalVars.numVars == 0);

  FJALAR_DPRINTF("ENTER initializeAllFjalarData\n");

  // (comment added 2005)  
  // TODO: We need to free up the entries in TypesTable if we are
  // really trying to be robust

  VisitedStructsTable = 0;

  // Initialize TypesTable
  TypesTable =
    genallocatehashtable((unsigned int (*)(void *)) &hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  createNamesForUnnamedDwarfEntries();

  initializeFunctionTable();

  // We need to initialize this list even if we are ignoring globals
  // (with --ignore-globals) because otherwise we won't be able to
  // find references to global variables from pointer parameters:
  initializeGlobalVarsList();

  // Run after initializeFunctionTable() so that function demangled
  // names are available if necessary:
  updateAllGlobalVariableNames();


  updateAllVarTypes();
  // Initialize member functions last after TypesTable and
  // FunctionTable have already been initialized:
  initMemberFuncs();

  // Initialize all constructors and destructors by using a heuristic
  // to pattern match names to type names:
  initConstructorsAndDestructors();


  // Some post-processing on functions to work around GCC
  // issues
  processFunctions();

  // Run this after everything else that deal with entries in
  // FunctionTable:
  initFunctionFjalarNames();

  FJALAR_DPRINTF(".data:   0x%x bytes starting at %p\n.bss:    0x%x bytes starting at %p\n.rodata: 0x%x bytes starting at %p\n.data.rel.ro: 0x%x bytes starting at %p\n",
                 data_section_size, VoidPtr(data_section_addr),
                 bss_section_size, VoidPtr(bss_section_addr),
                 rodata_section_size, VoidPtr(rodata_section_addr),
                 relrodata_section_size, VoidPtr(relrodata_section_addr));

  // Should only be called here:
  FJALAR_DPRINTF("\nChecking the representation of internal data structures ...\n");

  repCheckAllEntries();

  FJALAR_DPRINTF("All representation checks PASSED.\n");
  FJALAR_DPRINTF("EXIT  initializeAllFjalarData\n");
}

// Returns true iff the address is within a global area as specified
// by the executable's symbol table (it lies within the .data, .bss,
// or .rodata sections):
Bool addressIsGlobal(Addr addr) {
  return (((addr >= data_section_addr) && (addr < data_section_addr + data_section_size)) ||
          ((addr >= bss_section_addr) && (addr < bss_section_addr + bss_section_size)) ||
          ((addr >= rodata_section_addr) && (addr < rodata_section_addr + rodata_section_size)) ||
          ((addr >= relrodata_section_addr) && (addr < relrodata_section_addr + relrodata_section_size)));
}

// Performs a scan over all VariableEntry, TypeEntry, and
// FunctionEntry instances in various data structures and checks to
// make sure that all invariants hold true after initialization.
// Checks entries in globalVars, TypesTable, and FunctionTable.  This
// make take a bit of time to run, but it gives us confidence that our
// data structures are initialized properly and obviates the need for
// lots of checks later in execution.
void repCheckAllEntries(void) {
  VarNode* curNode;
  unsigned int numGlobalVars = 0;
  FuncIterator* funcIt;
  TypeIterator* typeIt;

  // Rep. check all variables in globalVars:

  FJALAR_DPRINTF("Rep. checking global variables list ...\n");

  for (curNode = globalVars.first;
       curNode != 0;
       curNode = curNode->next) {
    VariableEntry* curGlobalVar = curNode->var;

    // Specific requirements for global vars:
    tl_assert(IS_GLOBAL_VAR(curGlobalVar));

    // Basic checks:
    repCheckOneVariable(curGlobalVar);

    numGlobalVars++;
  }

  // Check the integrity of globalVars.numVars
  tl_assert(numGlobalVars == globalVars.numVars);


  FJALAR_DPRINTF("DONE\n");

  // Rep. check all entries in FunctionTable
  funcIt = newFuncIterator();

  FJALAR_DPRINTF("Rep. checking function entries ...\n");
  while (hasNextFunc(funcIt)) {
    FunctionEntry* f = nextFunc(funcIt);
    VarNode* n;
    unsigned int numFormalParams = 0;
    unsigned int numLocalArrayVars = 0;
    unsigned int numReturnVars = 0;

    // int prevByteOffset = 0;

    // Properties that should hold true for all FunctionEntry
    // instances:

    // There should be no unnamed functions:
    tl_assert(f->name);
    tl_assert(f->startPC);
    tl_assert(f->endPC);

    // Formal parameters:
    for (n = f->formalParameters.first;
         n != 0;
         n = n->next) {
      VariableEntry* v = n->var;

      tl_assert(!IS_GLOBAL_VAR(v));

      // It is no longer the case that the byteOffsets will be strictly
      // increasing, since we're now using the locations in the debugging
      // information, some of which may be copies in the function's private
      // data area.
      // tl_assert(v->byteOffset > prevByteOffset);
      // prevByteOffset = v->byteOffset;

      repCheckOneVariable(v);
      numFormalParams++;
    }
    tl_assert(numFormalParams == f->formalParameters.numVars);

    // Local static array variables:
    for (n = f->localArrayAndStructVars.first;
         n != 0;
         n = n->next) {
      VariableEntry* v = n->var;

      tl_assert(!IS_GLOBAL_VAR(v));

      repCheckOneVariable(v);
      numLocalArrayVars++;
    }
    tl_assert(numLocalArrayVars == f->localArrayAndStructVars.numVars);

    // Return value:

    // A function either has 0 or 1 return values
    tl_assert(f->returnValue.numVars <= 1);

    for (n = f->returnValue.first;
         n != 0;
         n = n->next) {
      VariableEntry* v = n->var;

      tl_assert(!IS_GLOBAL_VAR(v));
      tl_assert(0 == v->byteOffset);

      repCheckOneVariable(v);
      numReturnVars++;
    }
    tl_assert(numReturnVars == f->returnValue.numVars);

  }

  deleteFuncIterator(funcIt);

  FJALAR_DPRINTF("DONE\n");

  FJALAR_DPRINTF("Rep. checking type entries ...\n");

  // Rep. check all entries in TypesTable
  typeIt = newTypeIterator();

  while (hasNextType(typeIt)) {
    TypeEntry* t = nextType(typeIt);

    // All TypeEntry instances within TypesTable should NOT be basic
    // types:
    tl_assert(!IS_BASIC_TYPE(t->decType));

    // Properties that should hold true for all TypeEntry instances:

    tl_assert((D_ENUMERATION == t->decType) ||
              (D_STRUCT_CLASS == t->decType) ||
              (D_UNION == t->decType));

    // Because TypesTable is indexed by name, there should be no
    // unnamed entries in TypesTable:
    tl_assert(t->typeName);

    if (IS_AGGREGATE_TYPE(t)) {
      VarNode* n;
      unsigned int numMemberVars = 0;
      unsigned int prev_data_member_location = 0;

      SimpleNode* memberFunctionNode;
      SimpleNode* superclassNode;

      UInt numMemberFunctions = 0;
      UInt numSuperclasses = 0;

      tl_assert(t->typeName);

      FJALAR_DPRINTF("  typeName: %s (%p)\n", t->typeName, t);

      tl_assert((D_STRUCT_CLASS == t->decType) ||
                (D_UNION == t->decType));

      // Rep. check member variables (if there are any):
      if (t->aggType->memberVarList) {
        for (n = t->aggType->memberVarList->first;
             n != 0;
             n = n->next) {
          VariableEntry* curMember = n->var;

          FJALAR_DPRINTF(" checking member %s for %s\n",
                      curMember->name, t->typeName);

          // Specific checks for member variables:
          tl_assert(IS_MEMBER_VAR(curMember));
          tl_assert(0 == curMember->byteOffset);

          // For a struct, check that data_member_location is greater
          // than the one of the previous member variable.  Notice that
          // data_member_location can be 0.
          if (D_STRUCT_CLASS == t->decType) {
            // We don't check bit-fields as the compiler may
            // allocate them to a previous location.
            // (We currently don't support bit-fields.)
            // FJALAR_DPRINTF("addr: %lx, bitfield?: %d %d %d\n", curMember->memberVar->data_member_location,
            //     curMember->memberVar->internalByteSize,
            //     curMember->memberVar->internalBitOffset,
            //     curMember->memberVar->internalBitSize);
            if ((curMember->memberVar->internalByteSize == 0) && (curMember->memberVar->data_member_location != 0))
              tl_assert(curMember->memberVar->data_member_location > prev_data_member_location);
            prev_data_member_location = curMember->memberVar->data_member_location;
          }
          // For a union, all offsets should be 0
          else if (D_UNION == t->decType) {
            tl_assert(0 == curMember->memberVar->data_member_location);
          }

          tl_assert(curMember->memberVar->structParentType == t);

          repCheckOneVariable(curMember);

          numMemberVars++;
        }
        tl_assert(numMemberVars == t->aggType->memberVarList->numVars);
      }

      // Rep. check static member variables (if there are any):
      if (t->aggType->staticMemberVarList) {
        unsigned int numStaticMemberVars = 0;
        VarNode* node;

        for (node = t->aggType->staticMemberVarList->first;
             node != 0;
             node = node->next) {
          VariableEntry* curMember = node->var;

          FJALAR_DPRINTF(" checking STATIC member %s for %s\n",
                      curMember->name, t->typeName);

          // Specific checks for static member variables:
          tl_assert(IS_MEMBER_VAR(curMember));
          tl_assert(0 == curMember->byteOffset);
          tl_assert(0 == curMember->memberVar->data_member_location);
          tl_assert(IS_GLOBAL_VAR(curMember));
          tl_assert(curMember->memberVar->structParentType == t);

          repCheckOneVariable(curMember);

          numStaticMemberVars++;
        }
        tl_assert(numStaticMemberVars == t->aggType->staticMemberVarList->numVars);
      }

      // Rep. check member functions:
      if (t->aggType->memberFunctionList) {
        for (memberFunctionNode = t->aggType->memberFunctionList->first;
             memberFunctionNode != NULL;
             memberFunctionNode = memberFunctionNode->next) {


/*           if(((FunctionEntry*)(memberFunctionNode->elt))->name) { */
/*             FJALAR_DPRINTF("\n checking member Function %s\n", */
/*                            ((FunctionEntry*)(memberFunctionNode->elt))->name); */
/*           } */

          FJALAR_DPRINTF(" parent class is %p\n",
                         ((FunctionEntry*)(memberFunctionNode->elt))->parentClass);

          if(((FunctionEntry*)(memberFunctionNode->elt))->parentClass) {
            FJALAR_DPRINTF(" type is %s\n", ((FunctionEntry*)(memberFunctionNode->elt))->parentClass->typeName);
          }

          // Make sure that all of their parentClass fields point to t:

          //RUDD TEMP
          //          tl_assert(((FunctionEntry*)(memberFunctionNode->elt))->parentClass == t);
          numMemberFunctions++;
        }
        tl_assert(numMemberFunctions == t->aggType->memberFunctionList->numElts);
      }

      // Rep. check superclasses
      if (t->aggType->superclassList) {
        for (superclassNode = t->aggType->superclassList->first;
             superclassNode != NULL;
             superclassNode = superclassNode->next) {
          // Make sure that all Superclass entries have a className and
          // it matches the className of the corresponding TypeEntry:
          Superclass* curSuper = (Superclass*)superclassNode->elt;
          tl_assert(curSuper->className);
          tl_assert(curSuper->class);
          tl_assert(0 == VG_(strcmp)(curSuper->className, curSuper->class->typeName));
          FJALAR_DPRINTF("  curSuper->className: %s, inheritance: %u\n",
                      curSuper->className, curSuper->inheritance);
          numSuperclasses++;
        }
        tl_assert(numSuperclasses == t->aggType->superclassList->numElts);
      }
    }
  }

  deleteTypeIterator(typeIt);

  FJALAR_DPRINTF("DONE\n");
}

// Checks rep. invariants for a VariableEntry (only performs general
// checks - additional checks are needed by the calling function if
// you want to really enforce stringent requirements)
static void repCheckOneVariable(VariableEntry* var) {
  tl_assert(var);

  // These properties should hold for all global vars:
  if (IS_GLOBAL_VAR(var)) {
    Addr global_loc;
    tl_assert(0 == var->byteOffset);

    // Not true for C++ static member variables
    if (!IS_MEMBER_VAR(var)) {
      tl_assert(var->globalVar->fileName);
    }

    global_loc = var->globalVar->globalLocation;
    FJALAR_DPRINTF(" --- checking var (t: %s) (%p): %s, globalLoc: %p\n",
                   (IS_MEMBER_VAR(var) && var->memberVar->structParentType) ?
                   var->memberVar->structParentType->typeName : "no parent",
                   var, var->name, (void *)global_loc);


    if (global_loc) {
      if (!addressIsGlobal(global_loc) &&
          (global_loc < 0x08048000 || global_loc > 0x8100000)) {
        // (comment added 2005)  
        /* addressIsGlobal() works fine for the normal case of
           dynamically linked programs, but if you statically link
           with a debugging libc, it will contain some weird variables
           whose location is in other sections. The extra numeric
           comparison is a fallback hack for that case. */
        printf("Address 0x%08x doesn't look like a global\n",
                (unsigned int)var->globalVar->globalLocation);
        printf("Data section is 0x%08x to 0x%08x\n",
                data_section_addr, data_section_addr + data_section_size);
        printf("BSS section is 0x%08x to 0x%08x\n",
                bss_section_addr, bss_section_addr + bss_section_size);
        printf("ROData section is 0x%08x to 0x%08x\n",
                rodata_section_addr,
                rodata_section_addr + rodata_section_size);
        printf("Relocated ROData section is 0x%08x to 0x%08x\n",
                relrodata_section_addr,
                relrodata_section_addr + relrodata_section_size);
        tl_assert(0);
      }
    }
  }

  // These properties hold for all variables:
  tl_assert(var->name);

  tl_assert(var->varType);

  if (IS_STATIC_ARRAY_VAR(var)) {
    tl_assert(var->staticArr->numDimensions > 0);
    tl_assert(var->staticArr->upperBounds);
  }

  if (IS_STRING(var)) {
    tl_assert(D_CHAR == var->varType->decType);
    tl_assert(var->ptrLevels > 0);
  }

  if(IS_MEMBER_VAR(var)) {
      // a static member var won't have a parent  (markro)
      if (!IS_GLOBAL_VAR(var)) {
          tl_assert(var->memberVar->structParentType);
      }
  }

  // C++ reference vars should never have more than 1 level of
  // reference '&' right?
  tl_assert((var->referenceLevels == 0) ||
            (var->referenceLevels == 1));

  FJALAR_DPRINTF(" --- DONE checking var (t: %s) (%p): %s, globalLoc: %p\n",
                 IS_MEMBER_VAR(var) && var->memberVar->structParentType ?
                 var->memberVar->structParentType->typeName : "no parent",
                 VoidPtr(var),
                 var->name,
                 VoidPtr(IS_GLOBAL_VAR(var) && var->globalVar->globalLocation));
}


static int entry_is_valid_function(dwarf_entry *entry) {
  if (tag_is_function(entry->tag_name)) {
    function* funcPtr = (function*)(entry->entry_ptr);
    if (funcPtr->name != 0 &&
        funcPtr->start_pc &&
        (!funcPtr->is_declaration) &&
        (!ignore_function_with_name(funcPtr->name))) {
      return 1;
    } else {

      FJALAR_DPRINTF("Skipping invalid-looking function %s\n", funcPtr->name);

      return 0;
    }
  }
  return 0;
}

// DEPRECATED: No need for hash function for an integer
//unsigned int hashGlobalVarAddr(unsigned long ID) {
//  return ((unsigned int)ID) % geninitialnumbins;
//}


// Pre: e->tag_name == DW_TAG_variable
// functionStartPC identifies the function that this static
// variable was declared within
static void extractOneGlobalVariable(dwarf_entry* e, unsigned long functionStartPC)
{
  variable* variablePtr = 0;
  dwarf_entry* typePtr = 0;

  FJALAR_DPRINTF("ENTER extractOneGlobalVariable(%p)\n", e);


  if (e == NULL || !tag_is_variable(e->tag_name)) {
    printf( "Error, global variable information struct is null or belongs to the incorrect type\n");
    my_abort();
  }

  variablePtr = (variable*)(e->entry_ptr);
  typePtr = variablePtr->type_ptr;
  

  extractOneVariable(&globalVars,
                     typePtr,
                     variablePtr->name,
                     findFilenameForEntry(e),
                     variablePtr->couldBeGlobalVar,
                     variablePtr->is_external,
                     variablePtr->is_const,
                     variablePtr->const_value,
                     variablePtr->globalVarAddr,
                     functionStartPC,
                     variablePtr->isStaticMemberVar,
                     0,0,0,0,0,0,0,
                     getDeclaredFile(e->comp_unit, variablePtr->decl_file));

  FJALAR_DPRINTF("EXIT  extractOneGlobalVariable(%p)\n", e);
}

// Initializes the global variables list (globalVars) and fills it up
// with global variable entries from dwarf_entry_array.

// Note: If two or more source files include the same header file
// which has global declarations, then the entry for these global
// variables will appear multiple times, once for every source
// file. However, these multiple copies of global variable entries all
// have the SAME address location and thus are the exact same
// thing. We must discard these duplicates.  Remember, we must key in
// on both the variable names and the address locations for removing
// duplicates.
static void initializeGlobalVarsList(void)
{
  UInt i;
  dwarf_entry* cur_entry = 0;

  // Create a hashtable with keys = {unsigned long (globalVarAddr), non-zero}
  //                   and values = {string which is the global variable name}
  struct genhashtable* GlobalVarsTable =
    genallocatehashtable(0, (int (*)(void *,void *)) &equivalentIDs);

  FJALAR_DPRINTF("ENTER initializeGlobalVarsList - %d dwarf entries\n",
                 (int)dwarf_entry_array_size);

  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_variable(cur_entry->tag_name)) {
      variable* variable_ptr = (variable*)(cur_entry->entry_ptr);

      FJALAR_DPRINTF("\t[initializeGlobalVarsList] lvl %d, ID %lx, %s 0x%x, spec_ID: 0x%lx, static: %u, dec: %d, const: %d global: %d\n",
                     cur_entry->level,
                     cur_entry->ID,
                     variable_ptr->name,
                     (unsigned int)variable_ptr->globalVarAddr,
                     variable_ptr->specification_ID,
                     (unsigned int)variable_ptr->isStaticMemberVar,
                     variable_ptr->is_declaration_or_artificial,
                     variable_ptr->is_const,
                     variable_ptr->couldBeGlobalVar);

      FJALAR_DPRINTF("\t[initializeGlobalVarsList] compile_unit: %p\n", cur_entry->comp_unit);

      // IGNORE variables with is_declaration_or_artificial or
      // specification_ID active because these are empty shells!

      // ABOVE is no longer true.  GCC 4.7.x (perhaps earlier?) now
      // represents a static member variable with a DW_TAG_member at the
      // declation and a DW_TAG_variable at the definition.  This entry
      // has a DW_AT_specification that points back to the DW_TAG_member. 
      // We want to treat static members kind of like globals so we will
      // process them here.          (markro)
      if ((variable_ptr->couldBeGlobalVar &&
          variable_ptr->globalVarAddr &&
           (!variable_ptr->is_declaration_or_artificial)) ||
          (variable_ptr->is_const && !variable_ptr->is_declaration_or_artificial)) {
        char* existingName;

        if (variable_ptr->is_const) {
          variable_ptr->couldBeGlobalVar = True;
        }

        if (!variable_ptr->name) {
          FJALAR_DPRINTF("\t[initializeGlobalVarsList] Skipping weird unnamed global variable ID#%x - addr: %x\n",
                       (unsigned int)cur_entry->ID, (unsigned int)variable_ptr->globalVarAddr);
          continue;
        }
        else if (VG_STREQ(variable_ptr->name, "_IO_stdin_used")) {

          /* Hide from our users this silly glibc feature:
          [http://www.mail-archive.com/bug-glibc@gnu.org/msg02830.html]
          There is a symbol, _IO_stdin_used, placed into the
          executable program, *only* when a program compiles against
          glibc that has support for pre-2.1 libio.  Inside a
          fully-backward-compatible glibc, there is a routine that
          "looks into an executable" and determines if that symbol is
          present.  If not, that routine switches std{in,out,err} to
          point to old, pre-2.1 libio structures, assuming that this
          is a very old program compiled against old glibc, so that
          all stdio routines will work correctly. */

          FJALAR_DPRINTF("\t[initializeGlobalVarsList] Skipping silly glibc feature - %s\n",
                         variable_ptr->name);
          continue;
        }

        // This is the part where we do not add duplicates. We first
        // look up to see whether variable_ptr->globalVarAddr is
        // non-null and in GlobalVarsTable. If it is already in the
        // table, we get the value for that entry and compare it with
        // the name of variable_ptr. If both globalVarAddr and name
        // match, then we have a duplicate entry so we don't add the
        // new entry to the globalVars list. However, if the variable
        // is not yet in GlobalVarsTable, then we add it to the table
        // and proceed with adding it to the globalVars list.
        existingName = 0;
        if ((0 != variable_ptr->globalVarAddr) &&
              ((existingName =
                gengettable(GlobalVarsTable, (void*)variable_ptr->globalVarAddr)))) {
            if VG_STREQ(variable_ptr->name, existingName) {
                FJALAR_DPRINTF("\t[initializeGlobalVarsList] DUPLICATE! - %s\n", variable_ptr->name);
                continue;
            }
        } else {
            genputtable(GlobalVarsTable,
                        (void*)variable_ptr->globalVarAddr, // key    (unsigned long)
                        (void*)variable_ptr->name);         // value  (char*)
        }

        // If a variable is a global variable in C or in C++ without
        // an enclosing namespace (older g++ versions do not put
        // DW_TAG_namespace tags in the debug. info.), then its
        // dwarf_entry.level is 1 because it is not nested within
        // anything.  If dwarf_entry.level > 1, that means that this
        // is either a static global variable declared within a
        // function or a C++ global variable enclosed inside of a
        // namespace (generated by g++ 4.0) so we should include
        // either the namespace or function name along with the
        // filename in front of the variable name:
        if (cur_entry->level > 1) {
          // (comment added 2005)  
          // TODO: Support for different namespaces in the future.
          namespace_type* enclosing_namespace = findNamespaceForVariableEntry(cur_entry);
          unsigned long startPC =
            enclosing_namespace ? 0 : findFunctionStartPCForVariableEntry(cur_entry);

          // Constant local variables would satisfy the above conditions, let's ignore
          // them.
          if((startPC != 0) && (variable_ptr->is_const)) {
            FJALAR_DPRINTF("\t[initializeGlobalVarsList] Constant variable with an enclosing function - NOT a global\n");
            continue;
          }
          extractOneGlobalVariable(cur_entry, startPC);
        } else {
          extractOneGlobalVariable(cur_entry, 0);
        }
      }
    }
  }

  genfreehashtable(GlobalVarsTable);
  FJALAR_DPRINTF("EXIT  initializeGlobalVarsList\n");
}

// Initialize the names of unnamed structs so that we can have
// something to uniquely identify them with:
//
// For unnamed structs/unions/enums, we should just munge the
// name from the ID field so that we have something
// to use to identify this struct
// We will name it "unnamed_0x$ID" where $ID
// is the ID field in hex.
static void createNamesForUnnamedDwarfEntries(void)
{
  unsigned long i;
  dwarf_entry* cur_entry = 0;

  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_collection_type(cur_entry->tag_name)) {
      collection_type* collectionPtr = (collection_type*)(cur_entry->entry_ptr);
      if (!collectionPtr->is_declaration &&
          !collectionPtr->name) {
        //        printf("%s (%u)\n", collectionPtr->name, cur_entry->ID);

        // The maximum size is 10 + 8 + 1 = 19 10 for "unnamed_0x", 8
        // for maximum size for cur_entry->ID, and 1 for
        // null-terminator
        char* fake_name = VG_(calloc)("generate_fjalar_entries.c: createNamesForUnnamedDwarfEntries", 19, sizeof(*fake_name));
        sprintf(fake_name, "unnamed_0x%lx", cur_entry->ID);
        collectionPtr->name = fake_name;
      }
    }
  }
}

static int hashGlobalConstant(VariableEntry* varPtr) { 
  return  hashString(varPtr->declaredIn) + hashString(varPtr->name);
}
  

static int equivalentGlobalConstants(VariableEntry* varPtr1, VariableEntry* varPtr2) {
  return VG_STREQ(varPtr1->declaredIn, varPtr2->declaredIn) && VG_STREQ(varPtr1->name, varPtr2->name);
}

// Pre: initializeFunctionTable() and initializeGlobalVarsList() MUST
// BE RUN before running this function.
// Iterates through globalVars and generates a fully-qualified name
// for each global variable so that they are not ambiguous.
// (Also demangles C++ names if necessary.)
static void updateAllGlobalVariableNames(void) {
  char* globalName = 0;
  const char *loc_part; /* Part of the name to specify where the variable came from
                     (doesn't exist in the real language) */
  char *p;

  VarNode* curNode;
  VariableEntry* curVar;
  
  struct genhashtable* constGlobalHash = genallocatehashtable((unsigned int (*)(void *)) &hashGlobalConstant,
                                                              (int (*)(void *,void *)) &equivalentGlobalConstants);

  // We'll go through the entire globals list, and remove any global constant
  // VariableEntries that are a duplicate of one we've seen earlier (where duplicate
  // is defined as being declared in the same file and having the same name) and change
  // the first instance's file name to be the file it was declared in. This could
  // be extended to merge all constant variables with the same name and value
  // or even all constant variables with the same value relatively easily, but I'm
  // not sure how useful that would be - rudd
  if(fjalar_merge_constants) {
    VarNode* lastNode = NULL;
    for (curNode = globalVars.first;
         curNode != NULL;
         curNode = curNode->next) {
      curVar = curNode->var;      

      tl_assert(IS_GLOBAL_VAR(curVar));      
      if(curVar->isConstant && curVar->declaredIn) {

        if(gencontains(constGlobalHash, curVar)) {
          FJALAR_DPRINTF("[updateAllGlobalVariableNames] Ignoring duplicate variable entry %s (%p)\n",
                         curVar->name, curVar);
          lastNode->next = curNode->next;

          if(curNode->next) {
            curNode->next->prev = lastNode;
          }

          VG_(free)(curNode);
          curNode = lastNode;
          destroyVariableEntry(curVar);
          globalVars.numVars--;
          continue;
        } else {
          genputtable(constGlobalHash, curVar, curVar);
          if(curVar->declaredIn) {
            curVar->globalVar->fileName = curVar->declaredIn;
          }
        }      
      }
      lastNode = curNode;          
    }
  }

  for (curNode = globalVars.first;
       curNode != NULL;
       curNode = curNode->next) {
    FunctionEntry* var_func = 0;
    char* name_to_use = 0;

    curVar = curNode->var;
    tl_assert(IS_GLOBAL_VAR(curVar));      

    // Do not bother to make unique names for C++ static member
    // variables that are in the globalVars list because they should
    // already have unique names since their class name is appended to
    // the front of their names: e.g. "Stack::publicNumLinksCreated"
    if (IS_MEMBER_VAR(curVar)) {
      continue;
    }

    // For file static global variables, we are going to append the
    // filename in front of it
    if (curVar->globalVar->isExternal) {
      /* A leading slash indicates a true global */
      loc_part = "";
    }
    else {
      loc_part = curVar->globalVar->fileName;
    }

    /* We want to print static variables in subdir/filename.c
       as "subdir/filename_c/static_var for globally-declared static variables
       or as "subdir/filename_c@function_name/static_var for static vars declared within functions
    */
    tl_assert(curVar->name);

    if (curVar->globalVar->functionStartPC) {
      // Try to find a function entry with that start PC:
      var_func = (FunctionEntry*)gengettable(FunctionTable,
                                             (void*)curVar->globalVar->functionStartPC);

      tl_assert(var_func);

      // Use the demangled name of the function (if available) to
      // disambiguate in the presence of overloading:
      name_to_use = var_func->demangled_name ?
        var_func->demangled_name : var_func->name;

      tl_assert(name_to_use);

      globalName = VG_(calloc)("generate_fjalar_entries.c: updateAllGlobalVariableNames.1", VG_(strlen)(loc_part) + 1 +
                               VG_(strlen)(name_to_use) + 1 + 1 +
                               VG_(strlen)(curVar->name) + 1, sizeof(*globalName));
    }
    else {
      globalName = VG_(calloc)("generate_fjalar_entries.c: updateAllGlobalVariableNames.2", VG_(strlen)(loc_part) + 1 + 1 +
                               VG_(strlen)(curVar->name) + 1, sizeof(*globalName));
    }

    VG_(strcpy)(globalName, loc_part);
    for (p = globalName; *p; p++) {
      if (!isalpha(*p) && !isdigit(*p) && *p != '/' && *p != '_')
        *p = '_';
    }

    if (curVar->globalVar->functionStartPC) {
      VG_(strcat)(globalName, "@");
      VG_(strcat)(globalName, name_to_use);

      for (p = globalName; *p; p++) {
        if (!isalpha(*p) && !isdigit(*p) && *p != '/' && *p != '_' && *p != '@')
          *p = '_';
      }
    }

    VG_(strcat)(globalName, "/");
    VG_(strcat)(globalName, curVar->name);

    // Assign curVar->name to the newly-formed name:
    curVar->name = globalName;
  }
}


// Utility function for prepending class/file name
static char* PrependClass(const char* class, const char* func, int func_name_len) {
  char *buf = NULL, *p = NULL;

  /* We want to print static_fn in subdir/filename.c
     as "subdir/filename.c.static_fn() */
  buf = VG_(malloc)("genereate_fjalar_entries.c: prependClass.1", VG_(strlen)(class) + 1 +
                    func_name_len + 3); // 3 for possible trailing parens
  VG_(strcpy)(buf, class);
  for (p = buf; *p; p++) {
    if (!isalpha(*p) && !isdigit(*p) && *p != '.' && *p != '/'
        && *p != '_')
      *p = '_';
  }
  VG_(strcat)(buf, ".");
  VG_(strcat)(buf, func);
  return buf;
}

// Initializes all the fully-unique Fjalar names and trace_vars_tree
// for all functions in FunctionTable:
// Pre: If we are using the --var-list-file= option, the var-list file
// must have already been processed by the time this function runs
static void initFunctionFjalarNames(void) {
  FuncIterator* funcIt = newFuncIterator();

  // FJALAR_DPRINTF("ENTER initFunctionFjalarNames\n");

  while (hasNextFunc(funcIt)) {
    FunctionEntry* cur_entry = nextFunc(funcIt);

    const char *the_class;
    char *buf;

    char* name_to_use;
    int name_len, fjalar_name_len;

    tl_assert(cur_entry);

    // Use the demangled name if there is one (sometimes in C++), or
    // just the regular name if there isn't one (C):
    name_to_use = (cur_entry->demangled_name ?
                   cur_entry->demangled_name :
                   cur_entry->name);

    name_len = VG_(strlen)(name_to_use);
    tl_assert(name_len);

    // FJALAR_DPRINTF("original name: %s\n", name_to_use);

    // What should we use as a prefix for function names?
    // Global functions should print as: ..main()
    // File-static functions should print as: dirname/filename.c.staticFunction()
    // C++ member functions should print as: className.memberFunction()
    if (cur_entry->parentClass) {
      the_class = cur_entry->parentClass->typeName;
      // If there is demangled name like: "Stack::Link::initialize(char*, Stack::Link*)",
      // we want to strip off all but "initialize(char*, Stack::Link*)" and then tack
      // on the class name to that to form "Link.initialize(char*, Stack::Link*)"
      // in order to make it look cleaner:
      if (cur_entry->demangled_name) {
        name_to_use = getRawCppFunctionName(cur_entry->demangled_name);
      }
    }
    else if (cur_entry->isExternal) {
      the_class = ".";
    }
    else {
      the_class = cur_entry->filename;
    }

    tl_assert(the_class);

    buf = PrependClass(the_class, name_to_use, name_len);
    fjalar_name_len = VG_(strlen)(buf);

    // If we didnt need to demangle a C++ name, then we just have a
    // plain C name without the last character being a right paren.
    // If that's the case, then tack on some parens:
    if (!cur_entry->demangled_name) {
      VG_(strcat)(buf, "()");
    }

    // FJALAR_DPRINTF("modified name: %s\n", buf);

    // Rudd 2.0 - There seems to be an issue in regards to C++ files
    // having duplicate function names in the debugging info. I haven't
    // verified as to why this happens, but this issue was present in the
    // first large C++ program I tested.

    // This will attempt to disambiguate duplicate function names
    // my prepending the filename to them. (It may also be reasonable
    // to just throw out the duplicate name, because it's very unlikely
    // that a program would have 2 identically named non-static functinos
    // with different semantics, but let's just be safe)

    if(gencontains(FuncNameTable, buf)) {
      char* bufOld;
      char* bufNew;
      FunctionEntry* collided_func = gengettable(FuncNameTable, buf);
      tl_assert(collided_func);

      // Prepend filename to new entry
      the_class = cur_entry->filename;
      bufNew = PrependClass(the_class, buf, fjalar_name_len);

      // Prepend filename to old entry
      the_class = collided_func->filename;
      bufOld = PrependClass(the_class, buf, fjalar_name_len);

      // Check if entries are the same. If they are, clean up and continue
      if(!VG_(strcmp)(bufOld, bufNew)) {
        genfreekey(FunctionTable_by_entryPC, (void *)cur_entry->entryPC);
        genfreekey(FunctionTable, (void *)cur_entry->startPC);

        VG_(free)(buf);
        VG_(free)(bufOld);
        VG_(free)(bufNew);

        continue;
      }

      VG_(free)(collided_func->fjalar_name);
      collided_func->fjalar_name = bufOld;
      VG_(free)(buf);
      buf = bufNew;
    }
      genputtable(FuncNameTable, buf, cur_entry);


    // Woohoo, we have constructed a Fjalar name!
    cur_entry->fjalar_name = buf;

    // See if we are interested in tracing variables for this file,
    // and if so, we must initialize cur_entry->trace_vars_tree
    // appropriately.  We cannot initialize it any earlier because we
    // need to use the Fjalar name of the function to identify its
    // entry in vars_tree, and this is the earliest point where the
    // Fjalar name is guaranteed to be initialized.

    // Note that we must read in and process the var-list-file BEFORE
    // calling this function:
    if (fjalar_trace_vars_filename &&
        (!cur_entry->trace_vars_tree_already_initialized)) {
      extern FunctionTree* vars_tree;

      FunctionTree** foundFuncTree = 0;
      FunctionTree searchFuncTree;
      searchFuncTree.function_fjalar_name = cur_entry->fjalar_name;
      searchFuncTree.function_variables_tree = 0;

      if ((foundFuncTree =
           (FunctionTree**)tfind((void*)&searchFuncTree,
                                 (void**)&vars_tree,
                                 compareFunctionTrees))) {
        cur_entry->trace_vars_tree = (*foundFuncTree)->function_variables_tree;
        FJALAR_DPRINTF("FOUND FOUND FOUND!!! - %s\n",
                       (*foundFuncTree)->function_fjalar_name);
      }
      else {
        cur_entry->trace_vars_tree = 0;
      }
    }


    // No matter what, we've ran it once for this function so
    // trace_vars_tree has been initialized
    cur_entry->trace_vars_tree_already_initialized = 1;

    // Now that we have fjalar_trace_vars, we can identiy the globals to
    // track for the function. We just walk the trace_vars_tree to extract
    // the globals. We union this list with the globalFunctionTree list

    // At somepoint we may want to consider not copying the globalFunctionTree
    // for function that has additional globals to track. In practice I don't
    // think this will be an issue because the number of interesting globals
    // for any particular function is small compared to the total number of
    // globals.

    cur_entry->trace_global_vars_tree = 0;

    if (fjalar_trace_vars_filename &&
        (!cur_entry->trace_global_vars_tree_already_initialized)){
      extern FunctionTree * globalFunctionTree;

      if (cur_entry->trace_vars_tree != 0){
        struct tree_iter_t *it = titer((void *) cur_entry->trace_vars_tree);
        while (titer_hasnext(it)){
          char *var = (char *) titer_next(it);
          
          if (var[0] == '/'){ //it's a global variable
            char *newString = VG_(strdup)("generate_fjalar_entries.c", var);
            tsearch((void *) newString,
                    (void **) &(cur_entry->trace_global_vars_tree),
                    compareStrings);
          }        
        }
        titer_destroy(it);
      }
     
      // Only copy the globalFunctionTree if there were additions from trace_vars_tree
      // If there weren't additions, we'll just use globalFunctionTree during traversal
      if (globalFunctionTree != 0 && cur_entry->trace_global_vars_tree){
        struct tree_iter_t *it = titer((void *) globalFunctionTree->function_variables_tree);
        while (titer_hasnext(it)){
          char *var = (char *) titer_next(it);
          char *newString = VG_(strdup)("generate_fjalar_entries.c", var);
          tsearch((void *) newString,
                  (void **) &(cur_entry->trace_global_vars_tree),
                  compareStrings);
        }
        titer_destroy(it);
      }
               
      //We also remove all globals from the normal trace_vars_tree to save time
      //when checking formal parameters against it later
      if (cur_entry->trace_global_vars_tree && cur_entry->trace_vars_tree){
        struct tree_iter_t *it = titer((void *) cur_entry->trace_global_vars_tree);
        while (titer_hasnext(it)){
          char *var = (char *) titer_next(it);
          tdelete(var,
                  (void **) &(cur_entry->trace_vars_tree),
                  compareStrings);
        }
        titer_destroy(it);
      }
    }
    
    cur_entry->trace_global_vars_tree_already_initialized = 1;
  }      
  deleteFuncIterator(funcIt);

  // FJALAR_DPRINTF("EXIT  initFunctionFjalarNames\n");
}

// (comment added 2005)  
// TODO: This will leak memory if called more than once per program
// execution since the entries in FunctionTable are not being properly
// freed.  However, during normal execution, this should only be
// called once.

// Note: This does NOT initialize the fjalar_name fields of the
// functions in FunctionTable.  It is up to initFunctionFjalarNames()
// to do that after all the smoke has cleared.
void initializeFunctionTable(void)
{
  unsigned long i;
  dwarf_entry* cur_entry = 0;
  FunctionEntry* cur_func_entry = 0;
  unsigned long num_functions_added = 0;

  FJALAR_DPRINTF("ENTER initializeFunctionTable\n");

  FunctionTable =
    genallocatehashtable(0,
                         (int (*)(void *,void *)) &equivalentIDs);

  FunctionTable_by_endOfBb =
    genallocatehashtable(0,
                         (int (*)(void *,void *)) &equivalentIDs);

  FunctionTable_by_entryPC =
    genallocatehashtable(0,
                         (int (*)(void *,void *)) &equivalentIDs);

  FuncNameTable =
    genallocatehashtable((unsigned int (*)(void *)) &hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  for (i = 0; i < dwarf_entry_array_size; i++)
    {
      // FJALAR_DPRINTF("i: %lu\n", i);
      cur_entry = &dwarf_entry_array[i];
      // Ignore invalid functions and DUPLICATE function entries
      // with the same start_pc (only test if there is start_pc)
      if (entry_is_valid_function(cur_entry) &&
          ((((function*)cur_entry->entry_ptr)->start_pc) &&
           !gencontains(FunctionTable,
                        (void*)(((function*)cur_entry->entry_ptr)->start_pc))))
        {
          function* dwarfFunctionPtr = (function*)(cur_entry->entry_ptr);
          // This is non-null only if we have successfully demangled a
          // C++ name:
          char* demangled_name = 0;

          // Remember to use the tool's constructor,
          // constructFunctionEntry(), in order to properly support
          // sub-classing:
          cur_func_entry = constructFunctionEntry();
          FJALAR_DPRINTF("Function at %p\n", cur_func_entry);

          FJALAR_DPRINTF("Adding function %s\n", dwarfFunctionPtr->name);


          cur_func_entry->name = dwarfFunctionPtr->name;
          cur_func_entry->mangled_name = dwarfFunctionPtr->mangled_name;
          cur_func_entry->filename = dwarfFunctionPtr->filename;

          switch (dwarfFunctionPtr->accessibility) {
          case DW_ACCESS_private:
            cur_func_entry->visibility = PRIVATE_VISIBILITY;
            break;
          case DW_ACCESS_protected:
            cur_func_entry->visibility = PROTECTED_VISIBILITY;
            break;
          case DW_ACCESS_public:
          default:
            cur_func_entry->visibility = PUBLIC_VISIBILITY;
          }

          cur_func_entry->startPC = dwarfFunctionPtr->start_pc;
          cur_func_entry->cuBase = dwarfFunctionPtr->comp_pc;
          cur_func_entry->endPC = dwarfFunctionPtr->end_pc;

          FJALAR_DPRINTF("Frame base exp is: %u + %ld\n", dwarfFunctionPtr->frame_base_expression,
                                                         dwarfFunctionPtr->frame_base_offset);
          cur_func_entry->frame_base_atom = dwarfFunctionPtr->frame_base_expression;
          cur_func_entry->frame_base_offset = dwarfFunctionPtr->frame_base_offset;


          cur_func_entry->isExternal = dwarfFunctionPtr->is_external;

          FJALAR_DPRINTF("cur_func_entry->startPC: %p (%s %s)\n",
                         (void *)cur_func_entry->startPC,
                         cur_func_entry->name,
                         cur_func_entry->mangled_name);
          FJALAR_DPRINTF("cur_func_entry->cuBase: %p\n",
                         (void *)cur_func_entry->cuBase);

          // This seems to happen with class constructors.  If there
          // is NO C++ mangled name but there is a startPC, then
          // attempt to look up the C++ mangled name from the symbol
          // table (FunctionSymbolTable):
          if (!cur_func_entry->mangled_name &&
              cur_func_entry->startPC) {
            char* maybe_mangled_name = (char*)gengettable(ReverseFunctionSymbolTable,
                                                          (void*)cur_func_entry->startPC);

            // If it doesn't match the regular ole' name, then we may
            // have something interesting:
            if (!VG_STREQ(maybe_mangled_name, cur_func_entry->name)) {
              FJALAR_DPRINTF("  maybe_mangled_name: %s\n", maybe_mangled_name);
              cur_func_entry->mangled_name = maybe_mangled_name;
            }
          }

          // If there is a C++ mangled name, then call Valgrind core
          // to try to demangle the name (remember the demangled name
          // is malloc'ed):
          if (cur_func_entry->mangled_name) {
            demangled_name = cplus_demangle_v3(cur_func_entry->mangled_name, DMGL_PARAMS | DMGL_ANSI);
            if (demangled_name) {
              FJALAR_DPRINTF("demangling: %s\n", demangled_name);
              // Set the demangled_name of the function to be the
              // demangled name:
              cur_func_entry->demangled_name = demangled_name;
            }
          }

          // Extract all formal parameter variables
          extractFormalParameterVars(cur_func_entry, dwarfFunctionPtr);

          // Extract all local array variables
          extractLocalArrayAndStructVariables(cur_func_entry, dwarfFunctionPtr);

          // Extract return variable
          extractReturnVar(cur_func_entry, dwarfFunctionPtr);

          // Add to FunctionTable
          genputtable(FunctionTable,
                      (void*)cur_func_entry->startPC, // key    (unsigned long)
                      (void*)cur_func_entry);         // value  (FunctionEntry*)

          // FJALAR_DPRINTF("  call gencontains %p %p\n", next_line_addr, (void*)cur_func_entry->startPC);

          if (gencontains(next_line_addr, (void*)cur_func_entry->startPC)) {
            cur_func_entry->entryPC = (Addr)
              gengettable(next_line_addr, (void*)cur_func_entry->startPC);
            FJALAR_DPRINTF("Entering %s at 0x%08x instead of 0x%08x\n",
                           cur_func_entry->name, (unsigned int)cur_func_entry->entryPC,
                           (unsigned int)cur_func_entry->startPC);
            /* Leave DWARF offsets alone if the exist, since we should
               be properly placed to use them. */
            verifyStackParamWordAlignment(cur_func_entry, 0);
          } else {
            // Make one more pass-through to make sure that byteOffsets
            // are correct for the word-aligned stack!
            // We must do this AFTER extracting the return variable.
            // Should only be needed when we weren't able to skip the
            // prolog, and so can't rely on the DWARF information to
            // have the correct parameter locations.
            cur_func_entry->entryPC = cur_func_entry->startPC;
            FJALAR_DPRINTF("Entering %s at 0x%08x \n",
                           cur_func_entry->name, (unsigned int)cur_func_entry->entryPC);
            verifyStackParamWordAlignment(cur_func_entry, 1);
          }
          genputtable(FunctionTable_by_entryPC,
                      (void*)cur_func_entry->entryPC,
                      (void*)cur_func_entry);

          cur_func_entry->formalParamStackByteSize
            = determineFormalParametersStackByteSize(cur_func_entry);

          cur_func_entry->formalParamLowerStackByteSize
            = determineFormalParametersLowerStackByteSize(cur_func_entry);

          num_functions_added++;
        }
    }

  if (!num_functions_added) {
    printf( "\nError - No functions were found, probably due to a lack of debugging information.\n");
    printf( "Did you compile your program with DWARF2 debugging info?  The option is -gdwarf-2 on gcc.\n");
    my_abort();
  }

  FJALAR_DPRINTF("EXIT  initializeFunctionTable\n");
}


// Extracts dummy modifier type information from modifierPtr
// returning the new stripped dwarf entry
static dwarf_entry* extractModifierType(modifier_type* modifierPtr)
{
  return modifierPtr->target_ptr;
}

// Extracts array type by modifying varPtr
// varListPtr and filling in the isStaticArray, numDimensions, and upperBounds
// fields within it
// Modifies: varPtr
// Returns: Pointer to the type of the array
// (This functions like an extended version of extractPointerType)
static dwarf_entry* extractArrayType(VariableEntry* varPtr, array_type* arrayPtr)
{
  int arrayDims = 0;
  int i = 0;
  arrayDims = arrayPtr->num_subrange_entries;

  varPtr->staticArr = VG_(calloc)("generate_fjalar_entries.c: extractArrayType.1", 1, sizeof(*varPtr->staticArr));
  varPtr->staticArr->numDimensions = arrayDims;
  varPtr->staticArr->upperBounds = VG_(calloc)("generate_fjalar_entries.c: extractArrayType.2", arrayDims,
                                               sizeof(*(varPtr->staticArr->upperBounds)));

  for (i = 0; i < arrayDims; i++) {
    array_subrange_type* subrangeEntry = (array_subrange_type*)
                                         (arrayPtr->subrange_entries[i]->entry_ptr);
    varPtr->staticArr->upperBounds[i] = subrangeEntry->upperBound;
  }

  return arrayPtr->type_ptr;
}

// Extracts base type information by assigning var->varType to a basic
// type TypeEntry in BasicTypesArray
// Modifies: var->varType
static void extractBaseType(VariableEntry* var, base_type* basePtr)
{
  FJALAR_DPRINTF("ENTER extractBaseType\n");

  // Figure out what basic type it is
  switch(basePtr->encoding) {
  case DW_ATE_float:
    if (basePtr->byte_size == sizeof(float)) {
      var->varType = BasicTypesArray[D_FLOAT];
    }
    else if (basePtr->byte_size == sizeof(double)) {
      var->varType = BasicTypesArray[D_DOUBLE];
    }
    else if (basePtr->byte_size == sizeof(long double)) {
      var->varType = BasicTypesArray[D_LONG_DOUBLE];
    }
    break;

  case DW_ATE_signed:
  case DW_ATE_signed_char:
    if (basePtr->byte_size == sizeof(char)) {
      var->varType = BasicTypesArray[D_CHAR];
    }
    else if (basePtr->byte_size == sizeof(short)) {
      var->varType= BasicTypesArray[D_SHORT];
    }
    else if (basePtr->byte_size == sizeof(int)) {
      var->varType = BasicTypesArray[D_INT];
    }
    // not used on 32 bit as sizeof(int) == sizeof(long)
    else if (basePtr->byte_size == sizeof(long)) {
      var->varType = BasicTypesArray[D_LONG];
    }
    // not used on 64 bit as sizeof(long) == sizeof(long long)
    else if (basePtr->byte_size == sizeof(long long int)) {
      var->varType = BasicTypesArray[D_LONG_LONG_INT];
    }
    break;

  case DW_ATE_unsigned:
  case DW_ATE_unsigned_char:
    if (basePtr->byte_size == sizeof(unsigned char)) {
      var->varType = BasicTypesArray[D_UNSIGNED_CHAR];
    }
    else if (basePtr->byte_size == sizeof(unsigned short)) {
      var->varType = BasicTypesArray[D_UNSIGNED_SHORT];
    }
    else if (basePtr->byte_size == sizeof(unsigned int)) {
      var->varType = BasicTypesArray[D_UNSIGNED_INT];
    }
    // not used on 32 bit as sizeof(unsigned int) == sizeof(unsigned long)
    else if (basePtr->byte_size == sizeof(long)) {
      var->varType = BasicTypesArray[D_UNSIGNED_LONG];
    }
    // not used on 64 bit as sizeof(unsigned long) == sizeof(unsigned long long)
    else if (basePtr->byte_size == sizeof(unsigned long long int)) {
      var->varType = BasicTypesArray[D_UNSIGNED_LONG_LONG_INT];
    }
    break;

  case DW_ATE_boolean:
    var->varType = BasicTypesArray[D_BOOL];
    break;

  default:
    tl_assert(0 && "Unknown primitive type");
  }

  // Post-condition:
  tl_assert(IS_BASIC_TYPE(var->varType->decType));

  FJALAR_DPRINTF("EXIT  extractBaseType\n");
}

// Extracts enumeration type info
// Modifies: t
static void extractEnumerationType(TypeEntry* t, collection_type* collectionPtr)
{
  FJALAR_DPRINTF("ENTER extractEnumerationType\n");

  t->decType = D_ENUMERATION;
  t->typeName = collectionPtr->name;

  t->byteSize = sizeof(int); // An enumeration is an int
  
  FJALAR_DPRINTF("EXIT  extractEnumerationType\n");
}

// Extracts struct/union type info from collectionPtr and creates
// entries for member variables in t->memberVarList
// (which can be null if there are no non-static member vars)
static void extractStructUnionType(TypeEntry* t, dwarf_entry* e)
{
  FJALAR_DPRINTF("ENTER extractStructUnionType(%p)\n", e);

  collection_type* collectionPtr = 0;
  UInt i = 0, member_func_index = 0, superclass_index = 0;
  VarNode* memberNodePtr = 0;

  tl_assert((e->tag_name == DW_TAG_structure_type) ||
            (e->tag_name == DW_TAG_union_type) ||
            (e->tag_name == DW_TAG_class_type));

  collectionPtr = (collection_type*)(e->entry_ptr);

  FJALAR_DPRINTF("name %s (dec: %d) (ID: %lu) (size: %lu)\n",
              collectionPtr->name,
              collectionPtr->is_declaration,
              e->ID,
              collectionPtr->byte_size);


  t->aggType = VG_(calloc)("generate_fjalar_entries.c: extractStructUnionType.1", 1, sizeof(*t->aggType));


  if (e->tag_name == DW_TAG_union_type) {
    t->decType = D_UNION;
  }
  else {
    t->decType = D_STRUCT_CLASS;
  }

  t->typeName = collectionPtr->name;

  // (comment added 2005)  
  // This is a bit of a hack, but since FunctionTable probably hasn't
  // finished being initialized yet, we will fill up each entry in
  // t->memberFunctionList with the start PC of the function, then
  // later in initMemberFuncs(), we will
  // use those start PC values to look up the actual FunctionEntry
  // entries using getFunctionEntryFromStartAddr().  Thus, we
  // temporarily overload memberFunctionList elts to hold start PC
  // pointer values.

  // First make a dry pass to determine how many functions we actually
  // have debug. info for, and try to fill in start_pc if necessary:
  for (member_func_index = 0;
       member_func_index < collectionPtr->num_member_funcs;
       member_func_index++) {
    function* funcPtr =
      (function*)((collectionPtr->member_funcs[member_func_index])->entry_ptr);

    FJALAR_DPRINTF("  *** funcPtr->mangled_name: %s\n", funcPtr->mangled_name);

    // Look up the start_pc of the function in FunctionSymbolTable if
    // there is no start_pc:
    if (!funcPtr->start_pc) {
      // Try the C++ mangled name first ...
      if (funcPtr->mangled_name) {
        funcPtr->start_pc = (unsigned long)gengettable(FunctionSymbolTable,
                                                       (void*)funcPtr->mangled_name);
      }
      // then try the regular name:
      else if (funcPtr->name) {
        funcPtr->start_pc = (unsigned long)gengettable(FunctionSymbolTable,
                                                       (void*)funcPtr->name);
      }
    }

    // If we can't even find a start_pc, then just punt it:
    if (!funcPtr->start_pc) {
      continue;
    }

    FJALAR_DPRINTF("         funcPtr->start_pc: %p\n", (void *)funcPtr->start_pc);

    // Success!
    // If memberFunctionList hasn't been allocated yet, calloc it:
    if (!t->aggType->memberFunctionList) {
      t->aggType->memberFunctionList =
        (SimpleList*)VG_(calloc)("generate_fjalar_entries.c: extractStructUnionType.2", 1, sizeof(*(t->aggType->memberFunctionList)));
    }

    SimpleListInsert(t->aggType->memberFunctionList,
                     (void*)funcPtr->start_pc);
  }

  for (superclass_index = 0;
       superclass_index < collectionPtr->num_superclasses;
       superclass_index++) {
    inheritance_type* inh =
      (inheritance_type*)(collectionPtr->superclasses[superclass_index])->entry_ptr;

    // Follow the type pointer:
    unsigned long super_type_loc = 0;
    if (binary_search_dwarf_entry_array(inh->superclass_type_ID, &super_type_loc)) {
      dwarf_entry* super_type_entry = &dwarf_entry_array[super_type_loc];
      collection_type* dwarf_super = 0;
      // Make sure that it's a collection entry
      tl_assert(tag_is_collection_type(super_type_entry->tag_name));

      dwarf_super = (collection_type*)(super_type_entry->entry_ptr);

      // Make sure that it has a name; otherwise just give up on it
      if (dwarf_super->name) {

        TypeEntry* existing_entry = 0;
        // Note: We never ever free this! (whoops!)
        Superclass* curSuper = VG_(calloc)("generate_fjalar_entries.c: extractSTructUnionType.3", 1, sizeof(*curSuper));
        curSuper->className = VG_(strdup)("genereate_fjalar_entries.c: extractStructUnionType.3.1", dwarf_super->name);

        // Success!
        // If superclassList hasn't been allocated yet, calloc it:
        if (!t->aggType->superclassList) {
          t->aggType->superclassList =
            (SimpleList*)VG_(calloc)("generate_fjalar_entries.c: extractSTructUnionType.4", 1, sizeof(*(t->aggType->superclassList)));
        }

        // Insert new superclass element:
        SimpleListInsert(t->aggType->superclassList, (void*)curSuper);

        FJALAR_DPRINTF(" +++ super->name: %s\n", dwarf_super->name);

        switch (inh->accessibility) {
        case DW_ACCESS_private:
          curSuper->inheritance = PRIVATE_VISIBILITY;
          break;
        case DW_ACCESS_protected:
          curSuper->inheritance = PROTECTED_VISIBILITY;
          break;
        case DW_ACCESS_public:
        default:
          curSuper->inheritance = PUBLIC_VISIBILITY;
        }

        curSuper->member_var_offset = inh->member_var_offset;

        // Force the superclass TypeEntry to be loaded from
        // TypesTable or created if it doesn't yet exist:
        existing_entry = getTypeEntry(curSuper->className);

        FJALAR_DPRINTF("  [superclass] Try to find existing entry %p in TypesTable with name %s(%p)\n",
                       existing_entry, curSuper->className, curSuper->className);

        if (existing_entry) {
          curSuper->class = existing_entry;
          // We are done!
        }
        // No entry exists for this name, so insert a new one:
        else {
          // Use the tool's constructor to support sub-classing:
          curSuper->class = constructTypeEntry();

          // Insert it into the table BEFORE calling
          // extractStructUnionType() or else we may infinitely
          // recurse!
          FJALAR_DPRINTF("  Insert %s (superclass) into TypesTable\n", curSuper->className);
          genputtable(TypesTable,
                      (void*)curSuper->className,
                      curSuper->class);

          tl_assert((super_type_entry->tag_name == DW_TAG_structure_type) ||
                    (super_type_entry->tag_name == DW_TAG_union_type) ||
                    (super_type_entry->tag_name == DW_TAG_class_type));

          FJALAR_DPRINTF("  Doesn't exist ... trying to add class %s\n", curSuper->className);
          extractStructUnionType(curSuper->class, super_type_entry);
        }
      }
    }
  }

  if (collectionPtr->num_member_vars > 0) {
    t->aggType->memberVarList =
      (VarList*)VG_(calloc)("generate_fjalar_entries.c: extractSTructUnionType.5", 1, sizeof(*(t->aggType->memberVarList)));

    // Look up the dwarf_entry for the struct/union and iterate
    // through its member_vars array (of pointers to members)
    // in order to extract each member variable

    for (i = 0; i < collectionPtr->num_member_vars; i++) {
      member* memberPtr = (member*)((collectionPtr->member_vars[i])->entry_ptr);
      extractOneVariable(t->aggType->memberVarList,
                         memberPtr->type_ptr,
                         memberPtr->name,
                         0,
                         0,
                         0,
                         memberPtr->is_const,
                         memberPtr->const_value,
                         0,
                         0,
                         1,
                         memberPtr->data_member_location,
                         memberPtr->internal_byte_size,
                         memberPtr->internal_bit_offset,
                         memberPtr->internal_bit_size,
                         t,
                         memberPtr->accessibility,
                         0,
                         getDeclaredFile((collectionPtr->member_vars[i])->comp_unit, memberPtr->decl_file));
    }
  }

  FJALAR_DPRINTF("t: %s, num_static_member_vars: %u\n",
                  t->typeName,
                  collectionPtr->num_static_member_vars);

  // Extract static member variables into staticMemberVarList only if
  // there is at least 1 static member variable:
  if (collectionPtr->num_static_member_vars > 0) {
    unsigned long ind;
    VarNode* node = 0;

    t->aggType->staticMemberVarList =
      (VarList*)VG_(calloc)("generate_fjalar_entries.c: extractSTructUnionType.6", 1, sizeof(*(t->aggType->staticMemberVarList)));

    for (ind = 0; ind < collectionPtr->num_static_member_vars; ind++) {

      char *mangled_name = NULL, *name = NULL;
      char is_external = 0;
      char is_const = 0;
      long const_value = 0;
      unsigned long globalVarAddr = 0, accessibility = 0;
      dwarf_entry* type_ptr = NULL;
      char* decl_file = NULL;

      // Commonalities between these really need to be extracted
      // into a struct which variable and member "inherit" from
      // for now, let's use Macros

      tl_assert(tag_is_variable(collectionPtr->static_member_vars[ind]->tag_name) ||
                tag_is_member(collectionPtr->static_member_vars[ind]->tag_name));

#define EXTRACT_STATIC_INFO(dwarf_type, dwarf_ptr) \
      dwarf_type *staticMemberPtr = (dwarf_type*)dwarf_ptr; \
      is_external = staticMemberPtr->is_external; \
      accessibility = staticMemberPtr->accessibility; \
      type_ptr = staticMemberPtr->type_ptr;           \
      is_const = staticMemberPtr->is_const;           \
      const_value = staticMemberPtr->const_value

      if(tag_is_variable(collectionPtr->static_member_vars[ind]->tag_name)) {
        EXTRACT_STATIC_INFO(variable, collectionPtr->static_member_vars[ind]->entry_ptr);
        mangled_name = staticMemberPtr->mangled_name;
        globalVarAddr = staticMemberPtr->globalVarAddr;
        if (staticMemberPtr->name)
            FJALAR_DPRINTF("??? Static member var - var name: %s\n", staticMemberPtr->name);
        if (staticMemberPtr->mangled_name)
            FJALAR_DPRINTF("??? Static member var - var mangled: %s\n", staticMemberPtr->mangled_name);
        decl_file = getDeclaredFile(collectionPtr->static_member_vars[ind]->comp_unit, staticMemberPtr->decl_file);
        
      } else if(tag_is_member(collectionPtr->static_member_vars[ind]->tag_name)) {
        EXTRACT_STATIC_INFO(member, collectionPtr->static_member_vars[ind]->entry_ptr);
        if (staticMemberPtr->name)
            FJALAR_DPRINTF("??? Static member var - member: %s\n", staticMemberPtr->name);
        // We intentionally leave 'name' as null.  This will cause the
        // call to extractOneVariable below to do nothing.  This is 
        // okay because we will process static members later with the
        // globals.   (markro)
        decl_file = getDeclaredFile(collectionPtr->static_member_vars[ind]->comp_unit, staticMemberPtr->decl_file);
      }

      // Try to find a global address in VariableSymbolTable if it
      // doesn't exist yet:
      if (!globalVarAddr) {
        // Try the C++ mangled name:
        if (mangled_name) {
          globalVarAddr = (Addr)gengettable(VariableSymbolTable, (void*)mangled_name);
        }
      }

      extractOneVariable(t->aggType->staticMemberVarList,
                         type_ptr,
                         // If a mangled name exists, pass it in so
                         // that it can be de-mangled:
                         (mangled_name ? mangled_name : name),
                         0,
                         1,
                         is_external,
                         is_const,
                         const_value,
                         globalVarAddr,
                         0,
                         1, 0, 0, 0, 0,
                         t,
                         accessibility,
                         0,
                         decl_file);
      
    }

    // This is a very important step.  We want to iterate over
    // t->staticMemberVarList and insert every VariableEntry element
    // into the globalVars list because static member variables are
    // really globals albeit with limited scope:
    for (node = t->aggType->staticMemberVarList->first;
         node != NULL;
         node = node->next) {
      VariableEntry* curStaticVar = node->var;
      VarNode* lastGlobalNode = 0;

      // Insert a new node into globalVars:
      insertNewNode(&globalVars);
      lastGlobalNode = globalVars.last;
      // FREE the VG_(calloc)'ed VariableEntry since we don't want to
      // use it (we will replace it with curStaticVar):
      destroyVariableEntry(lastGlobalNode->var);
      lastGlobalNode->var = curStaticVar;
    }
  }

  // After we are doing constructing the struct TypeEntry entry,
  // we must initialize the struct byte size:

  // To calculate the byte size of the struct, we look at the
  // data_member_location of the last member and add its byte size
  // (if member is actually a struct type, then its byte size should already
  //  have been computed by the recursive version of this call to that struct)
  if (t->aggType->memberVarList) {
    memberNodePtr = t->aggType->memberVarList->last;
    if (memberNodePtr) {
      int structByteSize = 0;
      VariableEntry* memberVarPtr = memberNodePtr->var;
      structByteSize =
        memberVarPtr->memberVar->data_member_location + determineVariableByteSize(memberVarPtr);

      // Round struct size up to the nearest word (dependent on architecture)
      if(sizeof(UWord)==4) {
        t->byteSize = ((structByteSize + 3) >> 2) << 2;
      } else if (sizeof(UWord)==8){
        t->byteSize = ((structByteSize + 7) >> 3) << 3;
      } else {
        // This portion of the check may be silly, but oh well.
        FJALAR_DPRINTF("Unsupported word size: %lu\n", (unsigned long) sizeof(UWord));
        tl_assert(0);
      }

      if(collectionPtr->byte_size) {
        t->byteSize = collectionPtr->byte_size;

      }

      FJALAR_DPRINTF("collection name: %s, byteSize: %d\n", t->typeName, t->byteSize);
    }
  }
  else {
    t->byteSize = 0;
  }

  FJALAR_DPRINTF("EXIT  extractStructUnionType(%p)\n", e);
}



// Extracts only the local variables of type DW_TAG_array_type
// or collection_type (struct/union)
// and places them in the local_vars list within each respective
// function (we need struct types because they may contain static arrays
// or structs which themselves contain static arrays)
static void extractLocalArrayAndStructVariables(FunctionEntry* f,
                                                function* dwarfFunctionEntry)
{
  UInt i;

  FJALAR_DPRINTF("ENTER extractLocalArrayAndStructVariables - %s (#: %u)\n",
         dwarfFunctionEntry->name, dwarfFunctionEntry->num_local_vars);

  // No local variables - don't do anything
  if (!dwarfFunctionEntry->num_local_vars)
    return;

  for (i = 0; i < dwarfFunctionEntry->num_local_vars; i++)
    {
      FJALAR_DPRINTF("%s - local_vars: %u of %d\n", dwarfFunctionEntry->name, i+1, dwarfFunctionEntry->num_local_vars);
      extractOneLocalArrayOrStructVariable(f,
                                           dwarfFunctionEntry->local_vars[i]);
    }

  FJALAR_DPRINTF("EXIT  extractLocalArrayAndStructVariables - %s\n",
          dwarfFunctionEntry->name);
}

// MUST BE RUN AFTER the return value for a function has been initialized!!!
// Otherwise it cannot tell whether the function returns a struct type!!!
//
// We potentially want to ignore the offsets that DWARF2 provides for
// us because if Valgrind gains control at the beginning of a
// function, the parameters are not guaranteed to be at those
// locations yet. We have devised our own calculation that
// word-aligns everything in the caller's stack frame (positive offsets
// from EBP). We always use this computed value if the DWARF information
// didn't provide a location (which can happen for instance if the parameter
// is unused), or if replace == 1.
// This code will need a major rewrite to support AMD64.
static void verifyStackParamWordAlignment(FunctionEntry* f, int replace)
{
  VarNode* cur_node;
  int offset = 8;
  VarNode* firstNode = f->returnValue.first;

  FJALAR_DPRINTF("ENTER verifyStackParamWordAlignment(%s): %p\n",
                 f->fjalar_name, firstNode);

  // Start with default offset of 8 from EBP (*EBP = old EBP, *(EBP+4) = return addr)
  // unless the function returns a struct by value - then we start
  // with an offset of 12 since *(EBP+8) = pointer to the place to put the struct)

  if (firstNode) {
    VariableEntry* firstReturnVar = firstNode->var;
    // See if the function seturn a struct by value:
    if (firstReturnVar &&
        (D_STRUCT_CLASS == firstReturnVar->varType->decType) &&
        (0 == firstReturnVar->ptrLevels) &&
        // Don't forget C++ reference variables!
        (0 == firstReturnVar->referenceLevels)) {
      offset = 12;
    }
  }

  for (cur_node = f->formalParameters.first;
       cur_node != NULL;
       cur_node = cur_node->next)
    {
      int cur_byteSize = 0;
      if (cur_node->var->locationType == NO_LOCATION || replace) {
        cur_node->var->locationType = FP_OFFSET_LOCATION;
        cur_node->var->byteOffset = offset;
      }
      cur_byteSize = determineVariableByteSize(cur_node->var);
      // WORD ALIGNED!!!
      if (cur_byteSize > 0)
        {
          // Round offset up to the nearest word (4 bytes)
          offset += (((cur_byteSize + 3) >> 2) << 2);
        }
    }

  FJALAR_DPRINTF("EXIT verifyStackParamWordAlignment(%s)\n",
                 f->fjalar_name);
}

// Returns the byte size of the given VariableEntry
static int determineVariableByteSize(VariableEntry* var)
{
  int byteSize = 0;

  if (0 == var->ptrLevels) {
    byteSize = var->varType->byteSize;
  }
  // Static array of some type
  else if (IS_STATIC_ARRAY_VAR(var))
    {
      UInt i;

      if (var->ptrLevels == 1) {
        byteSize = var->varType->byteSize; // static array of base type
      }
      else if (var->ptrLevels > 1) {
        byteSize = sizeof(void*); // static array of pointers
      }

      for (i = 0; i < var->staticArr->numDimensions; i++) {
        FJALAR_DPRINTF("  upperBounds[%u] = %u\n", i, var->staticArr->upperBounds[i]);
        byteSize *= (var->staticArr->upperBounds[i] + 1);
      }
    }
  // Pointer type
  else {
    byteSize = sizeof(void*);
  }

  FJALAR_DPRINTF("detDVBS | name: %s, decPtrLvls: %u, isSA: %d, byteSize: %d, return: %d\n",
                 var->name,
                 var->ptrLevels,
                 IS_STATIC_ARRAY_VAR(var) ? 1 : 0,
                 var->varType->byteSize,
                 byteSize);

  return byteSize;
}


// Determines the number of bytes needed above the frame pointer in
// the stack to hold the values of all function formal parameters for
// a particular function
int determineFormalParametersStackByteSize(FunctionEntry* f)
{
  VarNode* cur_node;
  int totalByteSize = 0;

  if(!f){
    return 0;
  }

  for (cur_node = f->formalParameters.first;
       cur_node != NULL;
       cur_node = cur_node->next)
    {
      int this_end = cur_node->var->byteOffset +
        determineVariableByteSize(cur_node->var);
      totalByteSize = MAX(totalByteSize, this_end);
    }
  // PG comment said "Just to be safe, round UP to the next multiple
  // of 4". For the moment, live dangerously and see if anything
  // breaks. -SMcC
  return totalByteSize;
}


// Determines the number of bytes needed below the frame pointer in
// the stack to hold the values of all function formal parameters for
// a particular function.
int determineFormalParametersLowerStackByteSize(FunctionEntry* f)
{
  VarNode* cur_node;
  int totalByteSize = 0;

  if(!f){
    return 0;
  }

  for (cur_node = f->formalParameters.first;
       cur_node != NULL;
       cur_node = cur_node->next)
    {
      totalByteSize = MIN(totalByteSize, cur_node->var->byteOffset);
    }
  return -totalByteSize;
}


// dwarfParamEntry->tag_name == DW_TAG_formal_parameter
static void extractOneFormalParameterVar(FunctionEntry* f,
                                         dwarf_entry* dwarfParamEntry)
{
  FJALAR_DPRINTF("ENTER extractOneFormalParameterVar(%p)\n", dwarfParamEntry);

  formal_parameter* paramPtr = 0;
  dwarf_entry* typePtr = 0;
  VariableEntry *varPtr;

  if (dwarfParamEntry == NULL || !tag_is_formal_parameter(dwarfParamEntry->tag_name)) {
    printf( "Error, formal parameter information struct is null or belongs to the incorrect type\n");
    my_abort();
  }

  paramPtr = (formal_parameter*)(dwarfParamEntry->entry_ptr);
  typePtr = paramPtr->type_ptr;

  if (!paramPtr->name) {
    // Previously this generated an error, but unnamed parameters are legal. (markro)
    FJALAR_DPRINTF("  %s has an unnamed parameter\n", f->name);
    // The maximum size is 19 + 8 + 1 = 28; 19 for "unnamed_parameter0x",
    // 8 for maximum size for ID, and 1 for null-terminator
    char* fake_name = VG_(calloc)("generate_fjalar_entries.c: extraceOneFormalParameterVar", 28, sizeof(*fake_name));
    sprintf(fake_name, "unnamed_parameter0x%lx", dwarfParamEntry->ID);
    paramPtr->name = fake_name;
  }
  FJALAR_DPRINTF("  %s parameter name %s\n", f->name, paramPtr->name);

  varPtr = extractOneVariable(&(f->formalParameters),
                              typePtr,
                              paramPtr->name,
                              0,
                              0,
                              0,
                              0,
                              0,
                              0,
                              0,
                              0,0,0,0,0,0,0,1,
                              0);

  if (paramPtr->dwarf_stack_size > 0) {
    unsigned int i;
    FJALAR_DPRINTF("\tCopying over DWARF Location stack\n");
    for(i = 0; i < paramPtr->dwarf_stack_size; i++) {
      varPtr->location_expression[i].atom = paramPtr->dwarf_stack[i].atom;
      varPtr->location_expression[i].atom_offset = paramPtr->dwarf_stack[i].atom_offset;
      FJALAR_DPRINTF("\tCopying over  %s (%lld)\n", location_expression_to_string(varPtr->location_expression[i].atom), varPtr->location_expression[i].atom_offset);
    }
    varPtr->location_expression_size = paramPtr->dwarf_stack_size;
  }

  if (paramPtr->location_type == LT_FP_OFFSET) {
    varPtr->validLoc = paramPtr->valid_loc;
    varPtr->locationType = FP_OFFSET_LOCATION;
    varPtr->byteOffset = paramPtr->location;
    //    varPtr->atom = paramPtr->loc_atom;

    FJALAR_DPRINTF(" location_type: %u, byteOffset: %x\n", varPtr->locationType, (unsigned int)varPtr->byteOffset);
  }

  FJALAR_DPRINTF("EXIT  extractOneFormalParameterVar\n");
}

static void extractFormalParameterVars(FunctionEntry* f,
                                       function* dwarfFunctionEntry)
{
  UInt i;

  FJALAR_DPRINTF("ENTER extractFormalParameterVars - %s (#: %u)\n",
         dwarfFunctionEntry->name, dwarfFunctionEntry->num_formal_params);

  // No formal parameters - don't do anything
  if (!dwarfFunctionEntry->num_formal_params)
    return;

  for (i = 0; i < dwarfFunctionEntry->num_formal_params; i++)
    {
      extractOneFormalParameterVar(f, dwarfFunctionEntry->params[i]);
    }

  FJALAR_DPRINTF("EXIT  extractFormalParameterVars\n");
}


// Only adds a new entry if dwarfVariableEntry's type ==
// DW_TAG_array_type or struct or union type:
static void extractOneLocalArrayOrStructVariable(FunctionEntry* f,
                                                 dwarf_entry* dwarfVariableEntry)
{
  FJALAR_DPRINTF("ENTER extractOneLocalArrayOrStructVariable(%p)\n", dwarfVariableEntry);

  variable* variablePtr = 0;
  dwarf_entry* typePtr = 0;
  VariableEntry *varPtr;

  if (dwarfVariableEntry == NULL || !tag_is_variable(dwarfVariableEntry->tag_name)) {
    printf( "Error, local variable information struct is null or belongs to the incorrect type\n");
    my_abort();
  }

  variablePtr = (variable*)(dwarfVariableEntry->entry_ptr);
  typePtr = variablePtr->type_ptr;

  if (!typePtr) {
    printf( "Unexpected typed local variable %s in %s\n",
                 variablePtr->name, f->name);
    return;
  }

  // Only store array types and struct/union types!
  // Also, don't store anything with couldBeGlobalVar == true
  // because that means that it's a static variable.
  // static variables have global scope so they can be picked up
  // by the sweep of the global variables
  if (!(tag_is_array_type(typePtr->tag_name) ||
        (DW_TAG_structure_type == typePtr->tag_name) ||
        (DW_TAG_union_type == typePtr->tag_name) ||
        (DW_TAG_class_type == typePtr->tag_name)) ||
      variablePtr->couldBeGlobalVar) {
    return;
  }

  if (!variablePtr->name) {
    printf( "Unexpected unnamed local variable in %s\n",
            f->name);
    return;
  }

  FJALAR_DPRINTF("  %s local variable name %s - localArrayAndStructVars %p size = %u\n",
                 f->name,
                 variablePtr->name,
                 &(f->localArrayAndStructVars),
                 f->localArrayAndStructVars.numVars);

  varPtr = extractOneVariable(&(f->localArrayAndStructVars),
                              typePtr,
                              variablePtr->name,
                              0,
                              0,
                              0,
                              0,
                              0,
                              0,
                              0,
                              0,0,0,0,0,0,0,0,
                              getDeclaredFile(dwarfVariableEntry->comp_unit, variablePtr->decl_file));

  FJALAR_DPRINTF("  set locationType FP_OFFSET\n");
  if (variablePtr->regBase == -1) {
      varPtr->locationType = FP_OFFSET_LOCATION;
  } else {  
      // Potential bug!  We are ignoring the regBase value
      // and just assuming it is ESP.  This is the only case
      // we've seen (i386 only) so far.  (markro)
      varPtr->locationType = SP_OFFSET_LOCATION;
  }
  varPtr->byteOffset = variablePtr->offset;

  FJALAR_DPRINTF("EXIT  extractOneLocalArrayOrStructVariable(%p)\n", dwarfVariableEntry);
}

static void extractReturnVar(FunctionEntry* f,
                             function* dwarfFunctionEntry)
{
  // Get the return value type
  dwarf_entry* typePtr = dwarfFunctionEntry->return_type;

  FJALAR_DPRINTF("ENTER extractReturnVar - %s\n", dwarfFunctionEntry->name);

  // void function - no return type
  if(!typePtr) {
    FJALAR_DPRINTF("DONE (empty) - extractReturnVar - %s\n",
                   dwarfFunctionEntry->name);

    return;
  }

  f->returnValue.numVars = 0;

  extractOneVariable(&(f->returnValue),
                     typePtr,
                     RETURN_VALUE_NAME,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,0,0,0,0,0,0,0,0);

  FJALAR_DPRINTF("EXIT  extractReturnVar - %s\n", dwarfFunctionEntry->name);
}



// Scan through varsToUpdateTypes, look at the varType entries, look
// them up in TypesTable, replace the entries with the real versions,
// and free the faux TypeEntry:
void updateAllVarTypes(void) {
  VarNode* n;

  if (0 == varsToUpdateTypes.numVars) {
    return;
  }

  FJALAR_DPRINTF("ENTER updateAllVarTypes: %u\n", varsToUpdateTypes.numVars);

  for (n = varsToUpdateTypes.first;
       n != NULL;
       n = n->next) {
    VariableEntry* var = n->var;
    TypeEntry* fake_type = var->varType;
    TypeEntry* real_type = 0;

    // If we punted on this already, then don't do anything about it:
    if (fake_type == &VoidType) {
      continue;
    }

    tl_assert(fake_type->typeName);

    // Try to look in TypesTable for the entry:
    real_type = getTypeEntry(fake_type->typeName);

    // If we don't find it already in TypesTable, then look directly
    // in the DWARF debug info for a REAL struct entry (is_declaration
    // == 0) whose name matches the given typeName.  If it's
    // found, then allocate a new TypeEntry, populate it with that
    // data, and stuff it into TypesTable.  If it's not found, then
    // simply give up.
    if (!real_type) {
      dwarf_entry* struct_dwarf_ptr =
        find_struct_entry_with_name(fake_type->typeName);

      if (struct_dwarf_ptr) {
        real_type = constructTypeEntry();
        extractStructUnionType(real_type, struct_dwarf_ptr);

        // Add it to TypesTable
        genputtable(TypesTable,
                    (void*)real_type->typeName,
                    real_type);
      }
    }

    // If we have found a real type, then assign it to var->varType:
    if (real_type) {
      var->varType = real_type;
    }
    // Otherwise, assign it to a generic void type:
    else {
      var->varType = &VoidType;
    }

    // Free this because in either code path, we have assigned
    // var->varType away already
    VG_(free)(fake_type);
  }

  // Remember to NOT destroy the VariableEntry entries inside the list
  // because they are aliased elsewhere:
  clearVarList(&varsToUpdateTypes, 0);

  FJALAR_DPRINTF("EXIT  updateAllVarTypes\n");
}


// Extracts one variable and inserts it at the end of varListPtr
static VariableEntry*
extractOneVariable(VarList* varListPtr,
                   dwarf_entry* typePtr,
                   const char* variableName,
                   char* fileName,
                   char isGlobal,
                   char isExternal,
                   char isConstant,
                   long constantValue,
                   unsigned long globalLocation,
                   unsigned long functionStartPC,
                   char isStructUnionMember,
                   unsigned long data_member_location,
                   int internalByteSize,
                   int internalBitOffset,
                   int internalBitSize,
                   TypeEntry* structParentType,
                   unsigned long dwarf_accessibility,
                   char isFormalParam,
                   char* declared_in) // All static arrays which are
// formal parameters are treated like NORMAL pointers which are not statically-sized
// just because that's how the C language works
{
  VariableEntry* varPtr = 0;
  char ptrLevels = 0;
  char referenceLevels = 0;

  char* demangled_name = 0;

  FJALAR_DPRINTF("ENTER extractOneVariable for %s(varListPtr: %p)\n", variableName, varListPtr);

  // Don't extract the variable if it has a bogus name:
  if (!variableName || ignore_variable_with_name(variableName))
    return 0;

  // Create a new VariableEntry and append it to the end of VarList
  insertNewNode(varListPtr);

  // Work on the last variable in varListPtr
  varPtr = varListPtr->last->var;

  // Attempt to demangle C++ names (nothing happens if it's not a
  // mangled name)
  demangled_name = cplus_demangle_v3(variableName, 3);
  if (demangled_name) {
    varPtr->name = demangled_name;
  }
  else {
    varPtr->name = variableName;
  }

  // Special case for C++ 'this' parameter variables:
  // Automatically put a 'P' disambig on it because
  // 'this' will always refer to one object and not an array
  // (comment added 2005)  
  // TODO: This will simple-mindedly pick up any variable named 'this'
  // so it's possible that in a C program, you can have some variable
  // named 'this' and it'll get a 'P' disambig letter assigned to it
  if (VG_STREQ("this", variableName)) {
    varPtr->disambig = 'P';
  }

  // Propogate information about constants
  if(typePtr && (typePtr->tag_name == DW_TAG_const_type)) {
    varPtr->isConstant = True;
  }

  varPtr->isConstant |= isConstant;
  varPtr->constValue = constantValue;
    

  if (isGlobal) {
    varPtr->globalVar = VG_(calloc)("generate_fjalar_entries.c: extractOneVariable.1",1, sizeof(*varPtr->globalVar));
    varPtr->globalVar->isExternal = isExternal;
    varPtr->globalVar->fileName = fileName;
    varPtr->globalVar->globalLocation = globalLocation;
    varPtr->globalVar->functionStartPC = functionStartPC;
  }

  if (isStructUnionMember) {
    varPtr->memberVar = VG_(calloc)("generate_fjalar_entries.c: extractOneVariable.2", 1, sizeof(*varPtr->memberVar));
    varPtr->memberVar->data_member_location = data_member_location;
    varPtr->memberVar->internalByteSize = internalByteSize;
    varPtr->memberVar->internalBitOffset = internalBitOffset;
    varPtr->memberVar->internalBitSize = internalBitSize;
    varPtr->memberVar->structParentType = structParentType;
    FJALAR_DPRINTF("StructUnionMember: %s member of %s\n", varPtr->name,
                   structParentType ? structParentType->typeName : 0);

    // Figure out varPtr->visibility:
    switch (dwarf_accessibility) {
    case DW_ACCESS_private:
      varPtr->memberVar->visibility = PRIVATE_VISIBILITY;
      break;
    case DW_ACCESS_protected:
      varPtr->memberVar->visibility = PROTECTED_VISIBILITY;
      break;
    case DW_ACCESS_public:
    default:
      varPtr->memberVar->visibility = PUBLIC_VISIBILITY;
    }
  }

  varPtr->declaredIn = declared_in;

  FJALAR_DPRINTF("\tAbout to strip modifiers for %s\n", variableName);

  // Strip off modifier, typedef, and array tags until we eventually
  // hit a base or collection type (or a null pointer meaning "void")
  while (typePtr && (tag_is_modifier_type(typePtr->tag_name)
                     || tag_is_typedef(typePtr->tag_name)
                     || tag_is_array_type(typePtr->tag_name)))
    {
      if (tag_is_modifier_type(typePtr->tag_name))
        {
          // Strip off modifier tags and put each new stripped entry into typePtr
          modifier_type* modifierPtr = (modifier_type*)(typePtr->entry_ptr);

          // If the parameter is a "pointer" type, create one pointer
          // variable then one derived variable for every layer of indirection
          if (typePtr->tag_name == DW_TAG_pointer_type) {
            ptrLevels++;
          }
          // If the parameter is a C++ reference:
          // (this should really be incremented only once)
          else if (typePtr->tag_name == DW_TAG_reference_type) {
              referenceLevels++;
          }

          // If the parameter is a "const" or "volatile" type, just strip
          // off the "const" or "volatile" and process it again
          typePtr = extractModifierType(modifierPtr);
        }
      else if (tag_is_array_type(typePtr->tag_name))
        {
          array_type* arrayPtr = (array_type*)(typePtr->entry_ptr);
          typePtr = extractArrayType(varPtr, arrayPtr);
          ptrLevels++;
        }
      else if (tag_is_typedef(typePtr->tag_name))
        {
          typePtr = ((typedef_type*)typePtr->entry_ptr)->target_type_ptr;
        }
    }

  FJALAR_DPRINTF("\tFinished stripping modifiers for %s\n", variableName);
  FJALAR_DPRINTF("\tfunctionStartPC is %lx\n", functionStartPC);
  FJALAR_DPRINTF("\tvarPtr is %p\n", varPtr);
  FJALAR_DPRINTF("\ttypePtr is %p\n", typePtr);
  FJALAR_DPRINTF("\tConstant: %s\n", varPtr->isConstant?"Yes":"No");
  if(varPtr->isConstant) {
    FJALAR_DPRINTF("\t\tValue: %ld\n", varPtr->constValue);
  }
  
  FJALAR_DPRINTF("\tDeclared in: %s\n", (varPtr->declaredIn)?varPtr->declaredIn:"UNKNOWN");

  varPtr->ptrLevels = ptrLevels;
  varPtr->referenceLevels = referenceLevels;

  FJALAR_DPRINTF("\tptrLevels is %u\n", varPtr->ptrLevels);

  if (typePtr && ((typePtr->tag_name == DW_TAG_structure_type) ||
                  (typePtr->tag_name == DW_TAG_class_type))) {
    char* type_name = ((collection_type*)(typePtr->entry_ptr))->name;
    // We want to ignore POINTERS to certain types (don't ignore
    // the actual values of that type because it may screw up alignments).
    // Instead, we want to convert these into generic void pointers.
    if ((varPtr->ptrLevels > 0) &&
        ignore_type_with_name(type_name)) {
      //      printf("IGNORED --- %s\n", type_name);
      varPtr->varType = &VoidType;
      return varPtr; // punt at this point
    }
  }

  // Formal parameters which appear to be statically-sized arrays are
  // actually simply pointers:
  if (isFormalParam && IS_STATIC_ARRAY_VAR(varPtr)) {
    VG_(free)(varPtr->staticArr->upperBounds);
    VG_(free)(varPtr->staticArr);
    varPtr->staticArr = 0;
  }

  // Link it to a TypeEntry if one already exists
  varPtr->varType = 0;
  // We are passing in the true ID but casting it so the compiler won't warn me:


  // WARNING: Some typedefs do not have targets - if typePtr == NULL,
  // just say screw it and make this variable into a dummy null
  // variable: Void typePtr entries will NOT be in TypesTable :(
  if (!typePtr) {
    // Got void; probably was void *, const void *, etc.
    varPtr->varType = BasicTypesArray[D_VOID];
  }
  // (From this point forward, we know that typePtr is non-null,
  //  as long as we keep doing 'else if's)
  // For base and function types, DO NOT use the TypesTable and
  // instead use one of the entries in BasicTypesArray:
  else if (tag_is_base_type(typePtr->tag_name)) {
    base_type* basePtr = (base_type*)(typePtr->entry_ptr);
    extractBaseType(varPtr, basePtr);
  }
  else if (typePtr->tag_name == DW_TAG_subroutine_type) {
    // Function (from a function pointer)
    // Treat sorta like a hashcode, for the moment.
    varPtr->varType = BasicTypesArray[D_FUNCTION];
  }
  // For struct/union/enum types, we want to make sure that we are
  // performing a lookup on a REAL entry, not just a declaration:
  // (Hopefully, if all goes well, the only TypeEntry values in
  // TypesTable are REAL entries whose dwarf_entry has is_declaration
  // NULL, not fake declaration entries).  We also want to ensure that
  // there is at most one entry in TypesTable for a particular
  // collection name.
  else if (tag_is_collection_type(typePtr->tag_name)) {
    collection_type* collectionPtr = (collection_type*)(typePtr->entry_ptr);

    // I dunno what to do if we don't have a name - we need to pull
    // one out of thin air (or maybe make one from the DWARF ID):
    tl_assert(collectionPtr->name);

    // If it's a fake entry (is_declaration == 1), then we will create
    // a fake entry for varType and insert the variable in the
    // varsToUpdateTypes list so that updateAllVarTypes() can later
    // replace them with their real types:
    if (collectionPtr->is_declaration) {
      // Use the tool's constructor to properly support sub-classing:
      TypeEntry* fake_entry = constructTypeEntry();

      fake_entry->typeName = collectionPtr->name;

      varPtr->varType = fake_entry;
      insertNewNode(&varsToUpdateTypes);
      varsToUpdateTypes.last->var = varPtr;

      FJALAR_DPRINTF("  Inserted *fake* entry for variable %s with type %s\n",
                     variableName, collectionPtr->name);
    }
    // Otherwise, try to find an entry in TypesTable if one already exists
    else {
      TypeEntry* existing_entry = getTypeEntry(collectionPtr->name);

      FJALAR_DPRINTF("  Try to find existing entry %p in TypesTable with name %s\n",
                     existing_entry, collectionPtr->name);

      if (existing_entry) {
        FJALAR_DPRINTF("  Using existing type entry for %s\n", variableName);

        varPtr->varType = existing_entry;
        // We are done!
      }
      // No entry exists for this name, so insert a new one:
      else {
        FJALAR_DPRINTF("  Adding type entry for %s\n", variableName);

        // Use the tool's constructor to properly support sub-classing:
        varPtr->varType = constructTypeEntry();

        // Insert it into the table BEFORE calling
        // extractStructUnionType() or else we may infinitely recurse!

        FJALAR_DPRINTF("  Insert %s into TypesTable\n", collectionPtr->name);

        genputtable(TypesTable,
                    (void*)collectionPtr->name,
                    varPtr->varType);

        // If the parameter is an enumeration type
        if (typePtr->tag_name == DW_TAG_enumeration_type) {
          collection_type* colPtr = (collection_type*)(typePtr->entry_ptr);
          extractEnumerationType(varPtr->varType, colPtr);
        }
        // Struct or union type (where most of the action takes place)
        else if  ((typePtr->tag_name == DW_TAG_structure_type) ||
                  (typePtr->tag_name == DW_TAG_union_type) ||
                  (typePtr->tag_name == DW_TAG_class_type)) {
          extractStructUnionType(varPtr->varType, typePtr);
        }
      }
    }
  }

  // (comment added 2005)  
  // TODO: What about arrays of pointers?  int* [10] currently turns
  // into base type = int, ptrLevels = 2, isStaticArray = true
  // but it should be base type = hashcode, ptrLevels = 1, isStaticArray = true

  // Proposed solution: If IS_STATIC_ARRAY_VAR() and (ptrLevels > 1 and
  // varPtr->varType->decType != D_CHAR) or (ptrLevels > 2 and
  // varPtr->varType->decType == D_CHAR), then
  // we turn it into a 1-D array of hashcodes by setting ptrLevels = 1
  // and pointing the type to VoidType.
  // This means that we do not support multidimensional arrays
  // (but we didn't used to either) but fail more gracefully on them now
  if (IS_STATIC_ARRAY_VAR(varPtr) &&
      (ptrLevels > ((varPtr->varType->decType == D_CHAR) ?
                    2 : 1))) {
    varPtr->ptrLevels = 1;
    varPtr->varType = &VoidType;
  }

  FJALAR_DPRINTF("\tdecType is: %s\n", DeclaredTypeString[varPtr->varType->decType]);
  FJALAR_DPRINTF("EXIT  extractOneVariable for %s\n", variableName);

  return varPtr;
}


// FunctionTable - hash table containing FunctionEntry entries

// Super-trivial key comparison method -
int equivalentIDs(int ID1, int ID2) {
  return (ID1 == ID2);
}

// Run some heuristics to clean up some of the DWARF debugging data.

static void processFunctions() {
  FuncIterator* funcIt = newFuncIterator();

  FJALAR_DPRINTF("ENTER processFunctions\n");

  while(hasNextFunc(funcIt)) {
    FunctionEntry* f = nextFunc(funcIt);
    FJALAR_DPRINTF("Examining Function: %s\n", f->name);

    // GCC-4 Optimization work around. GCC-4 will optimize away
    // the location attributes for argc and argv of the 'main'
    // function if they are unused. Since calling convention
    // of main on x86 is well defined, we will attempt to locate
    // the argc and argv values ourself

    // We've found argc iff:
    // 1.) f->name is main
    // 2.) f->formalParameters.first->var->VarType->DeclaredType == D_INT
    // argc is 0 bytes offset from the base of the frame pointer.
    //

    // We've found argv iff:
    // 1.) f->name is main
    // 2.) f->formalParameters.first->var->VarType->DeclaredType == D_INT
    // argv is 4 bytes offset from the base of the frame pointer.

    if(VG_STREQ("main", f->name)) {
      if ((f->formalParameters.numVars > 0) &&
          (f->formalParameters.first->var) &&
          !(f->formalParameters.first->var->validLoc) &&
          (f->formalParameters.first->var->varType->decType == D_INT)){
        VariableEntry* var = f->formalParameters.first->var;
        printf("Found invalid argc, varByteOffset is: %d\n", var->byteOffset);
        var->byteOffset = 16;
        var->validLoc = 1;
      }

      if ((f->formalParameters.numVars > 1) &&
          (f->formalParameters.first->next->var) &&
          !(f->formalParameters.first->next->var->validLoc) &&
          (f->formalParameters.first->next->var->varType->decType == D_CHAR)) {
        VariableEntry* var = f->formalParameters.first->next->var;
        printf("Found invalid argv, varByteOffset is: %d\n", var->byteOffset);
        var->byteOffset = 20;
        var->validLoc = 1;
      }
    }
  }

  FJALAR_DPRINTF("EXIT  processFunctions\n");
  deleteFuncIterator(funcIt);
}



// More C++ fun.  So apparently constructors and destructors are
// printed in the DWARF debugging information as regular functions,
// not member functions.  Thus, the only reasonable way to infer that
// a function is a constructor or a destructor is to pattern match the
// names of functions to names of types in TypesTable.
static void initConstructorsAndDestructors(void) {
  FuncIterator* funcIt = newFuncIterator();


  // Iterate through all entries in TypesTable:
  while (hasNextFunc(funcIt)) {
    FunctionEntry* f = nextFunc(funcIt);

    // Here are our pattern-matching heuristics:

    // A function is a constructor iff:
    // 1.) Its raw C name (f->name) matches the name of a type in TypesTable
    // 2.) Its first parameter has the name 'this'
    // (The 2nd condition prevents false positives of C functions that
    // have the same name as structs - e.g., 'struct foo' and 'foo()'.
    // I don't know why you would ever do that, but it's legal.)

    // A function is a destructor iff:
    // 1.) Its name starts with '~'
    // 2.) Its name with the '~' stripped off the front matches the name
    //     of a type in TypesTable
    // 3.) Its first parameter has the name 'this'

    if ((f->formalParameters.numVars > 0) &&
        (f->formalParameters.first->var) &&
        VG_STREQ("this", f->formalParameters.first->var->name)) {
      TypeEntry* parentClass = 0;


      // (comment added 2009)  
      // RUDD - Dirty dirty hack. Force the location of this to be valid
      f->formalParameters.first->var->validLoc = 1;


      // Use the regular (not mangled or demangled) name for matching
      tl_assert(f->name);

      // See if it's a constructor:
      parentClass = getTypeEntry(f->name);

      if (parentClass) {
        FJALAR_DPRINTF(" *** CONSTRUCTOR! func-name: %s\n", f->name);

        f->parentClass = parentClass;
        tl_assert(IS_AGGREGATE_TYPE(parentClass));

        // Insert f into the parent class's constructorList,
        // allocating it if necessary:
        if (!parentClass->aggType->constructorList) {
          parentClass->aggType->constructorList =
            (SimpleList*)VG_(calloc)("generate_fjalar_entries.c: initConstructorsandDestructors.1", 1, sizeof(*(parentClass->aggType->constructorList)));
        }
        SimpleListInsert(parentClass->aggType->constructorList, (void*)f);
      }
      // See if it's a destructor
      else if ('~' == f->name[0]) {
        // Notice how we skip forward one letter to cut off the '~':
        parentClass = getTypeEntry((char*)(&(f->name[1])));

        if (parentClass) {
          FJALAR_DPRINTF(" *** DESTRUCTOR! func-name: %s\n", f->name);

          f->parentClass = parentClass;
          tl_assert(IS_AGGREGATE_TYPE(parentClass));

          // Insert f into the parent class's destructorList,
          // allocating it if necessary:
          if (!parentClass->aggType->destructorList) {
            parentClass->aggType->destructorList =
              (SimpleList*)VG_(calloc)("generate_fjalar_entries.c: initConstructorsandDestructors.2", 1, sizeof(*(parentClass->aggType->destructorList)));
          }
          SimpleListInsert(parentClass->aggType->destructorList, (void*)f);
        }
      }
    }
  }

  deleteFuncIterator(funcIt);
}

// Initializes all member functions for structs in TypesTable.
// Pre: This should only be run after TypesTable and FunctionTable
// have been initialized.
static void initMemberFuncs(void) {
  TypeIterator* typeIt = newTypeIterator();

  FJALAR_DPRINTF("ENTER initMemberFuncs\n");

  // Iterate through all entries in TypesTable:
  while (hasNextType(typeIt)) {
    TypeEntry* t = nextType(typeIt);

    FJALAR_DPRINTF("Examining %s it has dec_type %u\n", t->typeName, t->decType);

    // Only do this for struct/union types:
    if ((t->decType == D_STRUCT_CLASS) ||
        (t->decType == D_UNION)) {
      // (comment added 2005)  
      // This is a bit of a hack, but in extractStructUnionType(), we
      // initialized the entries of t->memberFunctionList with the
      // start PC of the member functions (we had to do this because
      // FunctionTable wasn't initialized at that time).  Thus, we
      // temporarily overload memberFunctionList elts to hold start PC
      // pointer values.  Now we will iterate over those values and
      // use getFunctionEntryFromStartAddr() to try to fill them in
      // with actual FunctionEntry instances:
      SimpleNode* n;
      FJALAR_DPRINTF("Searching for member funcs for %s\n", t->typeName);

      if (t->aggType->memberFunctionList) {
        for (n = t->aggType->memberFunctionList->first;
             n != NULL;
             n = n->next) {
          unsigned long start_PC = (unsigned long)(ptrdiff_t)(n->elt);
          tl_assert(start_PC);

          FJALAR_DPRINTF("  hacked start_pc: %p - parentClass = %s\n",
                         VoidPtr(start_PC), t->typeName);
          // Hopefully this will always be non-null
          n->elt = getFunctionEntryFromStartAddr(start_PC);
          tl_assert(n->elt);
          FJALAR_DPRINTF(" n->elt - name: %s = %p\n", ((FunctionEntry*)(n->elt))->name, (void *)n->elt);;
          // Very important!  Signify that it's a member function
          ((FunctionEntry*)(n->elt))->parentClass = t;

        }
      }
    }
  }

  FJALAR_DPRINTF("EXIT  initMemberFuncs\n");
  deleteTypeIterator(typeIt);
}

// FunctionTable

// This is SLOW because we must traverse all values, looking for the
// fjalar_name
FunctionEntry* getFunctionEntryFromFjalarName(char* fjalar_name) {
  FuncIterator* funcIt = newFuncIterator();
  while (hasNextFunc(funcIt)) {
    FunctionEntry* entry = nextFunc(funcIt);
    tl_assert(entry);
    if (VG_STREQ(entry->fjalar_name, fjalar_name)) {
      deleteFuncIterator(funcIt);
      return entry;
    }
  }
  deleteFuncIterator(funcIt);
  return 0;
}

// This is SLOW because we must traverse all values
// looking for an entry whose startPC and endPC encompass the
// desired address addr, inclusive.  Thus addr is in the range of
// [startPC, endPC]
FunctionEntry* getFunctionEntryFromAddr(Addr addr) {
  FuncIterator* funcIt = newFuncIterator();
  while (hasNextFunc(funcIt)) {
    FunctionEntry* entry = nextFunc(funcIt);
    tl_assert(entry && entry->startPC && entry->endPC);
    if ((entry->startPC <= addr) &&
        (addr <= entry->endPC)) {
      deleteFuncIterator(funcIt);
      return entry;
    }
  }
  deleteFuncIterator(funcIt);
  return 0;
}

// Iterate thru all chars, sum up each (ASCII value * (index + 1))
// Don't worry about modding because GenericHashtable.c will do it for us :)
unsigned int hashString(const char* str1) {
  int i;
  int sum = 0;
  int len = VG_(strlen)(str1);
  for (i = 0; i < len; i++) {
    sum += ((int)(str1[i]) * (i + i));
  }

  return sum;
}

int equivalentStrings(char* str1, char* str2) {
  return VG_STREQ(str1, str2);
}

VarIterator* newVarIterator(VarList* vlist) {
  VarIterator* varIt = (VarIterator*)VG_(calloc)("generate_fjalar_entries.c: newVarIterator", 1, sizeof(*varIt));
  tl_assert(vlist);
  varIt->curNode = vlist->first; // This could be null for an empty list
  return varIt;
}

Bool hasNextVar(VarIterator* varIt) {
  // Empty list:
  if (!varIt->curNode) {
    return 0;
  }
  else {
    return 1;
  }
}

VariableEntry* nextVar(VarIterator* varIt) {
  VariableEntry* v = 0;
  tl_assert(varIt && varIt->curNode);
  v = varIt->curNode->var;
  varIt->curNode = varIt->curNode->next;
  return v;
}

void deleteVarIterator(VarIterator* varIt) {
  tl_assert(varIt);
  VG_(free)(varIt);
}


// Returns the TypeEntry entry found in TypesTable with typeName
// matching the given name, and return 0 if nothing found.
TypeEntry* getTypeEntry(char* typeName) {
  return (TypeEntry*)gengettable(TypesTable, (void*)typeName);
}

TypeIterator* newTypeIterator() {
  TypeIterator* typeIt = (TypeIterator*)VG_(calloc)("generateFjalarEntries.c: newTypeIterator", 1, sizeof(*typeIt));
  typeIt->it = gengetiterator(TypesTable);
  return typeIt;
}

Bool hasNextType(TypeIterator* typeIt) {
  return !(typeIt->it->finished);
}

TypeEntry* nextType(TypeIterator* typeIt) {
  if (typeIt->it->finished) {
    return 0;
  }
  else {
    return (TypeEntry*)(gengettable(TypesTable, gennext(typeIt->it)));
  }
}

void deleteTypeIterator(TypeIterator* typeIt) {
  tl_assert(typeIt && typeIt->it);
  genfreeiterator(typeIt->it);
  VG_(free)(typeIt);
}


// Copy-and-paste alert! (but let's not resort to macros)
FuncIterator* newFuncIterator() {
  FuncIterator* funcIt = (FuncIterator*)VG_(calloc)("generateFjalarEntries.c: newFuncIterator", 1, sizeof(*funcIt));
  funcIt->it = gengetiterator(FunctionTable);
  return funcIt;
}

Bool hasNextFunc(FuncIterator* funcIt) {
  return !(funcIt->it->finished);
}

FunctionEntry* nextFunc(FuncIterator* funcIt) {
  if (funcIt->it->finished) {
    return 0;
  }
  else {
    return (FunctionEntry*)(gengettable(FunctionTable, gennext(funcIt->it)));
  }
}

void deleteFuncIterator(FuncIterator* funcIt) {
  tl_assert(funcIt && funcIt->it);
  genfreeiterator(funcIt->it);
  VG_(free)(funcIt);
}

char* getDeclaredFile(compile_unit* comp_unit, unsigned long file_idx) {
  if (comp_unit && (file_idx > 0) && (file_idx <= VG_(sizeXA)(comp_unit->file_name_table))) {
    return *(char**)VG_(indexXA)(comp_unit->file_name_table, file_idx - 1);
  } 
  return NULL;
}


#define XML_PRINTF(...) fprintf(xml_output_fp, __VA_ARGS__)

// Pre: xml_output_fp is open
void outputAllXMLDeclarations() {
  XML_PRINTF("<program>\n");

  XML_PRINTF("<executable-name>%s</executable-name>\n",
             executable_filename);

  XMLprintGlobalVars();
  XMLprintFunctionTable();
  XMLprintTypesTable();

  XML_PRINTF("</program>\n");
}

typedef enum {
  MEMBER_FUNCTION,
  CONSTRUCTOR_OR_DESTRUCTOR,
  REGULAR_FUNCTION
} FunctionXMLPrintType;

// Format things slightly differently for member functions:
static void XMLprintOneFunction(FunctionEntry* cur_entry,
                                FunctionXMLPrintType printType) {

  XML_PRINTF("<function");
  // Add function attributes:
  if (printType == MEMBER_FUNCTION) {
    XML_PRINTF(" type=\"");
    switch (cur_entry->visibility) {
    case PRIVATE_VISIBILITY:
      XML_PRINTF("private-member-function");
      break;
    case PROTECTED_VISIBILITY:
      XML_PRINTF("protected-member-function");
    break;
    default:
      XML_PRINTF("public-member-function");
      break;
    }
    XML_PRINTF("\"");
  }
  else if (printType == REGULAR_FUNCTION) {
    if (!cur_entry->isExternal) {
      XML_PRINTF(" type=\"file-static\"");
    }
  }
  XML_PRINTF(">\n");

  if (cur_entry->name) {
    XML_PRINTF("<name><![CDATA[%s]]></name>\n",
               cur_entry->name);
  }

  if (cur_entry->fjalar_name) {
    XML_PRINTF("<fjalar-name><![CDATA[%s]]></fjalar-name>\n",
               cur_entry->fjalar_name);
  }

  XML_PRINTF("<start-PC>%p</start-PC>\n",
             (void*)cur_entry->startPC);
  XML_PRINTF("<entry-PC>%p</entry-PC>\n",
             (void*)cur_entry->entryPC);
  XML_PRINTF("<end-PC>%p</end-PC>\n",
             (void*)cur_entry->endPC);

  if (cur_entry->filename) {
    XML_PRINTF("<filename>%s</filename>\n",
               cur_entry->filename);
  }

  XML_PRINTF("<formal-parameters>\n");
  XMLprintVariablesInList(&cur_entry->formalParameters);
  XML_PRINTF("</formal-parameters>\n");

  if (cur_entry->localArrayAndStructVars.numVars > 0) {
    XML_PRINTF("<local-array-and-struct-variables>\n");
    XMLprintVariablesInList(&cur_entry->localArrayAndStructVars);
    XML_PRINTF("</local-array-and-struct-variables>\n");
  }

  XML_PRINTF("<return-value>\n");
  XMLprintVariablesInList(&cur_entry->returnValue);
  XML_PRINTF("</return-value>\n");

  XML_PRINTF("</function>\n");
}

static void XMLprintGlobalVars()
{
  XML_PRINTF("<global-variable-declarations>\n");
  XMLprintVariablesInList(&globalVars);
  XML_PRINTF("</global-variable-declarations>\n");
}

static void XMLprintFunctionTable()
{
  FuncIterator* funcIt = newFuncIterator();

  XML_PRINTF("<function-declarations>\n");

  while (hasNextFunc(funcIt)) {
    FunctionEntry* cur_entry = nextFunc(funcIt);

    if (!cur_entry) {
      continue;
    }

    // DO NOT print out C++ member functions here.  Instead, print
    // them out as part of the <type> entry
    if (cur_entry->parentClass) {
      continue;
    }

    XMLprintOneFunction(cur_entry, REGULAR_FUNCTION);
  }

  XML_PRINTF("</function-declarations>\n");

  deleteFuncIterator(funcIt);
}

static void XMLprintTypesTable() {
  TypeIterator* typeIt = newTypeIterator();

  XML_PRINTF("<type-declarations>\n");

  while (hasNextType(typeIt)) {
    TypeEntry* cur_entry = nextType(typeIt);

    if (!cur_entry) {
      continue;
    }

    XML_PRINTF("<type>\n");

    if (cur_entry->typeName) {
      XML_PRINTF("<type-name>%s</type-name>\n",
                 cur_entry->typeName);
    }

    XML_PRINTF("<byte-size>%d</byte-size>\n",
               cur_entry->byteSize);

    XML_PRINTF("<declared-type>%s</declared-type>\n",
               DeclaredTypeNames[cur_entry->decType]);

    if (IS_AGGREGATE_TYPE(cur_entry)) {

      if (cur_entry->aggType->memberVarList &&
          (cur_entry->aggType->memberVarList->numVars > 0)) {
        XML_PRINTF("<member-variables>\n");
        XMLprintVariablesInList(cur_entry->aggType->memberVarList);
        XML_PRINTF("</member-variables>\n");
      }

      if (cur_entry->aggType->staticMemberVarList &&
          (cur_entry->aggType->staticMemberVarList->numVars > 0)) {
        XML_PRINTF("<static-member-variables>\n");
        XMLprintVariablesInList(cur_entry->aggType->staticMemberVarList);
        XML_PRINTF("</static-member-variables>\n");
      }

      if (cur_entry->aggType->constructorList &&
          (cur_entry->aggType->constructorList->numElts > 0)) {
        SimpleNode* n;
        XML_PRINTF("<constructors>\n");

        for (n = cur_entry->aggType->constructorList->first;
             n != NULL;
             n = n->next) {
          XMLprintOneFunction((FunctionEntry*)(n->elt),
                              CONSTRUCTOR_OR_DESTRUCTOR);
        }
        XML_PRINTF("</constructors>\n");
      }

      if (cur_entry->aggType->destructorList &&
          (cur_entry->aggType->destructorList->numElts > 0)) {
        SimpleNode* n;
        XML_PRINTF("<destructors>\n");

        for (n = cur_entry->aggType->destructorList->first;
             n != NULL;
             n = n->next) {
          XMLprintOneFunction((FunctionEntry*)(n->elt),
                              CONSTRUCTOR_OR_DESTRUCTOR);
        }
        XML_PRINTF("</destructors>\n");
      }

      if (cur_entry->aggType->memberFunctionList &&
          (cur_entry->aggType->memberFunctionList->numElts > 0)) {
        SimpleNode* n;
        XML_PRINTF("<member-functions>\n");

        for (n = cur_entry->aggType->memberFunctionList->first;
             n != NULL;
             n = n->next) {
          XMLprintOneFunction((FunctionEntry*)(n->elt),
                              MEMBER_FUNCTION);
        }
        XML_PRINTF("</member-functions>\n");
      }

      if (cur_entry->aggType->superclassList &&
          (cur_entry->aggType->superclassList->numElts > 0)) {
        SimpleNode* n;
        for (n = cur_entry->aggType->superclassList->first;
             n != NULL;
             n = n->next) {
          Superclass* super = (Superclass*)(n->elt);

          XML_PRINTF("<superclass ");

          switch(super->inheritance) {
          case PRIVATE_VISIBILITY:
            XML_PRINTF("inheritance=\"private\"");
            break;
          case PROTECTED_VISIBILITY:
            XML_PRINTF("inheritance=\"protected\"");
            break;
          case PUBLIC_VISIBILITY:
          default:
            XML_PRINTF("inheritance=\"public\"");
          }

          XML_PRINTF(" member-var-offset=\"%lu\"",
                     super->member_var_offset);

          XML_PRINTF(">%s</superclass>\n",
                     super->className);
        }
      }
    }

    XML_PRINTF("</type>\n");
  }

  XML_PRINTF("</type-declarations>\n");

  deleteTypeIterator(typeIt);
}

static void XMLprintVariablesInList(VarList* varListPtr) {
  VarIterator* varIt;
  tl_assert(varListPtr);
  varIt = newVarIterator(varListPtr);

  while (hasNextVar(varIt)) {
    VariableEntry* cur_var = nextVar(varIt);
    // Special case: Skip C++ member variables that are in the
    // globalVars list:
    if ((varListPtr == &globalVars) && IS_MEMBER_VAR(cur_var)) {
      continue;
    }

    XMLprintOneVariable(cur_var);
  }

  deleteVarIterator(varIt);
}

// Prints one VariableEntry
static void XMLprintOneVariable(VariableEntry* var) {
  TypeEntry* t;

  if (!var) {
    return;
  }

  t = var->varType;

  XML_PRINTF("<variable>\n");

  XML_PRINTF("<name><![CDATA[%s]]></name>\n", var->name);

  if (IS_GLOBAL_VAR(var)) {
    XML_PRINTF("<global-var>\n");

    XML_PRINTF("<location>%p</location>\n",
               (void*)var->globalVar->globalLocation);

    if (var->globalVar->fileName) {
      XML_PRINTF("<filename>%s</filename>\n",
                 var->globalVar->fileName);
    }

    if (!var->globalVar->isExternal) {
      XML_PRINTF("<file-static-var>\n");

      if (var->globalVar->functionStartPC) {
        XML_PRINTF("<function-start-PC>%p</function-start-PC>\n",
                   (void*)var->globalVar->functionStartPC);
      }

      XML_PRINTF("</file-static-var>\n");
    }

    XML_PRINTF("</global-var>\n");
  }

  if (var->byteOffset) {
    XML_PRINTF("<stack-byte-offset>%d</stack-byte-offset>\n",
               var->byteOffset);
  }

  if (IS_STATIC_ARRAY_VAR(var)) {
    UInt i = 0;

    XML_PRINTF("<static-array>\n");

    XML_PRINTF("<num-dimensions>%u</num-dimensions>\n",
               var->staticArr->numDimensions);

    for (i = 0; i < var->staticArr->numDimensions; i++) {
      XML_PRINTF("<upper-bound>%u</upper-bound>\n",
                 var->staticArr->upperBounds[i]);
    }

    XML_PRINTF("</static-array>\n");
  }

  if (IS_MEMBER_VAR(var)) {
    XML_PRINTF("<member-var visibility=\"");
    switch(var->memberVar->visibility) {
    case PRIVATE_VISIBILITY:
      XML_PRINTF("private");
      break;
    case PROTECTED_VISIBILITY:
      XML_PRINTF("protected");
      break;
    case PUBLIC_VISIBILITY:
    default:
      XML_PRINTF("public");
    }
    XML_PRINTF("\">\n");

    XML_PRINTF("<member-location>%lu</member-location>\n",
               var->memberVar->data_member_location);

    XML_PRINTF("<parent-type>%s</parent-type>\n",
               var->memberVar->structParentType->typeName);

    XML_PRINTF("</member-var>\n");
  }

  if (t) {
    XML_PRINTF("<var-type");

    if (var->ptrLevels > 0) {
      XML_PRINTF(" pointer-levels=\"%u\"", var->ptrLevels);
    }
    if (var->referenceLevels > 0) {
      XML_PRINTF(" reference-levels=\"%u\"", var->referenceLevels);
    }
    if (IS_STRING(var)) {
      XML_PRINTF(" is-string=\"true\"");
    }

    XML_PRINTF(">\n");

    XML_PRINTF("<declared-type>%s</declared-type>\n",
               DeclaredTypeNames[t->decType]);
    XML_PRINTF("<byte-size>%d</byte-size>\n",
               t->byteSize);

    if (t->typeName) {
      XML_PRINTF("<type-name>%s</type-name>\n",
                 t->typeName);
    }

    XML_PRINTF("</var-type>\n");
  }

  XML_PRINTF("</variable>\n");
}
