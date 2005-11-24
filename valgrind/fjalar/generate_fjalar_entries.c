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

#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "fjalar_main.h"
#include "generate_fjalar_entries.h"
#include "elf/dwarf2.h"
#include "GenericHashtable.h"

#include "fjalar_tool.h"

static void initializeFunctionTable();
static void initializeGlobalVarsList();
static void initMemberFuncs();
static void initConstructorsAndDestructors();
static void createNamesForUnnamedDwarfEntries();
static void updateAllVarTypes();

static void extractFormalParameterVars(FunctionEntry* f,
				       function* dwarfFunctionEntry);
static void extractLocalArrayAndStructVariables(FunctionEntry* f,
						function* dwarfFunctionEntry);
static void extractOneLocalArrayOrStructVariable(FunctionEntry* f,
						 dwarf_entry* dwarfVariableEntry);
static void extractReturnVar(FunctionEntry* f,
			     function* dwarfFunctionEntry);

static int determineVariableByteSize(VariableEntry* var);
static void verifyStackParamWordAlignment(FunctionEntry* f);

static void extractOneVariable(VarList* varListPtr,
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
                               TypeEntry* structParentType,
                               unsigned long dwarf_accessibility,
                               char isFormalParam);

static void repCheckOneVariable(VariableEntry* var);

static void XMLprintGlobalVars();
static void XMLprintFunctionTable();
static void XMLprintTypesTable();
static void XMLprintVariablesInList(VarList* varListPtr);
static void XMLprintOneVariable(VariableEntry* var);

FILE* xml_output_fp = 0;

// Global singleton entries for basic types.  These do not need to be
// placed in TypesTable because they are un-interesting.
TypeEntry UnsignedCharType = {D_UNSIGNED_CHAR, 0, sizeof(unsigned char), 0, 0, 0, 0, 0, 0, 0};
TypeEntry CharType = {D_CHAR, 0, sizeof(char), 0, 0, 0, 0, 0, 0, 0};
TypeEntry UnsignedShortType = {D_UNSIGNED_SHORT, 0, sizeof(unsigned short), 0, 0, 0, 0, 0, 0, 0};
TypeEntry ShortType = {D_SHORT, 0, sizeof(short), 0, 0, 0, 0, 0, 0, 0};
TypeEntry UnsignedIntType = {D_UNSIGNED_INT, 0, sizeof(unsigned int), 0, 0, 0, 0, 0, 0, 0};
TypeEntry IntType = {D_INT, 0, sizeof(int), 0, 0, 0, 0, 0, 0, 0};
TypeEntry UnsignedLongLongIntType = {D_UNSIGNED_LONG_LONG_INT, 0, sizeof(unsigned long long int), 0, 0, 0, 0, 0, 0, 0};
TypeEntry LongLongIntType = {D_LONG_LONG_INT, 0, sizeof(long long int), 0, 0, 0, 0, 0, 0, 0};
TypeEntry UnsignedFloatType = {D_UNSIGNED_FLOAT, 0, sizeof(float), 0, 0, 0, 0, 0, 0, 0};
TypeEntry FloatType = {D_FLOAT, 0, sizeof(float), 0, 0, 0, 0, 0, 0, 0};
TypeEntry UnsignedDoubleType = {D_UNSIGNED_DOUBLE, 0, sizeof(double), 0, 0, 0, 0, 0, 0, 0};
TypeEntry DoubleType = {D_DOUBLE, 0, sizeof(double), 0, 0, 0, 0, 0, 0, 0};
TypeEntry UnsignedLongDoubleType = {D_UNSIGNED_LONG_DOUBLE, 0, sizeof(long double), 0, 0, 0, 0, 0, 0, 0};
TypeEntry LongDoubleType = {D_LONG_DOUBLE, 0, sizeof(long double), 0, 0, 0, 0, 0, 0, 0};
TypeEntry FunctionType = {D_FUNCTION, 0, sizeof(void*), 0, 0, 0, 0, 0, 0, 0};
TypeEntry VoidType = {D_VOID, 0, sizeof(void*), 0, 0, 0, 0, 0, 0, 0};
TypeEntry BoolType = {D_BOOL, 0, sizeof(char), 0, 0, 0, 0, 0, 0, 0};

// Array indexed by DeclaredType where each entry is a pointer to one
// of the above singleton entries:

TypeEntry* BasicTypesArray[22] = {
  0,  //  D_NO_TYPE, // Create padding
  &UnsignedCharType,  //  D_UNSIGNED_CHAR,
  &CharType,  //  D_CHAR,
  &UnsignedShortType,  //  D_UNSIGNED_SHORT,
  &ShortType,  //  D_SHORT,
  &UnsignedIntType, //  D_UNSIGNED_INT,
  &IntType, //  D_INT,
  &UnsignedLongLongIntType, //  D_UNSIGNED_LONG_LONG_INT,
  &LongLongIntType, //  D_LONG_LONG_INT,
  &UnsignedFloatType, //  D_UNSIGNED_FLOAT, // currently unused
  &FloatType, //  D_FLOAT,
  &UnsignedDoubleType, //  D_UNSIGNED_DOUBLE, // currently unused
  &DoubleType, //  D_DOUBLE,
  &UnsignedLongDoubleType, //  D_UNSIGNED_LONG_DOUBLE, // currently unused
  &LongDoubleType, //  D_LONG_DOUBLE,
  0, //  D_ENUMERATION,
  0, //  D_STRUCT,
  0, //  D_UNION,
  &FunctionType, //  D_FUNCTION,
  &VoidType, //  D_VOID,
  0, //  D_CHAR_AS_STRING, // when .disambig 'C' option is used with chars
  &BoolType //  D_BOOL            // C++ only
};

// To figure out if a certain DeclaredType t is a basic type, simply
// query whether its entry in BasicTypesArray is non-null:
#define IS_BASIC_TYPE(t) (BasicTypesArray[t])


// A temporary data structure of variables that need to have their
// varType entries updated after TypesTable has been initialized.
// This is used for variables whose type entries are 'fake'
// (is_declaration == 1) so we want to fill them in with 'real' values
// of the same name later.  All variables in this list have their
// varType initialized to a dynamically-allocated TypeEntry whose
// collectionName is initialized properly, but all other fields in
// this TypeEntry are empty.  During updateAllVarTypes(), we scan
// through this list, look at the varType entries, look them up in
// TypesTable, replace the entries with the real versions, and free
// the faux TypeEntry:
VarList varsToUpdateTypes = {0, 0, 0};

// Global strings

static char* RETURN_VALUE_NAME = "return";

// For printing:
// Corresponds to DeclaredType enum:
char* DeclaredTypeNames[] = {"D_NO_TYPE", // Create padding
                             "D_UNSIGNED_CHAR",
                             "D_CHAR",
                             "D_UNSIGNED_SHORT",
                             "D_SHORT",
                             "D_UNSIGNED_INT",
                             "D_INT",
                             "D_UNSIGNED_LONG_LONG_INT",
                             "D_LONG_LONG_INT",
                             "D_UNSIGNED_FLOAT", // currently unused
                             "D_FLOAT",
                             "D_UNSIGNED_DOUBLE", // currently unused
                             "D_DOUBLE",
                             "D_UNSIGNED_LONG_DOUBLE", // currently unused
                             "D_LONG_DOUBLE",
                             "D_ENUMERATION",
                             "D_STRUCT",
                             "D_UNION",
                             "D_FUNCTION",
                             "D_VOID",
                             "D_CHAR_AS_STRING",
                             "D_BOOL"};

// This is a list of function names to avoid -
// mostly as a result of weirdo C++ compiler stuff:
// (This was all done by empirical observation)
// Note: DON'T IGNORE FUNCTIONS WITH NO NAMES
static char ignore_function_with_name(char* name) {
  if (!name) {
    return 0;
  }

  if ((0 == VG_(strncmp)(name, "__static_initialization_and_destruction", 39)) ||
      VG_STREQ(name, "_Alloc_hider") ||
      VG_STREQ(name, "~_Alloc_hider") ||
      VG_STREQ(name, "_Rep") ||
      (0 == VG_(strncmp)(name, "._", 2)) ||
      (0 == VG_(strncmp)(name, "_S_", 3)) ||
      (0 == VG_(strncmp)(name, "_M_", 3)) ||
      (0 == VG_(strncmp)(name, "_GLOBAL", 7)) ||
      (0 == VG_(strncmp)(name, "__tcf", 5)))
    return 1;
  else
    return 0;
}

// Ignores some weirdo C++ variables such as vtable function pointers
// and friends
// Note: DON'T IGNORE VARIABLES WITH NO NAMES
static char ignore_variable_with_name(char* name) {
  if (!name) {
    return 0;
  }

  if (VG_STREQ(name, "__ioinit") ||
      (0 == VG_(strncmp)(name, "_vptr.", 6)) ||
      (0 == VG_(strncmp)(name, "_ZTI", 4)) ||
      (0 == VG_(strncmp)(name, "_ZTS", 4)))
    return 1;
  else
    return 0;
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

// Super simple list - doesn't do any dynamic allocation or
// deallocation of elt - just stores pointers:

// Insert elt at the head of lst, allocating a new SimpleNode
void SimpleListPush(SimpleList* lst, void* elt) {
  SimpleNode* newNode;
  tl_assert(lst);
  newNode = VG_(calloc)(1, sizeof(*newNode));
  newNode->elt = elt;

  if (lst->first) {
    tl_assert(lst->numElts > 0);
    newNode->next = lst->first;
  }
  else {
    tl_assert(lst->numElts == 0);
    newNode->next = NULL;
  }

  lst->first = newNode;
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
    VG_(printf)(" Warning - SimpleListPop() attempting to pop an empty list\n");
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
  tl_assert(lst->numElts == 0);
}

void SimpleListInit(SimpleList* lst) {
  lst->first = NULL;
  lst->numElts = 0;
}

// Inserts a new node at the end of varListPtr
void insertNewNode(VarList* varListPtr)
{
  if (varListPtr->last)
    {
      varListPtr->last->next = VG_(calloc)(1, sizeof(VarNode));
      varListPtr->last->next->prev = varListPtr->last;
      varListPtr->last = varListPtr->last->next;
      varListPtr->numVars++;
    }
  else
    {
      varListPtr->last = varListPtr->first = VG_(calloc)(1, sizeof(VarNode));
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
          //	  VG_(free)(varListPtr->first);
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

// Clears the list:
void clearVarList(VarList* varListPtr) {
  VarNode* node = varListPtr->first;
  VarNode* nextNode = 0;

  while (node) {
    nextNode = node->next;
    destroyVariableEntry(node->var);
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
void initializeAllFjalarData()
{

  // First delete everything that's in the globalVars list
  clearVarList(&globalVars);

  // TODO: We need to free up the entries in TypesTable if we are
  // really trying to be robust

  VisitedStructsTable = 0;

  FJALAR_DPRINTF("About to allocate hash table\n");

  // Initialize TypesTable
  TypesTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  createNamesForUnnamedDwarfEntries();

  initializeFunctionTable();

  // We need to initialize this list even if we are ignoring globals
  // (with --ignore-globals) because otherwise we won't be able to
  // find references to global variables from pointer parameters:
  initializeGlobalVarsList();

  // Initialize member functions last after TypesTable and
  // FunctionTable have already been initialized:
  initMemberFuncs();

  // Initialize all constructors and destructors by using a heuristic
  // to pattern match names to type names:
  initConstructorsAndDestructors();

  updateAllVarTypes();

  VG_(printf)(".data:   0x%x bytes starting at %p\n.bss:    0x%x bytes starting at %p\n.rodata: 0x%x bytes starting at %p\n",
              data_section_size, data_section_addr,
              bss_section_size, bss_section_addr,
              rodata_section_size, rodata_section_addr);

  // Should only be called here:
  VG_(printf)("BEGIN checking the representation of internal data structures ...\n");
  repCheckAllEntries();
  VG_(printf)("DONE with representation checks.\n");
}

// Returns true iff the address is within a global area as specified
// by the executable's symbol table (it lies within the .data, .bss,
// or .rodata sections):
char addressIsGlobal(unsigned int addr) {
  return (((addr >= data_section_addr) && (addr < data_section_addr + data_section_size)) ||
          ((addr >= bss_section_addr) && (addr < bss_section_addr + bss_section_size)) ||
          ((addr >= rodata_section_addr) && (addr < rodata_section_addr + rodata_section_size)));
}

// Performs a scan over all VariableEntry, TypeEntry, and
// FunctionEntry instances in various data structures and checks to
// make sure that all invariants hold true after initialization.
// Checks entries in globalVars, TypesTable, and FunctionTable.  This
// make take a bit of time to run, but it gives us confidence that our
// data structures are initialized properly and obviates the need for
// lots of checks later in execution.
void repCheckAllEntries() {
  VarNode* curNode;
  unsigned int numGlobalVars = 0;
  struct geniterator* it;

  // Rep. check all variables in globalVars:

  VG_(printf)("  Rep. checking global variables list ...\n");
  for (curNode = globalVars.first;
       curNode != 0;
       curNode = curNode->next) {
    VariableEntry* curGlobalVar = curNode->var;

    // Specific requirements for global vars:
    tl_assert(curGlobalVar->isGlobal);

    // Basic checks:
    repCheckOneVariable(curGlobalVar);

    numGlobalVars++;
  }

  // Check the integrity of globalVars.numVars
  tl_assert(numGlobalVars == globalVars.numVars);


  VG_(printf)("DONE\n");

  // Rep. check all entries in FunctionTable
  it = gengetiterator(FunctionTable);

  VG_(printf)("  Rep. checking function entries ...\n");
  while (!it->finished) {
    FunctionEntry* f = (FunctionEntry*)
      gengettable(FunctionTable, gennext(it));

    VarNode* n;

    unsigned int numFormalParams = 0;
    unsigned int numLocalArrayVars = 0;
    unsigned int numReturnVars = 0;

    int prevByteOffset = 0;

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

      tl_assert(!v->isGlobal);

      // Make sure variables are listed in order of increasing byte
      // offsets (no variable should have a 0 byte offset):
      tl_assert(v->byteOffset > prevByteOffset);
      prevByteOffset = v->byteOffset;

      repCheckOneVariable(v);
      numFormalParams++;
    }
    tl_assert(numFormalParams == f->formalParameters.numVars);

    // Local static array variables:
    for (n = f->localArrayAndStructVars.first;
	 n != 0;
	 n = n->next) {
      VariableEntry* v = n->var;

      tl_assert(!v->isGlobal);

      repCheckOneVariable(v);
      numLocalArrayVars++;
    }
    tl_assert(numLocalArrayVars == f->localArrayAndStructVars.numVars);

    // Return value:
    for (n = f->returnValue.first;
	 n != 0;
	 n = n->next) {
      VariableEntry* v = n->var;

      tl_assert(!v->isGlobal);
      tl_assert(0 == v->byteOffset);

      repCheckOneVariable(v);
      numReturnVars++;
    }
    tl_assert(numReturnVars == f->returnValue.numVars);

  }

  genfreeiterator(it);

  VG_(printf)("DONE\n");

  VG_(printf)("  Rep. checking type entries ...\n");

  // Rep. check all entries in TypesTable
  it = gengetiterator(TypesTable);

  while (!it->finished) {
    TypeEntry* t = (TypeEntry*)
      gengettable(TypesTable, gennext(it));

    // All TypeEntry instances within TypesTable should NOT be basic
    // types:
    tl_assert(!IS_BASIC_TYPE(t->decType));

    // Properties that should hold true for all TypeEntry instances:

    tl_assert((D_ENUMERATION == t->decType) ||
              (D_STRUCT == t->decType) ||
              (D_UNION == t->decType));

    // Because TypesTable is indexed by name, there should be no
    // unnamed entries in TypesTable:
    tl_assert(t->collectionName);

    if (t->isStructUnionType) {
      VarNode* n;
      unsigned int numMemberVars = 0;
      unsigned int prev_data_member_location = 0;
      UShort memberFuncIndex = 0;
      UShort superclassIndex = 0;

      tl_assert(t->collectionName);

      FJALAR_DPRINTF("  collectionName: %s\n", t->collectionName);

      tl_assert((D_STRUCT == t->decType) ||
		(D_UNION == t->decType));
      tl_assert(t->memberVarList);

      // Rep. check member variables:
      for (n = t->memberVarList->first;
	   n != 0;
	   n = n->next) {
	VariableEntry* curMember = n->var;

	VG_(printf)(" checking member %s for %s\n",
		    curMember->name, t->collectionName);

	// Specific checks for member variables:
	tl_assert(curMember->isStructUnionMember);
	tl_assert(0 == curMember->byteOffset);

	// For a struct, check that data_member_location is greater
	// than the one of the previous member variable.  Notice that
	// data_member_location can be 0.
	if (D_STRUCT == t->decType) {
	  if (prev_data_member_location > 0) {
	    tl_assert(curMember->data_member_location > prev_data_member_location);
	  }
	  prev_data_member_location = curMember->data_member_location;
	}
	// For a union, all offsets should be 0
	else if (D_UNION == t->decType) {
	  tl_assert(0 == curMember->data_member_location);
	}

	tl_assert(curMember->structParentType == t);

	repCheckOneVariable(curMember);

	numMemberVars++;
      }
      tl_assert(numMemberVars == t->memberVarList->numVars);

      // Rep. check static member variables (if there are any):
      if (t->staticMemberVarList) {
	unsigned int numStaticMemberVars = 0;
	VarNode* node;

	for (node = t->staticMemberVarList->first;
	     node != 0;
	     node = node->next) {
	  VariableEntry* curMember = node->var;

	  VG_(printf)(" checking STATIC member %s for %s\n",
		      curMember->name, t->collectionName);

	  // Specific checks for static member variables:
	  tl_assert(curMember->isStructUnionMember);
	  tl_assert(0 == curMember->byteOffset);
	  tl_assert(0 == curMember->data_member_location);
	  tl_assert(curMember->isGlobal);
	  tl_assert(curMember->structParentType == t);

	  repCheckOneVariable(curMember);

	  numStaticMemberVars++;
	}
	tl_assert(numStaticMemberVars == t->staticMemberVarList->numVars);
      }

      VG_(printf)("Before checking member functions (num: %u)\n",
		  t->memberFunctionArraySize);
      // Rep. check member functions:
      for (memberFuncIndex = 0;
	   memberFuncIndex < t->memberFunctionArraySize;
	   memberFuncIndex++) {
	// Make sure that all of their parentClass fields point to t:
	VG_(printf)("memberFuncIndex: %u, t->memberFunctionArray[memberFuncIndex]: %p\n",
		    memberFuncIndex, t->memberFunctionArray[memberFuncIndex]);

	tl_assert(t->memberFunctionArray[memberFuncIndex]->parentClass == t);
      }
      VG_(printf)("After checking member functions\n");

      // Rep. check superclasses
      for (superclassIndex = 0;
           superclassIndex < t->superclassArraySize;
           superclassIndex++) {
        // Make sure that all Superclass entries have a className and
        // it matches the className of the corresponding TypeEntry:
        Superclass* curSuper = &(t->superclassArray[superclassIndex]);
        tl_assert(curSuper->className);
        tl_assert(curSuper->class);
        tl_assert(0 == VG_(strcmp)(curSuper->className, curSuper->class->collectionName));
        VG_(printf)("superclassIndex: %u, curSuper->className: %s, inheritance: %d\n",
                    superclassIndex, curSuper->className, curSuper->inheritance);
      }
    }
  }

  genfreeiterator(it);

  VG_(printf)("DONE\n");
}

// Checks rep. invariants for a VariableEntry (only performs general
// checks - additional checks are needed by the calling function if
// you want to really enforce stringent requirements)
static void repCheckOneVariable(VariableEntry* var) {
  tl_assert(var);

  // These properties should hold for all global vars:
  if (var->isGlobal) {
    tl_assert(0 == var->byteOffset);

    // Not true for C++ static member variables
    if (!var->isStructUnionMember) {
      tl_assert(var->fileName);
    }

    VG_(printf)(" --- checking var (t: %s) (%p): %s, globalLoc: %p\n",
		var->structParentType ? var->structParentType->collectionName : "no parent",
		var,
		var->name,
		var->globalLocation);

    if (var->globalLocation) {
      tl_assert(addressIsGlobal(var->globalLocation));
    }

    // These properties should hold for file-static variables declared
    // within a function body:
    if (var->functionStartPC) {
      tl_assert(!var->isExternal);
    }
  }
  // These properties should hold for all non-global vars:
  else {
    tl_assert(!var->isExternal);
    tl_assert(!var->fileName);
    tl_assert(0 == var->globalLocation);
    tl_assert(0 == var->functionStartPC);
  }

  // These properties hold for all variables:
  tl_assert(var->name);

  tl_assert(var->varType);

  if (var->isStaticArray) {
    tl_assert(var->numDimensions > 0);
    tl_assert(var->upperBounds);
  }

  if (var->isString) {
    tl_assert(D_CHAR == var->varType->decType);
    tl_assert(var->ptrLevels > 0);
  }

  if(var->isStructUnionMember) {
    tl_assert(var->structParentType);
  }
  else {
    tl_assert(!var->structParentType);
    tl_assert(0 == var->data_member_location);
    tl_assert(0 == var->internalByteSize);
    tl_assert(0 == var->internalBitOffset);
    tl_assert(0 == var->internalBitSize);
  }

  tl_assert(var->ptrLevels >= 0);

  // C++ reference vars should never have more than 1 level of
  // reference '&' right?
  tl_assert((var->referenceLevels == 0) ||
            (var->referenceLevels == 1));

  VG_(printf)(" --- DONE checking var (t: %s) (%p): %s, globalLoc: %p\n",
	      var->structParentType ? var->structParentType->collectionName : "no parent",
	      var,
	      var->name,
	      var->globalLocation);
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
    VG_(printf)( "Error, global variable information struct is null or belongs to the incorrect type\n");
    abort();
  }

  variablePtr = (variable*)(e->entry_ptr);
  typePtr = variablePtr->type_ptr;

  // If --ignore-static-vars, don't even let static variables
  // be CREATED in the first place!!!
  if (!variablePtr->is_external && fjalar_ignore_static_vars) {
    return;
  }

  extractOneVariable(&globalVars,
                     typePtr,
                     variablePtr->name,
		     findFilenameForEntry(e),
                     0,
                     variablePtr->couldBeGlobalVar,
		     variablePtr->is_external,
                     variablePtr->globalVarAddr,
		     functionStartPC,
		     0,0,0,0,0,0,0,0);

  FJALAR_DPRINTF("EXIT extractOneGlobalVariable(%p)\n", e);
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
static void initializeGlobalVarsList()
{
  UInt i;
  dwarf_entry* cur_entry = 0;

  // Create a hashtable with keys = {unsigned long (globalVarAddr), non-zero}
  //                   and values = {string which is the global variable name}
  struct genhashtable* GlobalVarsTable =
    genallocatehashtable((unsigned int (*)(void *)) &hashID,
			 (int (*)(void *,void *)) &equivalentIDs);

  FJALAR_DPRINTF("ENTER initializeGlobalVarsList() - %d\n",
		 dwarf_entry_array_size);

  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_variable(cur_entry->tag_name)) {
      variable* variable_ptr = (variable*)(cur_entry->entry_ptr);

      // IGNORE variables with is_declaration_or_artificial or
      // specification_ID active because these are empty shells!
      if (variable_ptr->couldBeGlobalVar &&
          variable_ptr->globalVarAddr &&
          (!variable_ptr->isStaticMemberVar) && // DON'T DEAL WITH C++ static member vars here;
                                                // We deal with them in extractStructUnionType()
          (!variable_ptr->specification_ID) &&
          (!variable_ptr->is_declaration_or_artificial)) {

	FJALAR_DPRINTF("dwarf_entry_array[%d] is a global named %s at addr: %p\n",
		       i, variable_ptr->name, variable_ptr->globalVarAddr);

	char* existingName;
	if (!variable_ptr->name) {
	  VG_(printf)( "Skipping weird unnamed global variable ID#%x - addr: %x\n",
		       cur_entry->ID, variable_ptr->globalVarAddr);
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
	  FJALAR_DPRINTF("Skipping silly glibc feature - %s\n",
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
	    FJALAR_DPRINTF("DUPLICATE! - %s\n", variable_ptr->name);
	    continue;
	  }
	}
	else {
	  genputtable(GlobalVarsTable,
		      (void*)variable_ptr->globalVarAddr, // key    (unsigned long)
		      (void*)variable_ptr->name);         // value  (char*)
	}

	// If a variable is truly a global variable, then
	// its dwarf_entry.level is 1 because it is not nested within
	// anything.  If dwarf_entry.level > 1, that means that this
	// is a static global variable declared within a function
	// so we should include the function name along with the filename
	// in front of the variable name:
	if (cur_entry->level > 1) {
	  extractOneGlobalVariable(cur_entry,
				   findFunctionStartPCForVariableEntry(cur_entry));
	}
	else {
	  extractOneGlobalVariable(cur_entry, 0);
	}
      }
    }
  }

  genfreehashtable(GlobalVarsTable);
}

// Initialize the names of unnamed structs so that we can have
// something to uniquely identify them with:
//
// For unnamed structs/unions/enums, we should just munge the
// name from the ID field so that we have something
// to use to identify this struct
// We will name it "unnamed_0x$ID" where $ID
// is the ID field in hex.
static void createNamesForUnnamedDwarfEntries()
{
  unsigned long i;
  dwarf_entry* cur_entry = 0;

  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_collection_type(cur_entry->tag_name)) {
      collection_type* collectionPtr = (collection_type*)(cur_entry->entry_ptr);
      if (!collectionPtr->is_declaration &&
          !collectionPtr->name) {
        //        VG_(printf)("%s (%u)\n", collectionPtr->name, cur_entry->ID);

        // The maximum size is 10 + 8 + 1 = 19 10 for "unnamed_0x", 8
        // for maximum size for cur_entry->ID, and 1 for
        // null-terminator
        char* fake_name = calloc(19, sizeof(*fake_name));
        sprintf(fake_name, "unnamed_0x%lx", cur_entry->ID);
        collectionPtr->name = fake_name;
      }
    }
  }
}

// TODO: This will leak memory if called more than once per program
// execution since the entries in FunctionTable are not being properly
// freed.  However, during normal execution, this should only be
// called once.

// After this function is called, the 'fjalar_name' field of all
// functions within FunctionTable should be initialized EXCEPT for C++
// function names which require demangling.  Demangling occurs in
// updateAllFunctionEntryNames() in fjalar_runtime.c
void initializeFunctionTable()
{
  unsigned long i;
  dwarf_entry* cur_entry = 0;
  FunctionEntry* cur_func_entry = 0;
  unsigned long num_functions_added = 0;

  FunctionTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashID,
                         (int (*)(void *,void *)) &equivalentIDs);

  for (i = 0; i < dwarf_entry_array_size; i++)
    {
      //      FJALAR_DPRINTF("i: %d\n", i);
      cur_entry = &dwarf_entry_array[i];
      // Ignore invalid functions and DUPLICATE function entries
      // with the same start_pc (only test if there is start_pc)
      if (entry_is_valid_function(cur_entry) &&
          ((((function*)cur_entry->entry_ptr)->start_pc) &&
           !gencontains(FunctionTable,
                        (void*)(((function*)cur_entry->entry_ptr)->start_pc))))
        {
          function* dwarfFunctionPtr = (function*)(cur_entry->entry_ptr);

          cur_func_entry = VG_(calloc)(1, sizeof(*cur_func_entry));

	  VG_(printf)("Adding function %s\n", dwarfFunctionPtr->name);

          cur_func_entry->name = dwarfFunctionPtr->name;
          cur_func_entry->mangled_name = dwarfFunctionPtr->mangled_name;
          cur_func_entry->filename = dwarfFunctionPtr->filename;
          cur_func_entry->accessibility = dwarfFunctionPtr->accessibility;

          cur_func_entry->startPC = dwarfFunctionPtr->start_pc;
          cur_func_entry->endPC = dwarfFunctionPtr->end_pc;

          cur_func_entry->isExternal = dwarfFunctionPtr->is_external;

          // Ok, here's the deal.  If cur_func_entry->mangled_name
          // exists, then we know that it's a C++ mangled function
          // name that requires demangling later at run-time in
          // updateAllFunctionEntryNames() (Valgrind's
          // demangler doesn't work at this point for some reason -
          // maybe it's too 'early' in the execution).  That function
          // will demangle mangled_name and turn it into a proper
          // Fjalar-approved name, so we don't have to initialize
          // fjalar_name right now.  So only generate fjalar_name
          // right now if there is no mangled name.
          if (!cur_func_entry->mangled_name) {
            char *the_class;
            char *buf, *p;

            if (dwarfFunctionPtr->is_external) {
              /* Globals print as "..main()", etc. */
              the_class = ".";
            } else {
              the_class = cur_func_entry->filename;
            }
            /* We want to print static_fn in subdir/filename.c
               as "subdir/filename.c.static_fn() */
            buf = VG_(malloc)(VG_(strlen)(the_class) + 1 +
                              VG_(strlen)(cur_func_entry->name) + 3);
            VG_(strcpy)(buf, the_class);
            for (p = buf; *p; p++) {
              if (!isalpha(*p) && !isdigit(*p) && *p != '.' && *p != '/'
                  && *p != '_')
                *p = '_';
            }
            VG_(strcat)(buf, ".");
            VG_(strcat)(buf, cur_func_entry->name);
            VG_(strcat)(buf, "()");
            cur_func_entry->fjalar_name = buf;
          }

          // This was formerly in extractTypeDataFromFunctionInfoArray():

          // Extract all formal parameter variables
          extractFormalParameterVars(cur_func_entry, dwarfFunctionPtr);

          // Extract all local array variables
          extractLocalArrayAndStructVariables(cur_func_entry, dwarfFunctionPtr);

          // Extract return variable
          extractReturnVar(cur_func_entry, dwarfFunctionPtr);

          // Make one more pass-through to make sure that byteOffsets are correct
          // for the word-aligned stack!
          // We must do this AFTER extracting the return variable
          verifyStackParamWordAlignment(cur_func_entry);

          // Add to FunctionTable
          genputtable(FunctionTable,
                      (void*)cur_func_entry->startPC, // key    (unsigned long)
		      (void*)cur_func_entry);         // value  (FunctionEntry*)
          num_functions_added++;
        }
    }

  if (!num_functions_added) {
    VG_(printf)( "\nError - No functions were found, probably due to a lack of debugging information.\n");
    VG_(printf)( "Did you compile your program with DWARF2 debugging info?  The option is -gdwarf-2 on gcc.\n");
    abort();
  }
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

  varPtr->isStaticArray = 1;
  varPtr->numDimensions = arrayDims;
  varPtr->upperBounds = VG_(calloc)(arrayDims,
			  sizeof(*(varPtr->upperBounds)));

  for (i = 0; i < arrayDims; i++) {
    array_subrange_type* subrangeEntry = (array_subrange_type*)
                                         (arrayPtr->subrange_entries[i]->entry_ptr);
    varPtr->upperBounds[i] = subrangeEntry->upperBound;
  }

  return arrayPtr->type_ptr;
}

// Extracts base type information by assigning var->varType to a basic
// type TypeEntry in BasicTypesArray
// Modifies: var->varType
static void extractBaseType(VariableEntry* var, base_type* basePtr)
{
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

    // TODO: Need to write a Kvasir/Fjalar function to scan over all
    // TypeEntry entries and map their declared types to rep. types
    // (which should run after TypesTable has been completely
    // initialized), then erase all mention of repType from this
    // file:
    //      t->repType = R_DOUBLE;
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
    else if (basePtr->byte_size == sizeof(long long int)) {
      var->varType = BasicTypesArray[D_LONG_LONG_INT];
    }

    //      t->repType = R_INT;
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
    else if (basePtr->byte_size == sizeof(unsigned long long int)) {
      var->varType = BasicTypesArray[D_UNSIGNED_LONG_LONG_INT];
    }

    //      t->repType = R_INT;
    break;

  case DW_ATE_boolean:
    var->varType = BasicTypesArray[D_BOOL];
    //      t->repType = R_INT;
    break;

  default:
    tl_assert(0 && "Unknown primitive type");
  }

  // Post-condition:
  tl_assert(IS_BASIC_TYPE(var->varType->decType));
}

// Extracts enumeration type info
// Modifies: t
static void extractEnumerationType(TypeEntry* t, collection_type* collectionPtr)
{
  t->decType = D_ENUMERATION;
  t->collectionName = collectionPtr->name;

  //  t->repType = R_INT;
  t->byteSize = sizeof(int); // An enumeration is an int
}


/* // Extracts subroutine type corresponding to a function pointer parameter */
/* // Modifies: t */
/* static void extractSubroutineType(TypeEntry* t, function_type* functionPtr) */
/* { */
/*   t->byteSize = 4; // TODO: Why does this only take up one byte? */
/*                    // Shouldn't it take up 4? */
/*   t->decType = D_FUNCTION; */
/*   //  t->repType = R_HASHCODE; */
/* } */

/* // Extracts type information from a void pointer */
/* // Modifies: t */
/* static void extractVoidType(TypeEntry* t) */
/* { */
/*   t->byteSize = 4; // TODO: Why does this only take up one byte? */
/*                    // Shouldn't it take up 4? */
/*   t->decType = D_VOID; */
/*   //  t->repType = R_HASHCODE; */
/* } */

// Extracts struct/union type info from collectionPtr and creates
// entries for member variables in t->memberVarList
// (DO NOT attempt to initialize t->memberFunctionArray right now
//  because FunctionTable has not been fully initialized yet, and
//  DO NOT attempt to initialize t->superclassArray right now
//  because TypesTable has not been fully initialized yet.)
static void extractStructUnionType(TypeEntry* t, dwarf_entry* e)
{
  collection_type* collectionPtr = 0;
  UInt i = 0, member_func_index = 0, superclass_index = 0;
  VarNode* memberNodePtr = 0;

  UShort numMemberFunctions = 0;
  UShort memberFunctionArrayIndex = 0;

  UShort numSuperclasses = 0;
  UShort superclassArrayIndex = 0;

  tl_assert((e->tag_name == DW_TAG_structure_type) ||
            (e->tag_name == DW_TAG_union_type));

  collectionPtr = (collection_type*)(e->entry_ptr);

  //  VG_(printf)("%s (dec: %u) (ID: %u)\n",
  //              collectionPtr->name,
  //              collectionPtr->is_declaration,
  //              e->ID);

  t->isStructUnionType = 1;
  //  t->repType = R_HASHCODE;

  if (e->tag_name == DW_TAG_union_type)
    t->decType = D_UNION;
  else
    t->decType = D_STRUCT;

  t->collectionName = collectionPtr->name;

  // This is a bit of a hack, but since FunctionTable probably hasn't
  // finished being initialized yet, we will fill up each entry in
  // t->memberFunctionArray with the start PC of the function, then
  // later in initMemberFuncs(), we will
  // use those start PC values to look up the actual FunctionEntry
  // entries using findFunctionEntryByStartAddr().  Thus, we
  // temporarily overload memberFunctionArray[] to hold start PC
  // pointer values.

  // First make a dry pass to determine how many functions we actually
  // have debug. info for, and try to fill in start_pc if necessary:
  for (member_func_index = 0;
       member_func_index < collectionPtr->num_member_funcs;
       member_func_index++) {
    function* funcPtr =
      (function*)((collectionPtr->member_funcs[member_func_index])->entry_ptr);

    VG_(printf)("  *** funcPtr->mangled_name: %s\n", funcPtr->mangled_name);

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

    VG_(printf)("         funcPtr->start_pc: %p\n", funcPtr->start_pc);

    // Success!
    numMemberFunctions++;
  }

  if (numMemberFunctions > 0) {
    t->memberFunctionArraySize = numMemberFunctions;
    t->memberFunctionArray = VG_(calloc)(numMemberFunctions,
                                         sizeof(*(t->memberFunctionArray)));

    VG_(printf)(" - numMemberFunctions: %d\n", numMemberFunctions);

    // Make the second pass to populate memberFunctionArray (The
    // conditions must PRECISELY match the previous pass or else we'll
    // have problems)
    for (member_func_index = 0;
         member_func_index < collectionPtr->num_member_funcs;
         member_func_index++) {
      function* funcPtr =
        (function*)((collectionPtr->member_funcs[member_func_index])->entry_ptr);
      // If we can't even find a start_pc, then just punt it:
      if (!funcPtr->start_pc) {
        continue;
      }

      // Success!
      // SUPER HACK!!! BE CAREFUL!!!
      t->memberFunctionArray[memberFunctionArrayIndex] = (FunctionEntry*)(funcPtr->start_pc);
      memberFunctionArrayIndex++;
    }
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
        VG_(printf)(" +++ super->name: %s\n", dwarf_super->name);
        numSuperclasses++;
      }
    }
  }

  // Now make a second pass and initialize superclassArray:
  if (numSuperclasses > 0) {
    t->superclassArraySize = numSuperclasses;
    t->superclassArray = (Superclass*)VG_(calloc)(numSuperclasses,
                                                  sizeof(*(t->superclassArray)));

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
          Superclass* curSuper = &(t->superclassArray[superclassArrayIndex]);
          curSuper->className = VG_(strdup)(dwarf_super->name);

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
          existing_entry = (TypeEntry*)gengettable(TypesTable,
                                                   (void*)curSuper->className);

          VG_(printf)("  [superclass] Try to find existing entry %p in TypesTable with name %s\n",
                      existing_entry, curSuper->className);

          if (existing_entry) {
            curSuper->class = existing_entry;
            // We are done!
          }
          // No entry exists for this name, so insert a new one:
          else {
            curSuper->class = (TypeEntry*)VG_(calloc)(1, sizeof(*(curSuper->class)));

            // Insert it into the table BEFORE calling
            // extractStructUnionType() or else we may infinitely
            // recurse!
            VG_(printf)("  Insert %s (superclass) into TypesTable\n", curSuper->className);
            genputtable(TypesTable,
                        (void*)curSuper->className,
                        curSuper->class);

            tl_assert((super_type_entry->tag_name == DW_TAG_structure_type) ||
                      (super_type_entry->tag_name == DW_TAG_union_type));

            VG_(printf)("  Doesn't exist ... trying to add class %s\n", curSuper->className);
            extractStructUnionType(curSuper->class, super_type_entry);
          }

          superclassArrayIndex++;
        }
      }
    }
  }

  t->memberVarList = (VarList*)VG_(calloc)(1, sizeof(*(t->memberVarList)));

  // Look up the dwarf_entry for the struct/union and iterate
  // through its member_vars array (of pointers to members)
  // in order to extract each member variable

  for (i = 0; i < collectionPtr->num_member_vars; i++) {
    member* memberPtr = (member*)((collectionPtr->member_vars[i])->entry_ptr);
    extractOneVariable(t->memberVarList,
                       memberPtr->type_ptr,
                       memberPtr->name,
                       0,
                       0,
                       0,
                       0,
                       0,
                       0,
                       1,
                       memberPtr->data_member_location,
                       memberPtr->internal_byte_size,
                       memberPtr->internal_bit_offset,
                       memberPtr->internal_bit_size,
                       t,
                       memberPtr->accessibility,
                       0);
  }


  VG_(printf)("t: %s, num_static_member_vars: %u\n",
	      t->collectionName,
	      collectionPtr->num_static_member_vars);

  // Extract static member variables into staticMemberVarList only if
  // there is at least 1 static member variable:
  if (collectionPtr->num_static_member_vars > 0) {
    unsigned long ind;

    t->staticMemberVarList =
      (VarList*)VG_(calloc)(1, sizeof(*(t->staticMemberVarList)));

    for (ind = 0; ind < collectionPtr->num_static_member_vars; ind++) {
      variable* staticMemberPtr =
	(variable*)((collectionPtr->static_member_vars[ind])->entry_ptr);

      // Try to find a global address in VariableSymbolTable if it
      // doesn't exist yet:
      if (!staticMemberPtr->globalVarAddr) {
        // Try the C++ mangled name:
        if (staticMemberPtr->mangled_name) {
          staticMemberPtr->globalVarAddr = (Addr)gengettable(VariableSymbolTable,
                                                             (void*)staticMemberPtr->mangled_name);
        }
      }

      VG_(printf)("Trying to extractOneVariable on static member var: %s at %p\n",
		  staticMemberPtr->mangled_name,
		  staticMemberPtr->globalVarAddr);

      extractOneVariable(t->staticMemberVarList,
			 staticMemberPtr->type_ptr,
			 (staticMemberPtr->mangled_name ?  // TODO: demangle this later
			  staticMemberPtr->mangled_name :
			  staticMemberPtr->name),
			 0,
			 0,
			 1,
			 staticMemberPtr->is_external,
			 staticMemberPtr->globalVarAddr,
			 0,
			 1, 0, 0, 0, 0,
			 t,
                         staticMemberPtr->accessibility,
			 0);

      FJALAR_DPRINTF("Finished Trying to extractOneVariable on member var: %s\n",
		     staticMemberPtr->mangled_name);
    }
  }

  // After we are doing constructing the struct TypeEntry entry,
  // we must initialize the struct byte size:

  // To calculate the byte size of the struct, we look at the
  // data_member_location of the last member and add its byte size
  // (if member is actually a struct type, then its byte size should already
  //  have been computed by the recursive version of this call to that struct)
  // - Round struct size up to the nearest word (multiple of 4)
  memberNodePtr = t->memberVarList->last;
  if (memberNodePtr)
    {
      int structByteSize = 0;
      VariableEntry* memberVarPtr = memberNodePtr->var;
      structByteSize = memberVarPtr->data_member_location +
	determineVariableByteSize(memberVarPtr);

      // Round struct size up to the nearest word (multiple of 4)
      t->byteSize = ((structByteSize + 3) >> 2) << 2;

      FJALAR_DPRINTF("collection name: %s, byteSize: %d\n", t->collectionName, t->byteSize);
    }
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

  FJALAR_DPRINTF("extractLocalArrayAndStructVariables - %s (#: %u)\n",
	 dwarfFunctionEntry->name, dwarfFunctionEntry->num_local_vars);

  // No local variables - don't do anything
  if (!dwarfFunctionEntry->num_local_vars)
    return;

  for (i = 0; i < dwarfFunctionEntry->num_local_vars; i++)
    {
      FJALAR_DPRINTF("%s - local_vars: %d of %d\n", dwarfFunctionEntry->name, i+1, dwarfFunctionEntry->num_local_vars);
      extractOneLocalArrayOrStructVariable(f,
                                           dwarfFunctionEntry->local_vars[i]);
    }

  FJALAR_DPRINTF("DONE extractLocalArrayAndVariables - %s\n",
	  dwarfFunctionEntry->name);
}

// MUST BE RUN AFTER the return value for a function has been initialized!!!
// Otherwise it cannot tell whether the function returns a struct type!!!
//
// We are ignoring the offsets that DWARF2 provides for us because when
// Valgrind gains control at the beginning of a function, the parameters
// are not guaranteed to be at those locations yet -
// We have devised our own calculation that word-aligns everything.
static void verifyStackParamWordAlignment(FunctionEntry* f)
{
  VarNode* cur_node;
  int offset = 8;

  FJALAR_DPRINTF("ENTER verifyStackParamWordAlignment(%s): %p\n",
		 f->fjalar_name, f->returnValue.first);

  // Start with default offset of 8 from EBP (*EBP = old EBP, *(EBP+4) = return addr)
  // unless the function returns a struct by value - then we start
  // with an offset of 12 since *(EBP+8) = pointer to the place to put the struct)

  VarNode* firstNode = f->returnValue.first;
  if (firstNode) {
    VariableEntry* firstReturnVar = firstNode->var;
    // See if the function seturn a struct by value:
    if (firstReturnVar &&
	(D_STRUCT == firstReturnVar->varType->decType) &&
	(0 == firstReturnVar->ptrLevels)) {
      offset = 12;
    }
  }

  for (cur_node = f->formalParameters.first;
       cur_node != NULL;
       cur_node = cur_node->next)
    {
      int cur_byteSize = 0;
      cur_node->var->byteOffset = offset;
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
  else if (var->isStaticArray)
    {
      int i;

      if (var->ptrLevels == 1) {
        byteSize = var->varType->byteSize; // static array of base type
      }
      else if (var->ptrLevels > 1) {
        byteSize = sizeof(void*); // static array of pointers
      }

      for (i = 0; i < var->numDimensions; i++) {
        FJALAR_DPRINTF("  upperBounds[%d] = %d\n", i, var->upperBounds[i]);
        byteSize *= (var->upperBounds[i] + 1);
      }
    }
  // Pointer type
  else {
    byteSize = sizeof(void*);
  }

  FJALAR_DPRINTF("detDVBS | name: %s, decPtrLvls: %d, isSA: %d, byteSize: %d, return: %d\n",
          var->name, var->ptrLevels, var->isStaticArray, var->varType->byteSize, byteSize);

  return byteSize;
}


// Determines the number of bytes needed above EBP in the stack
// to hold the values of all function formal parameters for
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
      // Assuming that we have already run verifyStackParamWordAlignment,
      // the byteOffset field of every cur_node->var should be updated
      // and all we have to do is to collect byteOffset + byteSize of
      // the LAST formal parameter in order to find the total required stack size.
      // So we will be lazy and just assign totalByteSize to byteOffset + byteSize
      // of EVERY formal parameter since we know that the last one we hit
      // will have the highest value.
      totalByteSize = (cur_node->var->byteOffset +
                       determineVariableByteSize(cur_node->var));
      // Just to be safe, round UP to the next multiple of 4
      totalByteSize += 4;
      totalByteSize -= (totalByteSize % 4);
    }
  return totalByteSize;
}


// dwarfParamEntry->tag_name == DW_TAG_formal_parameter
static void extractOneFormalParameterVar(FunctionEntry* f,
                                         dwarf_entry* dwarfParamEntry)
{
  formal_parameter* paramPtr = 0;
  dwarf_entry* typePtr = 0;

  if (dwarfParamEntry == NULL || !tag_is_formal_parameter(dwarfParamEntry->tag_name)) {
    VG_(printf)( "Error, formal parameter information struct is null or belongs to the incorrect type\n");
    abort();
  }

  paramPtr = (formal_parameter*)(dwarfParamEntry->entry_ptr);
  typePtr = paramPtr->type_ptr;

  if (!paramPtr->name) {
    VG_(printf)( "Unexpected unnamed parameter in %s\n",
            f->name);
    return;
  }

  FJALAR_DPRINTF("  %s parameter name %s\n",
	  f->name,
	  paramPtr->name);

  extractOneVariable(&(f->formalParameters),
                     typePtr,
		     paramPtr->name,
		     0,
                     paramPtr->location,
                     0,
		     0,
		     0,
		     0,
		     0,0,0,0,0,0,0,1);
}

static void extractFormalParameterVars(FunctionEntry* f,
				       function* dwarfFunctionEntry)
{
  UInt i;

  FJALAR_DPRINTF("extractFormalParameterVars - %s (#: %u)\n",
	 dwarfFunctionEntry->name, dwarfFunctionEntry->num_formal_params);

  // No formal parameters - don't do anything
  if (!dwarfFunctionEntry->num_formal_params)
    return;

  for (i = 0; i < dwarfFunctionEntry->num_formal_params; i++)
    {
      extractOneFormalParameterVar(f, dwarfFunctionEntry->params[i]);
    }
}


// Only adds a new entry if dwarfVariableEntry's type ==
// DW_TAG_array_type or struct or union type:
static void extractOneLocalArrayOrStructVariable(FunctionEntry* f,
						 dwarf_entry* dwarfVariableEntry)
{
  variable* variablePtr = 0;
  dwarf_entry* typePtr = 0;

  if (dwarfVariableEntry == NULL || !tag_is_variable(dwarfVariableEntry->tag_name)) {
    VG_(printf)( "Error, local variable information struct is null or belongs to the incorrect type\n");
    abort();
  }

  variablePtr = (variable*)(dwarfVariableEntry->entry_ptr);
  typePtr = variablePtr->type_ptr;

  // Only store array types and struct/union types!
  // Also, don't store anything with couldBeGlobalVar == true
  // because that means that it's a static variable.
  // static variables have global scope so they can be picked up
  // by the sweep of the global variables
  if (!(tag_is_array_type(typePtr->tag_name) ||
	(DW_TAG_structure_type == typePtr->tag_name) ||
	(DW_TAG_union_type == typePtr->tag_name)) ||
      variablePtr->couldBeGlobalVar) {
    return;
  }

  if (!variablePtr->name) {
    VG_(printf)( "Unexpected unnamed local variable in %s\n",
            f->name);
    return;
  }

  FJALAR_DPRINTF("  %s local variable name %s - localArrayAndStructVars %p size = %d\n",
		 f->name,
		 variablePtr->name,
		 &(f->localArrayAndStructVars),
		 f->localArrayAndStructVars.numVars);

  extractOneVariable(&(f->localArrayAndStructVars),
                     typePtr,
                     variablePtr->name,
		     0,
                     variablePtr->offset,
                     0,
		     0,
		     0,
		     0,
		     0,0,0,0,0,0,0,0);
}

static void extractReturnVar(FunctionEntry* f,
			     function* dwarfFunctionEntry)
{
  // Get the return value type
  dwarf_entry* typePtr = dwarfFunctionEntry->return_type;

  FJALAR_DPRINTF("extractReturnVar - %s\n",
	  dwarfFunctionEntry->name);

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
		     0,0,0,0,0,0,0,0);
}



// Scan through varsToUpdateTypes, look at the varType entries, look
// them up in TypesTable, replace the entries with the real versions,
// and free the faux TypeEntry:
void updateAllVarTypes() {
  VarNode* n;

  if (0 == varsToUpdateTypes.numVars) {
    return;
  }

  for (n = varsToUpdateTypes.first;
       n != NULL;
       n = n->next) {
    VariableEntry* var = n->var;
    TypeEntry* fake_type = var->varType;
    TypeEntry* real_type = 0;

    tl_assert(fake_type->collectionName);

    real_type = (TypeEntry*)gengettable(TypesTable,
                                        (void*)(fake_type->collectionName));
    tl_assert(real_type);
    var->varType = real_type;

    // Remember to free this!
    VG_(free)(fake_type);
  }

  // Remember to destroy this list now that we're done with it!
  clearVarList(&varsToUpdateTypes);
}


// Extracts one variable and inserts it at the end of varListPtr
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
			TypeEntry* structParentType,
                        unsigned long dwarf_accessibility,
                        char isFormalParam) // All static arrays which are
// formal parameters are treated like NORMAL pointers which are not statically-sized
// just because that's how the C language works
{
  VariableEntry* varPtr = 0;
  char ptrLevels = 0;
  char referenceLevels = 0;

  VG_(printf)("Entering extractOneVariable for %s\n", variableName);

  // Don't extract the variable if it has a bogus name:
  if (ignore_variable_with_name(variableName))
    return;

  // Create a new VariableEntry and append it to the end of VarList
  insertNewNode(varListPtr);

  // Work on the last variable in varListPtr
  varPtr = varListPtr->last->var;

  varPtr->name = variableName;
  varPtr->fileName = fileName;
  varPtr->byteOffset = byteOffset;

  // Special case for C++ 'this' parameter variables:
  // Automatically put a 'P' disambig on it because
  // 'this' will always refer to one object and not an array

  // TODO: This will simple-mindedly pick up any variable named 'this'
  // so it's possible that in a C program, you can have some variable
  // named 'this' and it'll get a 'P' disambig letter assigned to it
  if (VG_STREQ("this", variableName)) {
    varPtr->disambig = 'P';
  }

  varPtr->isGlobal = isGlobal;
  varPtr->isExternal = isExternal;
  varPtr->globalLocation = globalLocation;
  varPtr->functionStartPC = functionStartPC;

  varPtr->isStructUnionMember = isStructUnionMember;
  varPtr->data_member_location = data_member_location;
  varPtr->internalByteSize = internalByteSize;
  varPtr->internalBitOffset = internalBitOffset;
  varPtr->internalBitSize = internalBitSize;
  varPtr->structParentType = structParentType;

  // Figure out varPtr->visibility:
  switch (dwarf_accessibility) {
  case DW_ACCESS_private:
    varPtr->visibility = PRIVATE_VISIBILITY;
    break;
  case DW_ACCESS_protected:
    varPtr->visibility = PROTECTED_VISIBILITY;
    break;
  case DW_ACCESS_public:
  default:
    varPtr->visibility = PUBLIC_VISIBILITY;
  }

  FJALAR_DPRINTF("About to strip modifiers for %s\n", variableName);

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

  FJALAR_DPRINTF("Finished stripping modifiers for %s\n", variableName);
  FJALAR_DPRINTF("varPtr is %p\n", varPtr);
  FJALAR_DPRINTF("typePtr is %p\n", typePtr);

  varPtr->ptrLevels = ptrLevels;
  varPtr->referenceLevels = referenceLevels;

  if (typePtr && (typePtr->tag_name == DW_TAG_structure_type)) {
    char* type_name = ((collection_type*)(typePtr->entry_ptr))->name;
    // We want to ignore POINTERS to certain types (don't ignore
    // the actual values of that type because it may screw up alignments).
    // Instead, we want to convert these into generic void pointers.
    if ((varPtr->ptrLevels > 0) &&
        ignore_type_with_name(type_name)) {
      //      VG_(printf)("IGNORED --- %s\n", type_name);
      varPtr->varType = &VoidType;
      return; // punt at this point
    }
  }

  // Formal parameters which appear to be statically-sized arrays are
  // actually simply pointers:
  if (isFormalParam && varPtr->isStaticArray) {
    varPtr->isStaticArray = 0;
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
      TypeEntry* fake_entry = VG_(calloc)(1, sizeof(*fake_entry));

      fake_entry->collectionName = collectionPtr->name;

      varPtr->varType = fake_entry;
      insertNewNode(&varsToUpdateTypes);
      varsToUpdateTypes.last->var = varPtr;

      VG_(printf)("  Inserted *fake* entry for variable %s with type %s\n",
                  variableName, collectionPtr->name);
    }
    // Otherwise, try to find an entry in TypesTable if one already exists
    else {
      TypeEntry* existing_entry = (TypeEntry*)gengettable(TypesTable,
                                                          (void*)collectionPtr->name);

      VG_(printf)("  Try to find existing entry %p in TypesTable with name %s\n",
                  existing_entry, collectionPtr->name);

      if (existing_entry) {
        VG_(printf)("  Using existing type entry for %s\n", variableName);
        varPtr->varType = existing_entry;
        // We are done!
      }
      // No entry exists for this name, so insert a new one:
      else {
        VG_(printf)("  Adding type entry for %s\n", variableName);

        varPtr->varType = (TypeEntry*)VG_(calloc)(1, sizeof(*varPtr->varType));

        // Insert it into the table BEFORE calling
        // extractStructUnionType() or else we may infinitely recurse!
        VG_(printf)("  Insert %s into TypesTable\n", collectionPtr->name);
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
                  (typePtr->tag_name == DW_TAG_union_type)) {
          extractStructUnionType(varPtr->varType, typePtr);
        }
      }
    }
  }

  // Set isString to true if the variable is a pointer to a char (or a
  // pointer to a pointer to a char, etc...)
  if ((varPtr->varType->decType == D_CHAR) &&
      (varPtr->ptrLevels > 0)) {
    varPtr->isString = 1;
  }

  // TODO: What about arrays of pointers?  int* [10] currently turns
  // into base type = int, ptrLevels = 2, isStaticArray = true
  // but it should be base type = hashcode, ptrLevels = 1, isStaticArray = true

  // Proposed solution: If isStaticArray = true and (ptrLevels > 1 and
  // varPtr->varType->decType != D_CHAR) or (ptrLevels > 2 and
  // varPtr->varType->decType == D_CHAR), then
  // we turn it into a 1-D array of hashcodes by setting ptrLevels = 1
  // and pointing the type to VoidType.
  // This means that we do not support multidimensional arrays
  // (but we didn't used to either) but fail more gracefully on them now
  if (varPtr->isStaticArray &&
      (ptrLevels > ((varPtr->varType->decType == D_CHAR) ?
                    2 : 1))) {
    varPtr->ptrLevels = 1;
    varPtr->varType = &VoidType;
  }
}


// FunctionTable - hash table containing FunctionEntry entries

// Super-trivial division hashing method - do nothing.  We could
// improve upon this to increase efficiency, but it's ok for now
unsigned int hashID(int ID) {
  return ID;
}

// Super-trivial key comparison method -
int equivalentIDs(int ID1, int ID2) {
  return (ID1 == ID2);
}

// More C++ fun.  So apparently constructors and destructors are
// printed in the DWARF debugging information as regular functions,
// not member functions.  Thus, the only reasonable way to infer that
// a function is a constructor or a destructor is to pattern match the
// names of functions to names of types in TypesTable.
static void initConstructorsAndDestructors() {
  struct geniterator* it = gengetiterator(FunctionTable);
  // Iterate through all entries in TypesTable:
  while (!it->finished) {
    FunctionEntry* f = (FunctionEntry*)
      gengettable(FunctionTable, gennext(it));

    // Here are our pattern-matching heuristics:

    // A function is a constructor iff:
    // 1.) Its name matches the name of a type in TypesTable
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

      // Use the regular (not mangled or demangled) name for matching
      tl_assert(f->name);

      // See if it's a constructor:
      parentClass = (TypeEntry*)gengettable(TypesTable,
                                            (void*)f->name);

      if (parentClass) {
        VG_(printf)(" *** CONSTRUCTOR! func-name: %s\n", f->name);
        f->parentClass = parentClass;
      }
      // See if it's a destructor
      else if ('~' == f->name[0]) {
        // Notice how we skip forward one letter to cut off the '~':
        parentClass = (TypeEntry*)gengettable(TypesTable,
                                              (void*)(&(f->name[1])));

        if (parentClass) {
          VG_(printf)(" *** DESTRUCTOR! func-name: %s\n", f->name);
          f->parentClass = parentClass;
        }
      }
    }
  }

  genfreeiterator(it);
}

// Initializes all member functions for structs in TypesTable.
// Pre: This should only be run after TypesTable and FunctionTable
// have been initialized.
static void initMemberFuncs() {
  struct geniterator* it = gengetiterator(TypesTable);
  // Iterate through all entries in TypesTable:
  while (!it->finished) {
    TypeEntry* t = (TypeEntry*)
      gengettable(TypesTable, gennext(it));

    // Only do this for struct/union types:
    if ((t->decType == D_STRUCT) ||
        (t->decType == D_UNION)) {
      // This is a bit of a hack, but in extractStructUnionType(), we
      // initialized the entries of t->memberFunctionArray with the
      // start PC of the member functions (we had to do this because
      // FunctionTable wasn't initialized at that time).  Thus, we
      // temporarily overload memberFunctionArray[] to hold start PC
      // pointer values.  Now we will iterate over those values and
      // use findFunctionEntryByStartAddr() to try to fill them in
      // with actual FunctionEntry instances:
      UShort i;

      for (i = 0; i < t->memberFunctionArraySize; i++) {
        FunctionEntry** pCurMemberFunc = &t->memberFunctionArray[i];
        unsigned int start_PC = (unsigned int)(*pCurMemberFunc);
        tl_assert(start_PC);

        VG_(printf)("  hacked start_pc: %p - parentClass = %s\n", start_PC, t->collectionName);

        // Hopefully this will always be non-null
        *pCurMemberFunc = findFunctionEntryByStartAddr(start_PC);
        tl_assert(*pCurMemberFunc);
        // Very important!  Signify that it's a member function
        (*pCurMemberFunc)->parentClass = t;
      }
    }
  }

  genfreeiterator(it);
}


// FunctionTable

// This is SLOW because we must traverse all values,
// looking for the fjalar_name
FunctionEntry* findFunctionEntryByFjalarNameSlow(char* fjalar_name) {
  struct geniterator* it = gengetiterator(FunctionTable);
  FunctionEntry* entry = 0;

  while (!it->finished) {
    entry = (FunctionEntry*)
      gengettable(FunctionTable, gennext(it));

    if (!entry)
      continue;

    if (VG_STREQ(entry->fjalar_name, fjalar_name)) {
      genfreeiterator(it);
      return entry;
    }
  }

  genfreeiterator(it);
  return 0;
}

// This is SLOW because we must traverse all values
// looking for an entry whose startPC and endPC encompass the
// desired address addr, inclusive.  Thus addr is in the range of
// [startPC, endPC]
FunctionEntry* findFunctionEntryByAddrSlow(unsigned int addr) {
  struct geniterator* it = gengetiterator(FunctionTable);
  FunctionEntry* entry = 0;

  while (!it->finished) {

    entry = (FunctionEntry*)
      gengettable(FunctionTable, gennext(it));

    if (!entry)
      continue;

    if ((entry->startPC <= addr) &&
        (addr <= entry->endPC)) {
      genfreeiterator(it);
      return entry;
    }
  }
  genfreeiterator(it);
  return 0;
}

// This is FAST because the keys of the hash table are addresses
// startPC must match the starting address of the function
__inline__ FunctionEntry* findFunctionEntryByStartAddr(unsigned int startPC) {
  return (FunctionEntry*)gengettable(FunctionTable, (void*)startPC);
}


// Iterate thru all chars, sum up each (ASCII value * (index + 1))
// Don't worry about modding because GenericHashtable.c will do it for us :)
unsigned int hashString(char* str) {
  int i;
  int sum = 0;
  int len = VG_(strlen)(str);
  for (i = 0; i < len; i++) {
    sum += ((int)(str[i]) * (i + i));
  }

  return sum;
}

int equivalentStrings(char* str1, char* str2) {
  return VG_STREQ(str1, str2);
}


// Returns the first TypeEntry entry found in TypesTable with
// collectionName matching the given name, and return 0 if nothing
// found.
__inline__ TypeEntry* findTypeEntryByName(char* name) {
  return (TypeEntry*)gengettable(TypesTable, (void*)name);
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
  fclose(xml_output_fp);
}

// Format things slightly differently for member functions:
static void XMLprintOneFunction(FunctionEntry* cur_entry, char isMemberFunc) {

  XML_PRINTF("<function");
  // Add function attributes:
  if (isMemberFunc) {
    XML_PRINTF(" type=\"");
    switch (cur_entry->accessibility) {
    case DW_ACCESS_private:
      XML_PRINTF("private-member-function");
      break;
    case DW_ACCESS_protected:
      XML_PRINTF("protected-member-function");
    break;
    default:
      XML_PRINTF("public-member-function");
      break;
    }
    XML_PRINTF("\"");
  }
  else if (!cur_entry->isExternal) {
    XML_PRINTF(" type=\"file-static\"");
  }
  XML_PRINTF(">\n");

  if (cur_entry->name) {
    XML_PRINTF("<name>%s</name>\n",
               cur_entry->name);
  }

  if (cur_entry->fjalar_name) {
    XML_PRINTF("<fjalar-name>%s</fjalar-name>\n",
               cur_entry->fjalar_name);
  }

  XML_PRINTF("<start-PC>%p</start-PC>\n",
             (void*)cur_entry->startPC);
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
  struct geniterator* it = gengetiterator(FunctionTable);

  XML_PRINTF("<function-declarations>\n");

  while (!it->finished) {
    FunctionEntry* cur_entry = (FunctionEntry*)
      gengettable(FunctionTable, gennext(it));

    if (!cur_entry) {
      continue;
    }

    // DO NOT print out C++ member functions here.  Instead, print
    // them out as part of the <type> entry
    if (cur_entry->parentClass) {
      continue;
    }

    XMLprintOneFunction(cur_entry, 0);
  }

  XML_PRINTF("</function-declarations>\n");

  genfreeiterator(it);
}

static void XMLprintTypesTable() {
  struct geniterator* it = gengetiterator(TypesTable);

  XML_PRINTF("<type-declarations>\n");

  while (!it->finished) {
    TypeEntry* cur_entry = (TypeEntry*)
      gengettable(TypesTable, gennext(it));

    if (!cur_entry) {
      continue;
    }

    XML_PRINTF("<type>\n");

    if (cur_entry->collectionName) {
      XML_PRINTF("<type-name>%s</type-name>\n",
		 cur_entry->collectionName);
    }

    XML_PRINTF("<byte-size>%d</byte-size>\n",
	       cur_entry->byteSize);

    XML_PRINTF("<declared-type>%s</declared-type>\n",
	       DeclaredTypeNames[cur_entry->decType]);

    if (cur_entry->isStructUnionType) {
      unsigned int i;

      if (cur_entry->memberVarList &&
          (cur_entry->memberVarList->numVars > 0)) {
        XML_PRINTF("<member-variables>\n");
        XMLprintVariablesInList(cur_entry->memberVarList);
        XML_PRINTF("</member-variables>\n");
      }

      if (cur_entry->staticMemberVarList &&
          (cur_entry->staticMemberVarList->numVars > 0)) {
        XML_PRINTF("<static-member-variables>\n");
        XMLprintVariablesInList(cur_entry->staticMemberVarList);
        XML_PRINTF("</static-member-variables>\n");
      }

      if (cur_entry->memberFunctionArraySize > 0) {
        XML_PRINTF("<member-functions>\n");
        for (i = 0; i < cur_entry->memberFunctionArraySize; i++) {
          XMLprintOneFunction(cur_entry->memberFunctionArray[i], 1);
        }
        XML_PRINTF("</member-functions>\n");
      }

      for (i = 0; i < cur_entry->superclassArraySize; i++) {
        XML_PRINTF("<superclass ");

        switch(cur_entry->superclassArray[i].inheritance) {
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

        XML_PRINTF(" member-var-offset=\"%u\"",
                   cur_entry->superclassArray[i].member_var_offset);

        XML_PRINTF(">%s</superclass>\n",
                   cur_entry->superclassArray[i].className);
      }
    }

    XML_PRINTF("</type>\n");
  }

  XML_PRINTF("</type-declarations>\n");

  genfreeiterator(it);
}

static void XMLprintVariablesInList(VarList* varListPtr) {
  VarNode* curNode;

  if (!varListPtr) {
    return;
  }

  for (curNode = varListPtr->first;
       curNode != 0;
       curNode = curNode->next) {
    XMLprintOneVariable(curNode->var);
  }
}

// Prints one VariableEntry
static void XMLprintOneVariable(VariableEntry* var) {
  TypeEntry* t;

  if (!var) {
    return;
  }

  t = var->varType;

  XML_PRINTF("<variable>\n");

  XML_PRINTF("<name>%s</name>\n", var->name);

  if (var->isGlobal) {
    XML_PRINTF("<global-var>\n");

    XML_PRINTF("<location>%p</location>\n",
	       (void*)var->globalLocation);

    if (var->fileName) {
      XML_PRINTF("<filename>%s</filename>\n",
                 var->fileName);
    }

    if (!var->isExternal) {
      XML_PRINTF("<file-static-var>\n");

      if (var->functionStartPC) {
	XML_PRINTF("<function-start-PC>%p</function-start-PC>\n",
		   (void*)var->functionStartPC);
      }

      XML_PRINTF("</file-static-var>\n");
    }

    XML_PRINTF("</global-var>\n");
  }

  if (var->byteOffset) {
    XML_PRINTF("<stack-byte-offset>%d</stack-byte-offset>\n",
	       var->byteOffset);
  }

  if (var->isStaticArray) {
    int i = 0;

    XML_PRINTF("<static-array>\n");

    XML_PRINTF("<num-dimensions>%d</num-dimensions>\n",
	       var->numDimensions);

    for (i = 0; i < var->numDimensions; i++) {
      XML_PRINTF("<upper-bound>%u</upper-bound>\n",
		 var->upperBounds[i]);
    }

    XML_PRINTF("</static-array>\n");
  }

  if (var->isStructUnionMember) {
    XML_PRINTF("<member-var visibility=\"");
    switch(var->visibility) {
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
	       var->data_member_location);

    XML_PRINTF("<parent-type>%s</parent-type>\n",
	       var->structParentType->collectionName);

    XML_PRINTF("</member-var>\n");
  }

  if (t) {
    XML_PRINTF("<var-type");

    if (var->ptrLevels > 0) {
      XML_PRINTF(" pointer-levels=\"%d\"", var->ptrLevels);
    }
    if (var->referenceLevels > 0) {
      XML_PRINTF(" reference-levels=\"%d\"", var->referenceLevels);
    }
    if (var->isString) {
      XML_PRINTF(" is-string=\"true\"");
    }

    XML_PRINTF(">\n");

    XML_PRINTF("<declared-type>%s</declared-type>\n",
	       DeclaredTypeNames[t->decType]);
    XML_PRINTF("<byte-size>%d</byte-size>\n",
	       t->byteSize);

    if (t->collectionName) {
      XML_PRINTF("<type-name>%s</type-name>\n",
		 t->collectionName);
    }

    XML_PRINTF("</var-type>\n");
  }

  XML_PRINTF("</variable>\n");
}
