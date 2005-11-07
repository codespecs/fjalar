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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include "generate_fjalar_entries.h"
#include "elf/dwarf2.h"
#include "tool.h"
#include "GenericHashtable.h"

#include "fjalar_tool.h"

//#include "kvasir_main.h"
//#include "decls-output.h"

static void initializeStructNamesIDTable();
static void initializeFunctionTable();
static void initializeGlobalVarsList();
static void initializeAllClassMemberFunctions();

static int determineVariableByteSize(VariableEntry* var);

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
                               char isFormalParam);


// A sentinel for a void* type
TypeEntry GlobalHashcodeType = {0,             // collectionName
                                D_VOID,        // decType
                                sizeof(void*), // byteSize
                                0, 0, 0, 0};

// Hash table that maps the names of structs to their ID's in
// dwarf_entry_array
// (This is needed to make sure that there is only one entry of
//  each struct with a certain name that all variables can refer to.
//  Otherwise, lots of variables may refer to entries that are merely
//  empty declarations in their compilation unit.)
// Key: name of struct type
// Value: ID of REAL entry where is_declaration is 0
static struct genhashtable* StructNamesIDTable = 0;

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
      (0 == VG_(strncmp)(name, "_GLOBAL", 7)))
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

  // TODO: We need to free up the entries in TypesTable and
  // StructNamesIDTable if we are really trying to be robust

  VisitedStructsTable = 0;

  DPRINTF("About to allocate hash table\n");

  // Initialize TypesTable
  TypesTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashID,
                         (int (*)(void *,void *)) &equivalentIDs);

  StructNamesIDTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  initializeStructNamesIDTable();

  initializeFunctionTable();

  // Don't even bother to init this if we set --ignore-globals
  if (!ignore_globals) {
    initializeGlobalVarsList();
  }

  initializeAllClassMemberFunctions();

  genfreehashtable(StructNamesIDTable);
  StructNamesIDTable = 0;
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

      DPRINTF("Skipping invalid-looking function %s\n", funcPtr->name);

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
// functionStartPC is the name of the function that this variable belongs to
static void extractOneGlobalVariable(dwarf_entry* e, unsigned long functionStartPC)
{
  variable* variablePtr = 0;
  dwarf_entry* typePtr = 0;

  if (e == NULL || !tag_is_variable(e->tag_name)) {
    VG_(printf)( "Error, global variable information struct is null or belongs to the incorrect type\n");
    abort();
  }

  variablePtr = (variable*)(e->entry_ptr);
  typePtr = variablePtr->type_ptr;

  // If --ignore-static-vars, don't even let static variables
  // be CREATED in the first place!!!
  if (!variablePtr->is_external && kvasir_ignore_static_vars) {
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
		     0,0,0,0,0,0,0);
}

// Initializes the global variables list (globalVars) and fills it up
// with global variable entries from dwarf_entry_array.
// Also initializes lowestGlobalVarAddr and highestGlobalVarAddr

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
  VarNode* node = 0;
  VariableEntry* maxGlobalVar = 0;
  VariableEntry* currentVar = 0;
  VariableEntry* minGlobalVar = 0;

  // Create a hashtable with keys = {unsigned long (globalVarAddr), non-zero}
  //                   and values = {string which is the global variable name}
  struct genhashtable* GlobalVarsTable =
    genallocatehashtable((unsigned int (*)(void *)) &hashID,
			 (int (*)(void *,void *)) &equivalentIDs);

  DPRINTF("Entering initializeGlobalVarsList()\n");

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
	char* existingName;
	if (!variable_ptr->name) {
	  VG_(printf)( "Skipping weird unnamed global variable ID#%x - addr: %x\n", cur_entry->ID, variable_ptr->globalVarAddr);
	  continue;
	} else if (!VG_(strcmp)(variable_ptr->name, "_IO_stdin_used")) {
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
	  continue;
	}
	// This is the part where we do not add duplicates. We first look
	// up to see whether variable_ptr->globalVarAddr is non-null and
	// in GlobalVarsTable. If it is already in the table, we get the value
	// for that entry and compare it with the name of variable_ptr. If
	// both globalVarAddr and name match, then we have a duplicate entry
	// so we don't add the new entry to the globalVars list. However, if
	// the variable is not yet in GlobalVarsTable, then we add it to
	// the table and proceed with adding it to the globalVars list.
	existingName = 0;
	if ((0 != variable_ptr->globalVarAddr) &&
	    ((existingName =
	      gengettable(GlobalVarsTable, (void*)variable_ptr->globalVarAddr)))) {
	  if VG_STREQ(variable_ptr->name, existingName) {
	    //	    printf("DUPLICATE! - %s\n", variable_ptr->name);
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

  // Now that globalVars is all initialized,
  // calculate the highestGlobalVarAddr and lowestGlobalVarAddr values:

  // Find the minimum and maximum global addresses
  maxGlobalVar = &(globalVars.first->var);
  minGlobalVar = &(globalVars.first->var);

  if (globalVars.numVars > 0)
    {
      for (node = globalVars.first; node != 0; node = node->next)
	{
	  currentVar = &(node->var);
	  // (Deprecated: Only count real global variables)
          // Wait, don't static variables get placed in the globals
          // section also?  We should count those too:
          //	  if (currentVar->isGlobal)
          if (currentVar->globalLocation)
	    {
	      if (currentVar->globalLocation < minGlobalVar->globalLocation)
		{
		  minGlobalVar = currentVar;
		}
	      if (currentVar->globalLocation > maxGlobalVar->globalLocation)
		{
		  maxGlobalVar = currentVar;
		}
	    }
	}

      highestGlobalVarAddr = maxGlobalVar->globalLocation +
        determineVariableByteSize(maxGlobalVar);

      lowestGlobalVarAddr = minGlobalVar->globalLocation;
    }
  else
    {
      highestGlobalVarAddr = 0;
      lowestGlobalVarAddr = 0;
    }

  //  printf("highestGlobalVarAddr = 0x%lx, lowestGlobalVarAddr = 0x%lx\n",
  //	 highestGlobalVarAddr, lowestGlobalVarAddr);

  genfreehashtable(GlobalVarsTable);
}

// Returns true if the specified address and byte size fits
// is within the range of the globals:
// TODO: Check boundary conditions!!!
// Deprecated!
/* char isAddrInGlobalSpace(unsigned long a, int numBytes) */
/* { */
/*   char returnValue = ((a >= lowestGlobalVarAddr) && */
/* 		      ((a + (unsigned long)(numBytes)) <= highestGlobalVarAddr)); */
/*   //  printf("highestGlobalVarAddr = 0x%lx, lowestGlobalVarAddr = 0x%lx\n", */
/*   //	 highestGlobalVarAddr, lowestGlobalVarAddr); */
/*   //  printf("address in question: 0x%lx, byte size: %d, sum: 0x%lx - inGlobal? %d\n", */
/*   //	 a, numBytes, (a + (unsigned long)(numBytes)), returnValue); */

/*   return returnValue; */
/* } */


// Initializes StructNamesIDTable by going through dwarf_entry_array
// and associating each struct/union type declaration that has
// is_declaration = null with its name.  This ensures that in later
// stages, we only refer to one struct/union entry and not a myriad of
// 'fake' declaration entries.
// TODO: Is there the danger of having 2 struct
// types share the same name but are visibel in different compilation
// units?
//
// As a side effect, let's also initialize the names of unnamed structs
// so that we can have something to uniquely identify them with:
//
// For unnamed structs/unions/enums, we should just munge the
// name from the ID field so that we have something
// to use to identify this struct
// We will name it "unnamed_0x$ID" where $ID
// is the ID field in hex.
static void initializeStructNamesIDTable()
{
  unsigned long i;
  dwarf_entry* cur_entry = 0;

  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_collection_type(cur_entry->tag_name)) {
      collection_type* collectionPtr = (collection_type*)(cur_entry->entry_ptr);
      if (!collectionPtr->is_declaration) {
        //        VG_(printf)("%s (%u)\n", collectionPtr->name, cur_entry->ID);

        // Don't throw in entries with no names because that will be
        // really confusing
        if (collectionPtr->name) {
        genputtable(StructNamesIDTable,
                    (void*)collectionPtr->name, // key    (char*)
                    (void*)cur_entry->ID);      // value  (unsigned long)
        }
        // If it's a true entry (is_declaration == false)
        // but it's unnamed, then give it a name by munging its ID:
        else {
          // The maximum size is 10 + 8 + 1 = 19
          // 10 for "unnamed_0x", 8 for maximum size for cur_entry->ID,
          // and 1 for null-terminator
          char* fake_name = calloc(19, sizeof(*fake_name));
          sprintf(fake_name, "unnamed_0x%x", cur_entry->ID);
          collectionPtr->name = fake_name;
        }
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
// updateAllDaikonFunctionInfoEntries() in kvasir_runtime.c
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
      DPRINTF("i: %d\n", i);
      cur_entry = &dwarf_entry_array[i];
      // Ignore invalid functions and DUPLICATE function entries
      // with the same start_pc
      if (entry_is_valid_function(cur_entry) &&
          !gencontains(FunctionTable,
                        (void*)(((function*)cur_entry->entry_ptr)->start_pc)))
        {
          function* dwarfFunctionPtr = (function*)(cur_entry->entry_ptr);

          cur_func_entry = VG_(calloc)(1, sizeof(*cur_func_entry));

          //          VG_(printf)("Adding function %s\n", dwarfFunctionPtr->name);

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
          // updateAllDaikonFunctionInfoEntries() (Valgrind's
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
// "const", "volatile", or "pointer": it simply discards tag and moves on,
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

// Extracts base type information
// Modifies: t
static void extractBaseType(TypeEntry* t, base_type* basePtr)
{
  // Figure out what basic type it is
  switch(basePtr->encoding)
    {
    case DW_ATE_float:
      if (basePtr->byte_size == sizeof(float))
        {
          t->decType = D_FLOAT;
        }
      else if (basePtr->byte_size == sizeof(double))
        {
          t->decType = D_DOUBLE;
        }
      else if (basePtr->byte_size == sizeof(long double))
        {
          t->decType = D_LONG_DOUBLE;
        }

      // TODO: Need to write a Kvasir/Fjalar function to scan over all
      // TypeEntry entries and map their declared types to rep. types,
      // then erase all mention of repType from this file:
      t->repType = R_DOUBLE;
      break;

    case DW_ATE_signed:
    case DW_ATE_signed_char:
      if (basePtr->byte_size == sizeof(char))
        {
          t->decType = D_CHAR;
        }
      else if (basePtr->byte_size == sizeof(short))
        {
          t->decType = D_SHORT;
        }
      else if (basePtr->byte_size == sizeof(int))
        {
          t->decType = D_INT;
        }
      else if (basePtr->byte_size == sizeof(long long int))
        {
          t->decType = D_LONG_LONG_INT;
        }

      t->repType = R_INT;
      break;

    case DW_ATE_unsigned:
    case DW_ATE_unsigned_char:
      if (basePtr->byte_size == sizeof(unsigned char))
        {
          t->decType = D_UNSIGNED_CHAR;
        }
      else if (basePtr->byte_size == sizeof(unsigned short))
        {
          t->decType = D_UNSIGNED_SHORT;
        }
      else if (basePtr->byte_size == sizeof(unsigned int))
        {
          t->decType = D_UNSIGNED_INT;
        }
      else if (basePtr->byte_size == sizeof(unsigned long long int))
        {
          t->decType = D_UNSIGNED_LONG_LONG_INT;
        }

      t->repType = R_INT;
      break;

    case DW_ATE_boolean:
      t->decType = D_BOOL;
      t->repType = R_INT;
      break;

    default:
      tl_assert(0 && "Unknown primitive type");
    }

  t->byteSize = basePtr->byte_size;
}

// Extracts enumeration type info
// Modifies: t
static void extractEnumerationType(TypeEntry* t, collection_type* collectionPtr)
{
  t->decType = D_ENUMERATION;
  t->collectionName = collectionPtr->name;

  t->repType = R_INT;
  t->byteSize = sizeof(int); // An enumeration is an int
}


// Extracts subroutine type corresponding to a function pointer parameter
// Modifies: t
static void extractSubroutineType(TypeEntry* t, function_type* functionPtr)
{
  t->byteSize = 4; // TODO: Why does this only take up one byte?
                   // Shouldn't it take up 4?
  t->decType = D_FUNCTION;
  t->repType = R_HASHCODE;
}

// Extracts type information from a void pointer
// Modifies: t
static void extractVoidType(TypeEntry* t)
{
  t->byteSize = 4; // TODO: Why does this only take up one byte?
                   // Shouldn't it take up 4?
  t->decType = D_VOID;
  t->repType = R_HASHCODE;
}

// Extracts struct/union type info from collectionPtr and creates
// member variables in t->memberListPtr
static void extractStructUnionType(TypeEntry* t, dwarf_entry* e)
{
  collection_type* collectionPtr = 0;
  UInt i = 0;
  VarNode* memberNodePtr = 0;

  if (!(e->tag_name == DW_TAG_structure_type) &&
      !(e->tag_name == DW_TAG_union_type))
    return;

  collectionPtr = (collection_type*)(e->entry_ptr);

  //  VG_(printf)("%s (dec: %u) (ID: %u)\n",
  //              collectionPtr->name,
  //              collectionPtr->is_declaration,
  //              e->ID);

  t->isStructUnionType = 1;
  t->repType = R_HASHCODE;

  if (e->tag_name == DW_TAG_union_type)
    t->decType = D_UNION;
  else
    t->decType = D_STRUCT;

  t->collectionName = collectionPtr->name;

  t->memberListPtr = (VarList*)VG_(calloc)(1, sizeof(*(t->memberListPtr)));

  t->num_member_funcs = collectionPtr->num_member_funcs;
  t->member_funcs = collectionPtr->member_funcs;

  // Look up the dwarf_entry for the struct/union and iterate
  // through its member_vars array (of pointers to members)
  // in order to extract each member variable

  for (i = 0; i < collectionPtr->num_member_vars; i++) {
    member* memberPtr = (member*)((collectionPtr->member_vars[i])->entry_ptr);
    extractOneVariable(t->memberListPtr,
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
                       0);
  }


  // STATIC MEMBER VARIABLES!
  for (i = 0; i < collectionPtr->num_static_member_vars; i++) {
    variable* staticMemberPtr =
      (variable*)((collectionPtr->static_member_vars[i])->entry_ptr);

    DPRINTF("Trying to extractOneVariable on member var: %s\n",
            staticMemberPtr->mangled_name);

    extractOneVariable(&globalVars,
                       staticMemberPtr->type_ptr,
                       (staticMemberPtr->mangled_name ?  // TODO: demangle this later
                        staticMemberPtr->mangled_name :
                        staticMemberPtr->name),
                       0,
                       0,
                       1,
                       staticMemberPtr->is_external,
                       staticMemberPtr->globalVarAddr,
                       0,0,0,0,0,0,
                       t,
                       0);

    DPRINTF("Finished Trying to extractOneVariable on member var: %s\n",
            staticMemberPtr->mangled_name);
  }

  // After we are doing constructing the struct TypeEntry entry,
  // we must initialize the struct byte size:

  // To calculate the byte size of the struct, we look at the
  // data_member_location of the last member and add its byte size
  // (if member is actually a struct type, then its byte size should already
  //  have been computed by the recursive version of this call to that struct)
  // - Round struct size up to the nearest word (multiple of 4)
  memberNodePtr = t->memberListPtr->last;
  if (memberNodePtr)
    {
      int structByteSize = 0;
      VariableEntry* memberVarPtr = &(memberNodePtr->var);
      structByteSize = memberVarPtr->data_member_location +
	determineVariableByteSize(memberVarPtr);

      // Round struct size up to the nearest word (multiple of 4)
      t->byteSize = ((structByteSize + 3) >> 2) << 2;

      DPRINTF("collection name: %s, byteSize: %d\n", t->collectionName, t->byteSize);
    }
}



// Extracts only the local variables of type DW_TAG_array_type
// or collection_type (struct/union)
// and places them in the local_vars list within each respective
// function (we need struct types because they may contain static arrays
// or structs which themselves contain static arrays)
void extractLocalArrayAndStructVariables(FunctionEntry* f,
                                         function* dwarfFunctionEntry)
{
  UInt i;

  DPRINTF("extractLocalArrayAndStructVariables - %s (#: %u)\n",
	 dwarfFunctionEntry->name, dwarfFunctionEntry->num_local_vars);

  // No local variables - don't do anything
  if (!dwarfFunctionEntry->num_local_vars)
    return;

  for (i = 0; i < dwarfFunctionEntry->num_local_vars; i++)
    {
      DPRINTF("%s - local_vars: %d of %d\n", dwarfFunctionEntry->name, i+1, dwarfFunctionEntry->num_local_vars);
      extractOneLocalArrayOrStructVariable(f,
                                           dwarfFunctionEntry->local_vars[i]);
    }

  DPRINTF("DONE extractLocalArrayAndVariables - %s\n",
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

  // Start with default offset of 8 from EBP (*EBP = old EBP, *(EBP+4) = return addr)
  // unless the function returns a struct by value - then we start
  // with an offset of 12 since *(EBP+8) = pointer to the place to put the struct)

  VariableEntry* firstReturnVar = &f->returnValue.first->var;
  if (firstReturnVar &&
      (D_STRUCT == firstReturnVar->varType->decType) &&
      (0 == firstReturnVar->declaredPtrLevels))
    {
      offset = 12;
    }

  for (cur_node = f->formalParameters.first;
       cur_node != NULL;
       cur_node = cur_node->next)
    {
      int cur_byteSize = 0;
      cur_node->var.byteOffset = offset;
      cur_byteSize = determineVariableByteSize(&(cur_node->var));
      // WORD ALIGNED!!!
      if (cur_byteSize > 0)
	{
	  // Round offset up to the nearest word (4 bytes)
	  offset += (((cur_byteSize + 3) >> 2) << 2);
	}
    }
}

// Returns the byte size of the given VariableEntry
static int determineVariableByteSize(VariableEntry* var)
{
  int byteSize = 0;

  if (0 == var->declaredPtrLevels) {
    byteSize = var->varType->byteSize;
  }
  // Static array of some type
  else if (var->isStaticArray)
    {
      int i;

      if (var->declaredPtrLevels == 1) {
        byteSize = var->varType->byteSize; // static array of base type
      }
      else if (var->declaredPtrLevels > 1) {
        byteSize = sizeof(void*); // static array of pointers
      }

      for (i = 0; i < var->numDimensions; i++) {
        DPRINTF("  upperBounds[%d] = %d\n", i, var->upperBounds[i]);
        byteSize *= (var->upperBounds[i] + 1);
      }
    }
  // Pointer type
  else {
    byteSize = sizeof(void*);
  }

  DPRINTF("detDVBS| name: %s, decPtrLvls: %d, isSA: %d, byteSize: %d, return: %d\n",
          var->name, var->declaredPtrLevels, var->isStaticArray, var->varType->byteSize, byteSize);

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
      totalByteSize = (cur_node->var.byteOffset +
                       determineVariableByteSize(&(cur_node->var)));
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

  DPRINTF("  %s parameter name %s\n",
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
		     0,0,0,0,0,0,1);
}

static void extractFormalParameterVars(FunctionEntry* f,
                                function* dwarfFunctionEntry)
{
  UInt i;

  DPRINTF("extractFormalParameterVars - %s (#: %u)\n",
	 dwarfFunctionEntry->name, dwarfFunctionEntry->num_formal_params);

  // No formal parameters - don't do anything
  if (!dwarfFunctionEntry->num_formal_params)
    return;

  for (i = 0; i < dwarfFunctionEntry->num_formal_params; i++)
    {
      extractOneFormalParameterVar(f, dwarfFunctionEntry->params[i]);
    }
}


// Only adds a new entry if dwarfVariableEntry's type == DW_TAG_array_type
// or collection_type
void extractOneLocalArrayOrStructVariable(FunctionEntry* f,
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

  // Only store array types and collection types!
  // Also, don't store anything with couldBeGlobalVar == true
  // because that means that it's a static variable.
  // static variables have global scope so they can be picked up
  // by the sweep of the global variables
  if (!(tag_is_array_type(typePtr->tag_name) ||
        tag_is_collection_type(typePtr->tag_name)) ||
      variablePtr->couldBeGlobalVar)
    return;

  if (!variablePtr->name) {
    VG_(printf)( "Unexpected unnamed local variable in %s\n",
            f->name);
    return;
  }

      DPRINTF("  %s local variable name %s - localArrayVariables %p size = %d\n",
	  f->name,
	  variablePtr->name,
	  &(f->localArrayVariables),
	  f->localArrayVariables.numVars);

  extractOneVariable(&(f->localArrayVariables),
                     typePtr,
                     variablePtr->name,
		     0,
                     variablePtr->offset,
                     0,
		     0,
		     0,
		     0,
		     0,0,0,0,0,0,0);
}

void extractReturnVar(FunctionEntry* f,
                      function* dwarfFunctionEntry)
{
  // Get the return value type
  dwarf_entry* typePtr = dwarfFunctionEntry->return_type;

  DPRINTF("extractReturnVar - %s\n",
	  dwarfFunctionEntry->name);

  // void function - no return type
  if(!typePtr)
    {
      DPRINTF("DONE (empty) - extractReturnVar - %s\n",
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
		     0,0,0,0,0,0,0);
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
                        char isFormalParam) // All static arrays which are
// formal parameters are treated like NORMAL pointers which are not statically-sized
// just because that's how the C language works
{
  VariableEntry* varPtr = 0;
  int newlyAddedTypeEntry = 0;
  int ptrLevels = 0;

  DPRINTF("Entering extractOneVariable for %s\n", variableName);

  // Don't extract the variable if it has a bogus name:
  if (ignore_variable_with_name(variableName))
    return;

  // Create a new VariableEntry and append it to the end of VarList
  insertNewNode(varListPtr);

  // Work on the last variable in varListPtr
  varPtr = &(varListPtr->last->var);

  varPtr->name = variableName;
  varPtr->fileName = fileName;
  varPtr->byteOffset = byteOffset;

  // Special case for C++ 'this' parameter variables:
  // Automatically put a 'P' disambig on it because
  // 'this' will always refer to one object and not an array
  // TODO: This will pick up any variable named 'this' so it's possible
  // (I don't know why you would do this) that in a C program, you can have
  // some variable named 'this' and it'll get a 'P' disambig on it
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

  DPRINTF("About to strip modifiers for %s\n", variableName);

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
	  if (typePtr->tag_name == DW_TAG_pointer_type)
	    {
	      typePtr = extractModifierType(modifierPtr);
	      ptrLevels++;
	    }
	  else
	    {
	      // If the parameter is a "const" or "volatile" type, just strip
	      // off the "const" or "volatile" and process it again
	      typePtr = extractModifierType(modifierPtr);
	    }
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

  DPRINTF("Finished stripping modifiers for %s\n", variableName);
  DPRINTF("varPtr is %p\n", varPtr);
  DPRINTF("typePtr is %p\n", typePtr);

  varPtr->repPtrLevels = ptrLevels;
  varPtr->declaredPtrLevels = ptrLevels;

  if (typePtr && (typePtr->tag_name == DW_TAG_structure_type)) {
    char* type_name = ((collection_type*)(typePtr->entry_ptr))->name;
    // We want to ignore POINTERS to certain types (don't ignore
    // the actual values of that type because it may screw up alignments).
    // Instead, we want to convert these into generic void pointers.
    if ((varPtr->declaredPtrLevels > 0) &&
        ignore_type_with_name(type_name)) {
      //      VG_(printf)("IGNORED --- %s\n", type_name);
      varPtr->varType = &GlobalHashcodeType;
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

  if (typePtr)
    {
      // We want to look up the REAL type entry, not a fake one with
      // is_declaration non-null.
      //   (Hopefully, if all goes well, the only TypeEntry values
      //    in TypesTable are REAL entries whose dwarf_entry has
      //    is_declaration NULL, not fake declaration entries)

      // For struct/union types, we want to make sure that we are
      // performing a lookup on a REAL entry, not just a declaration:
      if (tag_is_collection_type(typePtr->tag_name)) {
        collection_type* collectionPtr = (collection_type*)(typePtr->entry_ptr);

        // If it's a fake entry, we want to look up its name in
        // StructNamesIDTable and map it to the REAL entry with the
        // same name:
        if (collectionPtr->is_declaration &&
            collectionPtr->name) {
          unsigned long realID = (unsigned long)gengettable(StructNamesIDTable,
                                                            (void*)collectionPtr->name);
          //          VG_(printf)("* %s (Fake ID: %u) (Real ID: %u)\n",
          //                      collectionPtr->name,
          //                      typePtr->ID,
          //                      realID);

          // If realID == 0, that means that we somehow don't have
          // debugging info for the real entry, so we must just resort
          // to using the fake entry, reluctantly
          if (realID) {
            // Now do a lookup for the REAL ID and not the fake one:
            varPtr->varType =
              (TypeEntry*)gengettable(TypesTable, (void*)realID);

            // If you can't find anything, we'll have to end up calling
            // extractStructUnionType so let's change typePtr to refer
            // to the entry in dwarf_entry_array with the REAL ID before
            // passing it further along:
            if (!varPtr->varType) {
              unsigned long realIndex = 0;
              if (binary_search_dwarf_entry_array(realID,  &realIndex)) {
                typePtr = &dwarf_entry_array[realIndex];

                //                VG_(printf)("  realIndex: %u, realID: %u, typePtr->ID: %u\n",
                //                            realIndex, realID, typePtr->ID);
              }
            }
          }
          else {
            varPtr->varType = (TypeEntry*)gengettable(TypesTable, (void*)typePtr->ID);
          }
        }
        // Do a regular lookup if it's either an unnamed struct or
        // (even better) a REAL one with is_declaration = null
        else {
          varPtr->varType = (TypeEntry*)gengettable(TypesTable, (void*)typePtr->ID);
        }
      }
      // Just do a lookup for non-struct/union types
      else {
        varPtr->varType = (TypeEntry*)gengettable(TypesTable, (void*)typePtr->ID);
      }
    }
  // If the entry is not found in TypesTable, create a new one
  // and add it to the table
  if (!varPtr->varType)
    {
      DPRINTF("Adding type entry for %s\n", variableName);

      varPtr->varType = (TypeEntry*)VG_(calloc)(1, sizeof(*varPtr->varType));
      // We are passing in the true ID but casting it so the compiler won't warn me:
      if (typePtr) {
        genputtable(TypesTable, (void*)typePtr->ID, varPtr->varType);
      }
      newlyAddedTypeEntry = 1;
    }

  if (newlyAddedTypeEntry)
    {
       // WARNING: Some typedefs do not have targets - if typePtr == NULL,
       // just say screw it and make this variable into a dummy null variable:
       // Void typePtr entries will NOT be in TypesTable :(
      if (!typePtr)
	{
	  // Got void; probably was void *, const void *, etc.
	  extractVoidType(varPtr->varType);
	}
      // If the parameter type is a basic type, then we're golden!
      // Base types are the easiest to handle!
      else if (tag_is_base_type(typePtr->tag_name))
	{
	  base_type* basePtr = (base_type*)(typePtr->entry_ptr);
	  extractBaseType(varPtr->varType, basePtr);
	}
      // If the parameter is an enumeration type
      else if (typePtr->tag_name == DW_TAG_enumeration_type)
	{
	  collection_type* collectionPtr = (collection_type*)(typePtr->entry_ptr);
	  extractEnumerationType(varPtr->varType, collectionPtr);
	}
      else if (typePtr->tag_name == DW_TAG_subroutine_type)
	{
	  // Function (from a function pointer)
	  // Treat sorta like a hashcode, for the moment.
	  function_type* func_type = (function_type *)(typePtr->entry_ptr);
	  extractSubroutineType(varPtr->varType, func_type);
	}
      // Struct or union type
      else if  ((typePtr->tag_name == DW_TAG_structure_type) ||
		(typePtr->tag_name == DW_TAG_union_type))
	{
          extractStructUnionType(varPtr->varType, typePtr);
	}
      else
	{
	  printf("Unknown type encountered while trying to parse variable: %s\n",
		 variableName);
	  //	  VG_(printf)( "Unknown type encountered while attempting to extract one variable!\n");
	  //	  abort();
	}
    }

  // Make a special case for handling strings:
  if ((varPtr->varType->decType == D_CHAR) &&
      (varPtr->repPtrLevels > 0))
    {
      varPtr->isString = 1;
      varPtr->repPtrLevels--;
    }

  // TODO: What about arrays of pointers?  int* [10] currently turns
  // into base type = int, ptrLevels = 2, isStaticArray = true
  // but it should be base type = hashcode, ptrLevels = 1, isStaticArray = true

  // Proposed solution: If isStaticArray = true and (ptrLevels > 1 and
  // varPtr->varType->decType != D_CHAR) or (ptrLevels > 2 and
  // varPtr->varType->decType == D_CHAR), then
  // we turn it into a 1-D array of hashcodes by setting ptrLevels = 1
  // and pointing the type to GlobalHashcodeType.
  // This means that we do not support multidimensional arrays
  // (but we didn't used to either) but fail more gracefully on them now
  if (varPtr->isStaticArray &&
      (ptrLevels > ((varPtr->varType->decType == D_CHAR) ?
                    2 : 1))) {
    varPtr->repPtrLevels = 1;
    varPtr->declaredPtrLevels = 1;
    varPtr->varType = &GlobalHashcodeType;
  }
}

// Pre: All entries in TypesTable have already been set
//      so run this AFTER we've set up all the stuff in TypesTable
// Effect: Iterate through all collection (Struct/Union/Class)
// entries in TypesTable, and for each one, iterate
// through its member_funcs_array, visit every member function
// in there, and set each one's parentClass field to this struct
void initializeAllClassMemberFunctions() {
  struct geniterator* it = gengetiterator(TypesTable);
  UInt i;
  // Iterate through member_funcs and set the classParent
  // field of each member function entry in FunctionTable
  // to point to this struct t

  while (!it->finished) {
    TypeEntry* t = (TypeEntry*)
      gengettable(TypesTable, gennext(it));

    // Skip unnamed structs or types which aren't structs
    if (!t->collectionName) {
      continue;
    }

    //    VG_(printf)("STRUCT %s\n", t->collectionName);
    for (i = 0; i < t->num_member_funcs; i++) {
      function* funcPtr = (function*)((t->member_funcs[i])->entry_ptr);

      FunctionEntry* entry = findFunctionInfoByStartAddr(funcPtr->start_pc);
      if (entry) {
        //        VG_(printf)("   member function: %s (%s)\n",
        //                    entry->name, entry->mangled_name);
        entry->parentClass = t;
      }
    }
  }
  genfreeiterator(it);
}

// TypesTable - hash table containing TypeEntry entries
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
inline FunctionEntry* findFunctionEntryByStartAddr(unsigned int startPC) {
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
TypeEntry* findTypeEntryByName(char* name) {
  struct geniterator* it = gengetiterator(TypesTable);

  while (!it->finished) {
    TypeEntry* cur_type = (TypeEntry*)
      gengettable(TypesTable, gennext(it));

    if (cur_type->collectionName &&
        VG_STREQ(cur_type->collectionName, name)) {
      genfreeiterator(it);
      return cur_type;
    }
  }

  genfreeiterator(it);
  return 0;
}


void XMLprintFunctionTable()
{
  VarNode* formalParamNode = 0;
  VarNode* localArrayVarNode = 0;
  VarNode* returnVarNode = 0;
  FunctionEntry* cur_entry;
  struct geniterator* it = gengetiterator(FunctionTable);

  while (!it->finished)
    {
      cur_entry = (FunctionEntry*)
        gengettable(FunctionTable, gennext(it));

      if (!cur_entry)
        continue;

      printf("\n%s (%s) startPC=%p\n\n",
             cur_entry->fjalar_name,
             cur_entry->filename,
	     (void*)cur_entry->startPC);

      for (formalParamNode = cur_entry->formalParameters.first;
           formalParamNode != 0; formalParamNode = formalParamNode->next)
        {
          printf("  PARAM: ");
          printOneVariable(&(formalParamNode->var), 0, 1);
        }

      for (localArrayVarNode = cur_entry->localArrayVariables.first;
           localArrayVarNode != 0; localArrayVarNode = localArrayVarNode->next)
        {
          printf("  LOCAL: ");
          printOneVariable(&(localArrayVarNode->var), 0, 1);
        }

      for (returnVarNode = cur_entry->returnValue.first;
           returnVarNode != 0; returnVarNode = returnVarNode->next)
        {
          printf("  RETURN: ");
          printOneVariable(&(returnVarNode->var), 0, 1);
        }
    }

  genfreeiterator(it);
}

void XMLprintGlobalVars()
{
  VarNode* globalVarNode = 0;

  printf("\nGlobal variables:\n\n");

  for (globalVarNode = globalVars.first;
       globalVarNode != 0;
       globalVarNode = globalVarNode->next)
    {
          printf("  GLOBAL: ");
          printOneVariable(&(globalVarNode->var), 0, 1);
    }
}

void XMLprintVariablesInList(VarList* varListPtr, int leadingSpaces, TypeEntry* structType)
{
  VarNode* curNode = 0;
  int i = 0;

  if (!varListPtr)
    return;

  for (curNode = varListPtr->first;
       curNode != 0;
       curNode = curNode->next)
    {
      for (i = 0; i < leadingSpaces; i++)
	printf(" ");

      // Avoid printing out repeated entries for recursively-defined structs
      // (ie. linked lists)
      //      if (curNode->var.varType == structType)
      if (gencontains(VisitedStructsTable, (void*)(curNode->var.varType)) &&
	  ((int)(gengettable(VisitedStructsTable, (void*)(curNode->var.varType))) >
	   MAX_VISIT_STRUCT_DEPTH))
	{
	  printOneVariable(&(curNode->var), 1, 0);
	}
      else
	{
	  printOneVariable(&(curNode->var), 0, 0);
	}
    }
}

// Prints one VariableEntry on one line followed by the type information
// of its TypeEntry on the next line and then a newline
void XMLprintOneVariable(VariableEntry* var, char doNotRecurse, char firstTimePrinting)
{
  TypeEntry* t;
  if (!var)
    return;

  if (firstTimePrinting)
    {
      // Initialize VisitedStructsTable if necessary
      if (VisitedStructsTable)
	{
	  genfreehashtable(VisitedStructsTable);
	}
      VisitedStructsTable = genallocatehashtable((unsigned int (*)(void *)) & hashID,(int (*)(void *,void *)) &equivalentIDs);
    }

   t = var->varType;

  printf("name: %s, ptrLevels R/D:%d/%d, init:%d, byteOffset:%d, isGlobal:%d, globalLocation:0x%lx",
         var->name,
	 var->repPtrLevels,
	 var->declaredPtrLevels,
	 var->isInitialized,
	 var->byteOffset,
	 var->isGlobal,
	 var->globalLocation);

  // Print out array information
  if (var->isStaticArray)
    {
      int i = 0;
      printf(", ARRAY dims:");
      for (i = 0; i < var->numDimensions; i++)
	{
	  printf(" %lu", var->upperBounds[i]);
	}
    }

  if (var->isStructUnionMember)
    {
      printf(", memberLocation: %lu, structParent: %s",
	     var->data_member_location,
	     (var->structParentType ?
	      var->structParentType->collectionName :
	      "(no parent)"));
    }

  if (t)
    {
      printf("\n     %s, decType: %s, byteSize: %d",
	     t->collectionName,
	     DeclaredTypeNames[t->decType],
	     t->byteSize);

      if (var->isString)
	{
	  printf(" CHARACTER STRING!");
	}

      printf("\n");

      if (t->isStructUnionType)
	{
	  // Check to see if the VisitedStructsTable contains
	  // more than MAX_VISIT_STRUCT_DEPTH of the current struct type:
	  if (gencontains(VisitedStructsTable, (void*)t))
	    {
	      int count = (int)(gengettable(VisitedStructsTable, (void*)t));
	      if (count <= MAX_VISIT_STRUCT_DEPTH)
		{
		  count++;
		  genputtable(VisitedStructsTable, (void*)t, (void*)count);
		}
	      else
		{
		  printf("   >>> RECURSION STOPPED by VisitedStructsTable to prevent infinite loop\n");
		  return;
		}
	    }
	  else
	    {
	      genputtable(VisitedStructsTable, (void*)t, (void*)1);
	    }

	  if (doNotRecurse)
	    {
	      printf("    >>> RECURSION STOPPED to prevent infinite loop\n");
	    }
	  else
	    {
	      printf("   BEGIN struct members of %s:\n",
		     t->collectionName);

	      printVariablesInList(t->memberListPtr, 5, t);

	      printf("   END struct members of %s\n",
		     t->collectionName);
	    }
	}
    }
  else
    {
      printf("   No type information found for variable %s\n",
	     var->name);
    }
}
