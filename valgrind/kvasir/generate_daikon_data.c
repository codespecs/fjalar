/*
   This file is part of Kvasir, a Valgrind tool that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* generate_daikon_data.c:
   Performs static analysis of dwarf_entry_array to organize
   type information into daikon-specific form for the .decls file
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include "generate_daikon_data.h"
#include "elf/dwarf2.h"
#include "tool.h"
#include "kvasir_main.h"
#include "decls-output.h"
#include "GenericHashtable.h"

DaikonType GlobalHashcodeType = {0,
                                 D_VOID,
                                 R_HASHCODE,
                                 4, // sizeof(void*)
                                 0, 0, 0, 0};

// Hash table that maps the names of structs to their ID in
// dwarf_entry_array
// (This is needed to make sure that there is only one entry of
//  each struct with a certain name that all variables can refer to.
//  Otherwise, lots of variables may refer to entries that are merely
//  empty declarations in their compilation unit.)
// Key: name of struct type
// Value: ID of REAL entry where is_declaration is 0
static struct genhashtable* StructNamesIDTable = 0;

// Global strings

static char* DAIKON_RETURN_NAME = "return";

// Corresponds to DaikonDeclaredType enum:
char* DaikonDeclaredTypeNames[] = {"D_NO_TYPE", // Create padding
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

// Corresponds to DaikonRepType enum:
char* DaikonRepTypeNames[5] = {"R_NO_TYPE", // Create padding
			       "R_INT",
			       "R_DOUBLE",
			       "R_HASHCODE",
			       "R_STRING"};

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
}

// Deletes the last node in *varListPtr
void deleteTailNode(VarList* varListPtr)
{
  if (varListPtr->last)
    {
      if (varListPtr->numVars == 1)
        {
          VG_(free)(varListPtr->last);
	  VG_(free)(varListPtr->first);
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

// Pre-processes global dwarf_entry_array in order to place
// the data in a form that can easily be turned into .decls
// and .dtrace files
void daikon_preprocess_entry_array()
{
  // First delete everything that's in the globalVars list
  // TODO: Yes, this is shady and will leak memory, but oh well
  VarNode* node = globalVars.first;
  VarNode* nextNode = 0;

  while (node) {
    nextNode = node->next;
    VG_(free)(node);
    node = nextNode;
  }
  globalVars.first = 0;
  globalVars.last = 0;
  globalVars.numVars = 0;

  VisitedStructsTable = 0;

  DPRINTF("About to allocate hash table\n");

  // Initialize DaikonTypesTable
  DaikonTypesTable = genallocatehashtable((unsigned int (*)(void *)) & hashID,(int (*)(void *,void *)) &equivalentIDs);

  StructNamesIDTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  initializeStructNamesIDTable();

  initializeDaikonFunctionInfoTable();

  // Don't even bother to init this if we set --kvasir-ignore-globals
  if (!kvasir_ignore_globals) {
    initializeGlobalVarsList();
  }

  initializeAllClassMemberFunctions();

  // TODO: This still leaks lots of memory :)

  // We shouldn't free this right now since other stuff (ie. .disambig)
  // depends upon it, but we need to think about freeing it sometime:
  //  genfreehashtable(DaikonTypesTable);
  //  DaikonTypesTable = 0;

  //  print_dwarf_entry_array();

  //  printDaikonFunctionInfoTable();
  //  printDaikonGlobalVars();

  genfreehashtable(StructNamesIDTable);
  StructNamesIDTable = 0;
}

int entry_is_valid_function(dwarf_entry *entry) {
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


unsigned int hashGlobalVarAddr(unsigned long ID) {
  return ((unsigned int)ID) % geninitialnumbins;
}

// Super-trivial key comparison method -
int equivalentGlobalVarAddrs(unsigned long ID1, unsigned long ID2) {
  return (ID1 == ID2);
}

// Initializes the global variables list and fills it up
// with global variable entries from dwarf_entry_array

// Note: If two or more source files include the same header file which
// has global declarations, then the entry for these global variables
// will appear multiple times, once for every source file. However, these
// multiple copies of global variable entries all have the SAME address location
// and thus are the exact same thing. We must discard these duplicates so
// that Kvasir doesn't produce duplicate output in the .decls and .dtrace
// files (Daikon cannot handle duplicate variable names at all).
// Remember, we must key in on both the variable names and the address
// locations for removing duplicates.
void initializeGlobalVarsList()
{
  UInt i;
  dwarf_entry* cur_entry = 0;
  VarNode* node = 0;
  DaikonVariable* maxGlobalVar = 0;
  DaikonVariable* currentVar = 0;
  DaikonVariable* minGlobalVar = 0;

  // Create a hashtable with keys = {unsigned long (globalVarAddr), non-zero}
  //                   and values = {string which is the global variable name}
  struct genhashtable* GlobalVarsTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashGlobalVarAddr,
			 (int (*)(void *,void *)) &equivalentGlobalVarAddrs);

  DPRINTF("Entering initializeGlobalVarsList()\n");

  DPRINTF("mid-initglobalvarslist\n");

  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_variable(cur_entry->tag_name)) {
      variable* variable_ptr = (variable*)(cur_entry->entry_ptr);
      // IGNORE variables with is_declaration_or_artificial or specification_ID active
      // because these are empty shells!
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

  DPRINTF("mid-2-initglobalvarslist\n");

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
        determineDaikonVariableByteSize(maxGlobalVar);

      lowestGlobalVarAddr = minGlobalVar->globalLocation;
    }
  else
    {
      highestGlobalVarAddr = 0;
      lowestGlobalVarAddr = 0;
    }

  DPRINTF("Exiting initializeGlobalVarsList()\n");

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
// and associates each struct/union type declaration with
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
void initializeStructNamesIDTable()
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

          // Special case for Brian's repair tool -
          // We will search for 'unnamed' later and fill that in
          // with a concatenation of field names
          if (kvasir_repair_format) {
            sprintf(fake_name, "unnamed", cur_entry->ID);
          }
          else {
            sprintf(fake_name, "unnamed_0x%x", cur_entry->ID);
          }
          collectionPtr->name = fake_name;
        }
      }
    }
  }
}

// TODO: This will leak memory if called more than once per program execution
//       since the entries in DaikonFunctionInfoTable are not being properly
//       freed.  However, during normal execution, this should only be called once
 // After this function is called, the 'daikon_name' field of all functions
 // within DaikonFunctionInfoTable should be initialized to what is printed
 // in the .decls/.dtrace EXCEPT for C++ function names which require demangling.
 // Demangling occurs in updateAllDaikonFunctionInfoEntries() in kvasir_runtime.c
void initializeDaikonFunctionInfoTable()
{
  unsigned long i;
  dwarf_entry* cur_entry = 0;
  DaikonFunctionInfo* cur_daikon_entry = 0;
  unsigned long num_functions_added = 0;

  // Create DaikonFunctionInfo table
  DaikonFunctionInfoTable =
    genallocatehashtable((unsigned int (*)(void *)) & hashID,
                         (int (*)(void *,void *)) &equivalentIDs);

  for (i = 0; i < dwarf_entry_array_size; i++)
    {
      DPRINTF("i: %d\n", i);
      cur_entry = &dwarf_entry_array[i];
      // Ignore invalid functions and DUPLICATE function entries
      // with the same start_pc
      if (entry_is_valid_function(cur_entry) &&
          !gencontains(DaikonFunctionInfoTable,
                        (void*)(((function*)cur_entry->entry_ptr)->start_pc)))
        {
          function* dwarfFunctionPtr = (function*)(cur_entry->entry_ptr);

          cur_daikon_entry = VG_(calloc)(1, sizeof(*cur_daikon_entry));

          //          VG_(printf)("Adding function %s\n", dwarfFunctionPtr->name);

          cur_daikon_entry->name = dwarfFunctionPtr->name;
          cur_daikon_entry->mangled_name = dwarfFunctionPtr->mangled_name;
          cur_daikon_entry->filename = dwarfFunctionPtr->filename;
          cur_daikon_entry->accessibility = dwarfFunctionPtr->accessibility;

          cur_daikon_entry->startPC = dwarfFunctionPtr->start_pc;
          cur_daikon_entry->endPC = dwarfFunctionPtr->end_pc;

          cur_daikon_entry->isExternal = dwarfFunctionPtr->is_external;

          // Ok, here's the deal.  If cur_daikon_entry->mangled_name
          // exists, then we know that it's a C++ mangled function
          // name that requires demangling later at run-time in
          // updateAllDaikonFunctionInfoEntries() (Valgrind's
          // demangler doesn't work at this point for some reason -
          // maybe it's too 'early' in the execution).  That function
          // will demangle mangled_name and turn it into a Daikon
          // name, so we don't have to initialize daikon_name right
          // now.  So only generate daikon_name right now if there is
          // no mangled name.
          if (!cur_daikon_entry->mangled_name) {
            char *the_class; /* What Daikon will think of as the
                                "class" part of the PPT name */
            char *buf, *p;

            if (dwarfFunctionPtr->is_external) {
              /* Globals print as "..main()", etc. */
              the_class = ".";
            } else {
              the_class = cur_daikon_entry->filename;
            }
            /* We want to print static_fn in subdir/filename.c
               as "subdir/filename.c.static_fn() */
            buf = VG_(malloc)(VG_(strlen)(the_class) + 1 +
                              VG_(strlen)(cur_daikon_entry->name) + 3);
            VG_(strcpy)(buf, the_class);
            for (p = buf; *p; p++) {
              if (!isalpha(*p) && !isdigit(*p) && *p != '.' && *p != '/'
                  && *p != '_')
                *p = '_';
            }
            VG_(strcat)(buf, ".");
            VG_(strcat)(buf, cur_daikon_entry->name);
            VG_(strcat)(buf, "()");
            cur_daikon_entry->daikon_name = buf;
        }

          DPRINTF("****** Name: %s | Mangled name: %s | Daikon name: %s | Address: 0x%x\n",
                      cur_daikon_entry->name,
                      (dwarfFunctionPtr->mangled_name ?
                       dwarfFunctionPtr->mangled_name :
                       "NO MANGLED NAME"),
                      cur_daikon_entry->daikon_name,
                      cur_daikon_entry->startPC);

          // This was formerly in extractTypeDataFromFunctionInfoArray():

          // Extract all formal parameter variables
          extractFormalParameterVars(cur_daikon_entry, dwarfFunctionPtr);

          // Extract all local array variables
          extractLocalArrayAndStructVariables(cur_daikon_entry, dwarfFunctionPtr);

          // Extract return variable
          extractReturnVar(cur_daikon_entry, dwarfFunctionPtr);

          // Make one more pass-through to make sure that byteOffsets are correct
          // for the word-aligned stack!
          // We must do this AFTER extracting the return variable
          verifyStackParamWordAlignment(cur_daikon_entry);

          // Add to DaikonFunctionInfoTable
          genputtable(DaikonFunctionInfoTable,
                      (void*)cur_daikon_entry->startPC, // key    (unsigned long)
		      (void*)cur_daikon_entry);         // value  (DaikonFunctionInfo*)
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
dwarf_entry* extractModifierType(modifier_type* modifierPtr)
{
  return modifierPtr->target_ptr;
}

// Extracts array type by modifying varPtr
// varListPtr and filling in the isStaticArray, numDimensions, and upperBounds
// fields within it
// Modifies: varPtr
// Returns: Pointer to the type of the array
// (This functions like an extended version of extractPointerType)
dwarf_entry* extractArrayType(DaikonVariable* varPtr, array_type* arrayPtr)
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
void extractBaseType(DaikonType* t, base_type* basePtr)
{
  // Figure out what basic type it is
  switch(basePtr->encoding)
    {
    case DW_ATE_float:
      if (basePtr->byte_size == sizeof(float))
        {
          t->declaredType = D_FLOAT;
        }
      else if (basePtr->byte_size == sizeof(double))
        {
          t->declaredType = D_DOUBLE;
        }
      else if (basePtr->byte_size == sizeof(long double))
        {
          t->declaredType = D_LONG_DOUBLE;
        }

      t->repType = R_DOUBLE;
      break;

    case DW_ATE_signed:
    case DW_ATE_signed_char:
      if (basePtr->byte_size == sizeof(char))
        {
          t->declaredType = D_CHAR;
        }
      else if (basePtr->byte_size == sizeof(short))
        {
          t->declaredType = D_SHORT;
        }
      else if (basePtr->byte_size == sizeof(int))
        {
          t->declaredType = D_INT;
        }
      else if (basePtr->byte_size == sizeof(long long int))
        {
          t->declaredType = D_LONG_LONG_INT;
        }

      t->repType = R_INT;
      break;

    case DW_ATE_unsigned:
    case DW_ATE_unsigned_char:
      if (basePtr->byte_size == sizeof(unsigned char))
        {
          t->declaredType = D_UNSIGNED_CHAR;
        }
      else if (basePtr->byte_size == sizeof(unsigned short))
        {
          t->declaredType = D_UNSIGNED_SHORT;
        }
      else if (basePtr->byte_size == sizeof(unsigned int))
        {
          t->declaredType = D_UNSIGNED_INT;
        }
      else if (basePtr->byte_size == sizeof(unsigned long long int))
        {
          t->declaredType = D_UNSIGNED_LONG_LONG_INT;
        }

      t->repType = R_INT;
      break;

    case DW_ATE_boolean:
      t->declaredType = D_BOOL;
      t->repType = R_INT;
      break;

    default:
      tl_assert(0 && "Unknown primitive type");
    }

  t->byteSize = basePtr->byte_size;
}

// Extracts enumeration type info (Daikon represents enums as integers)
// Modifies: t
void extractEnumerationType(DaikonType* t, collection_type* collectionPtr)
{
  t->declaredType = D_ENUMERATION;
  t->collectionName = collectionPtr->name;

  t->repType = R_INT;
  t->byteSize = sizeof(int); // An enumeration is an int
}


// Extracts subroutine type corresponding to a function pointer parameter
// Modifies: t
void extractSubroutineType(DaikonType* t, function_type* functionPtr)
{
  t->byteSize = 1; // TODO: Why does this only take up one byte?
                   // Shouldn't it take up 4?
  t->declaredType = D_FUNCTION;
  t->repType = R_HASHCODE;
}

// Extracts type information from a void pointer
// Modifies: t
void extractVoidType(DaikonType* t)
{
  t->byteSize = 1; // TODO: Why does this only take up one byte?
                   // Shouldn't it take up 4?
  t->declaredType = D_VOID;
  t->repType = R_HASHCODE;
}

// Extracts struct/union type info from collectionPtr and creates
// member variables in t->memberListPtr
void extractStructUnionType(DaikonType* t, dwarf_entry* e)
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
    t->declaredType = D_UNION;
  else
    t->declaredType = D_STRUCT;

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

  // After we are doing constructing the struct DaikonType entry,
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
      DaikonVariable* memberVarPtr = &(memberNodePtr->var);
      structByteSize = memberVarPtr->data_member_location +
	determineDaikonVariableByteSize(memberVarPtr);

      // Round struct size up to the nearest word (multiple of 4)
      t->byteSize = ((structByteSize + 3) >> 2) << 2;

      DPRINTF("collection name: %s, byteSize: %d\n", t->collectionName, t->byteSize);
    }
}


void extractFormalParameterVars(DaikonFunctionInfo* daikonEntry,
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
      extractOneFormalParameterVar(daikonEntry, dwarfFunctionEntry->params[i]);
    }
}


// Extracts only the local variables of type DW_TAG_array_type
// or collection_type (struct/union)
// and places them in the local_vars list within each respective
// function (we need struct types because they may contain static arrays
// or structs which themselves contain static arrays)
void extractLocalArrayAndStructVariables(DaikonFunctionInfo* daikonEntry,
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
      extractOneLocalArrayOrStructVariable(daikonEntry,
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
void verifyStackParamWordAlignment(DaikonFunctionInfo* daikonEntry)
{
  VarNode* cur_node;
  int offset = 8;

  // Start with default offset of 8 from EBP (*EBP = old EBP, *(EBP+4) = return addr)
  // unless the function returns a struct by value - then we start
  // with an offset of 12 since *(EBP+8) = pointer to the place to put the struct)

  DaikonVariable* firstReturnVar = &daikonEntry->returnValue.first->var;
  if (firstReturnVar &&
      (D_STRUCT == firstReturnVar->varType->declaredType) &&
      (0 == firstReturnVar->declaredPtrLevels))
    {
      offset = 12;
    }

  for (cur_node = daikonEntry->formalParameters.first;
       cur_node != NULL;
       cur_node = cur_node->next)
    {
      int cur_byteSize = 0;
      cur_node->var.byteOffset = offset;
      cur_byteSize = determineDaikonVariableByteSize(&(cur_node->var));
      // WORD ALIGNED!!!
      if (cur_byteSize > 0)
	{
	  // Round offset up to the nearest word (4 bytes)
	  offset += (((cur_byteSize + 3) >> 2) << 2);
	}
    }
}

// Returns the byte size of the given DaikonVariable
int determineDaikonVariableByteSize(DaikonVariable* var)
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
int determineFormalParametersStackByteSize(DaikonFunctionInfo* daikonEntry)
{
  VarNode* cur_node;
  int totalByteSize = 0;

  if(!daikonEntry){
    return 0;
  }

  for (cur_node = daikonEntry->formalParameters.first;
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
                       determineDaikonVariableByteSize(&(cur_node->var)));
      // Just to be safe, round UP to the next multiple of 4
      totalByteSize += 4;
      totalByteSize -= (totalByteSize % 4);
    }
  return totalByteSize;
}


// Pre: e->tag_name == DW_TAG_variable
// functionStartPC is the name of the function that this variable belongs to
void extractOneGlobalVariable(dwarf_entry* e, unsigned long functionStartPC)
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


// dwarfParamEntry->tag_name == DW_TAG_formal_parameter
void extractOneFormalParameterVar(DaikonFunctionInfo* daikonEntry,
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
            daikonEntry->name);
    return;
  }

  DPRINTF("  %s parameter name %s\n",
	  daikonEntry->name,
	  paramPtr->name);

  extractOneVariable(&(daikonEntry->formalParameters),
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

// Only adds a new entry if dwarfVariableEntry's type == DW_TAG_array_type
// or collection_type
void extractOneLocalArrayOrStructVariable(DaikonFunctionInfo* daikonEntry,
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
            daikonEntry->name);
    return;
  }

      DPRINTF("  %s local variable name %s - localArrayVariables %p size = %d\n",
	  daikonEntry->name,
	  variablePtr->name,
	  &(daikonEntry->localArrayVariables),
	  daikonEntry->localArrayVariables.numVars);

  extractOneVariable(&(daikonEntry->localArrayVariables),
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

void extractReturnVar(DaikonFunctionInfo* daikonEntry,
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

  daikonEntry->returnValue.numVars = 0;

  extractOneVariable(&(daikonEntry->returnValue),
                     typePtr,
                     DAIKON_RETURN_NAME,
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
			DaikonType* structParentType,
                        char isFormalParam) // All static arrays which are
// formal parameters are treated like NORMAL pointers which are not statically-sized
// just because that's how the C language works
{
  DaikonVariable* daikonVarPtr = 0;
  int newlyAddedTypeEntry = 0;
  int ptrLevels = 0;

  DPRINTF("Entering extractOneVariable for %s\n", variableName);

  // Don't extract the variable if it has a bogus name:
  if (ignore_variable_with_name(variableName))
    return;

  // Create a new DaikonVariable and append it to the end of VarList
  insertNewNode(varListPtr);

  // Work on the last variable in varListPtr
  daikonVarPtr = &(varListPtr->last->var);

  daikonVarPtr->name = variableName;
  daikonVarPtr->fileName = fileName;
  daikonVarPtr->byteOffset = byteOffset;

  // Special case for C++ 'this' parameter variables:
  // Automatically put a 'P' disambig on it because
  // 'this' will always refer to one object and not an array
  // TODO: This will pick up any variable named 'this' so it's possible
  // (I don't know why you would do this) that in a C program, you can have
  // some variable named 'this' and it'll get a 'P' disambig on it
  if (VG_STREQ("this", variableName)) {
    daikonVarPtr->disambig = 'P';
  }

  daikonVarPtr->isGlobal = isGlobal;
  daikonVarPtr->isExternal = isExternal;
  daikonVarPtr->globalLocation = globalLocation;
  daikonVarPtr->functionStartPC = functionStartPC;

  daikonVarPtr->isStructUnionMember = isStructUnionMember;
  daikonVarPtr->data_member_location = data_member_location;
  daikonVarPtr->internalByteSize = internalByteSize;
  daikonVarPtr->internalBitOffset = internalBitOffset;
  daikonVarPtr->internalBitSize = internalBitSize;
  daikonVarPtr->structParentType = structParentType;

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
	  typePtr = extractArrayType(daikonVarPtr, arrayPtr);
	  ptrLevels++;
	}
      else if (tag_is_typedef(typePtr->tag_name))
	{
	  typePtr = ((typedef_type*)typePtr->entry_ptr)->target_type_ptr;
	}
    }

  DPRINTF("Finished stripping modifiers for %s\n", variableName);
  DPRINTF("daikonVarPtr is %p\n", daikonVarPtr);
  DPRINTF("typePtr is %p\n", typePtr);

  daikonVarPtr->repPtrLevels = ptrLevels;
  daikonVarPtr->declaredPtrLevels = ptrLevels;

  if (typePtr && (typePtr->tag_name == DW_TAG_structure_type)) {
    char* type_name = ((collection_type*)(typePtr->entry_ptr))->name;
    // We want to ignore POINTERS to certain types (don't ignore
    // the actual values of that type because it may screw up alignments).
    // Instead, we want to convert these into generic void pointers.
    if ((daikonVarPtr->declaredPtrLevels > 0) &&
        ignore_type_with_name(type_name)) {
      //      VG_(printf)("IGNORED --- %s\n", type_name);
      daikonVarPtr->varType = &GlobalHashcodeType;
      return; // punt at this point
    }
  }

  // Formal parameters which appear to be statically-sized arrays are
  // actually simply pointers:
  if (isFormalParam && daikonVarPtr->isStaticArray) {
    daikonVarPtr->isStaticArray = 0;
  }

  // Link it to a DaikonType if one already exists
  daikonVarPtr->varType = 0;
  // We are passing in the true ID but casting it so the compiler won't warn me:

  if (typePtr)
    {
      // We want to look up the REAL type entry, not a fake one with
      // is_declaration non-null.
      //   (Hopefully, if all goes well, the only DaikonType values
      //    in DaikonTypesTable are REAL entries whose dwarf_entry has
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
            daikonVarPtr->varType =
              (DaikonType*)gengettable(DaikonTypesTable, (void*)realID);

            // If you can't find anything, we'll have to end up calling
            // extractStructUnionType so let's change typePtr to refer
            // to the entry in dwarf_entry_array with the REAL ID before
            // passing it further along:
            if (!daikonVarPtr->varType) {
              unsigned long realIndex = 0;
              if (binary_search_dwarf_entry_array(realID,  &realIndex)) {
                typePtr = &dwarf_entry_array[realIndex];

                //                VG_(printf)("  realIndex: %u, realID: %u, typePtr->ID: %u\n",
                //                            realIndex, realID, typePtr->ID);
              }
            }
          }
          else {
            daikonVarPtr->varType = (DaikonType*)gengettable(DaikonTypesTable, (void*)typePtr->ID);
          }
        }
        // Do a regular lookup if it's either an unnamed struct or
        // (even better) a REAL one with is_declaration = null
        else {
          daikonVarPtr->varType = (DaikonType*)gengettable(DaikonTypesTable, (void*)typePtr->ID);
        }
      }
      // Just do a lookup for non-struct/union types
      else {
        daikonVarPtr->varType = (DaikonType*)gengettable(DaikonTypesTable, (void*)typePtr->ID);
      }
    }
  // If the entry is not found in DaikonTypesTable, create a new one
  // and add it to the table
  if (!daikonVarPtr->varType)
    {
      DPRINTF("Adding type entry for %s\n", variableName);

      daikonVarPtr->varType = (DaikonType*)VG_(calloc)(1, sizeof(*daikonVarPtr->varType));
      // We are passing in the true ID but casting it so the compiler won't warn me:
      if (typePtr) {
        genputtable(DaikonTypesTable, (void*)typePtr->ID, daikonVarPtr->varType);
      }
      newlyAddedTypeEntry = 1;
    }

  if (newlyAddedTypeEntry)
    {
       // WARNING: Some typedefs do not have targets - if typePtr == NULL,
       // just say screw it and make this variable into a dummy null variable:
       // Void typePtr entries will NOT be in DaikonTypesTable :(
      if (!typePtr)
	{
	  // Got void; probably was void *, const void *, etc.
	  extractVoidType(daikonVarPtr->varType);
	}
      // If the parameter type is a basic type, then we're golden!
      // Base types are the easiest to handle!
      else if (tag_is_base_type(typePtr->tag_name))
	{
	  base_type* basePtr = (base_type*)(typePtr->entry_ptr);
	  extractBaseType(daikonVarPtr->varType, basePtr);
	}
      // If the parameter is an enumeration type
      else if (typePtr->tag_name == DW_TAG_enumeration_type)
	{
	  collection_type* collectionPtr = (collection_type*)(typePtr->entry_ptr);
	  extractEnumerationType(daikonVarPtr->varType, collectionPtr);
	}
      else if (typePtr->tag_name == DW_TAG_subroutine_type)
	{
	  // Function (from a function pointer)
	  // Treat sorta like a hashcode, for the moment.
	  function_type* func_type = (function_type *)(typePtr->entry_ptr);
	  extractSubroutineType(daikonVarPtr->varType, func_type);
	}
      // Struct or union type
      else if  ((typePtr->tag_name == DW_TAG_structure_type) ||
		(typePtr->tag_name == DW_TAG_union_type))
	{
          extractStructUnionType(daikonVarPtr->varType, typePtr);
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
  if ((daikonVarPtr->varType->declaredType == D_CHAR) &&
      (daikonVarPtr->repPtrLevels > 0))
    {
      daikonVarPtr->isString = 1;
      daikonVarPtr->repPtrLevels--;
    }

  // TODO: What about arrays of pointers?  int* [10] currently turns
  // into base type = int, ptrLevels = 2, isStaticArray = true
  // but it should be base type = hashcode, ptrLevels = 1, isStaticArray = true

  // Proposed solution: If isStaticArray = true and (ptrLevels > 1 and
  // daikonVarPtr->varType->declaredType != D_CHAR) or (ptrLevels > 2 and
  // daikonVarPtr->varType->declaredType == D_CHAR), then
  // we turn it into a 1-D array of hashcodes by setting ptrLevels = 1
  // and pointing the type to GlobalHashcodeType.
  // This means that we do not support multidimensional arrays
  // (but we didn't used to either) but fail more gracefully on them now
  if (daikonVarPtr->isStaticArray &&
      (ptrLevels > ((daikonVarPtr->varType->declaredType == D_CHAR) ?
                    2 : 1))) {
    daikonVarPtr->repPtrLevels = 1;
    daikonVarPtr->declaredPtrLevels = 1;
    daikonVarPtr->varType = &GlobalHashcodeType;
  }
}

void printDaikonFunctionInfoTable()
{
  VarNode* formalParamNode = 0;
  VarNode* localArrayVarNode = 0;
  VarNode* returnVarNode = 0;
  DaikonFunctionInfo* cur_entry;
  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);

  while (!it->finished)
    {
      cur_entry = (DaikonFunctionInfo*)
        gengettable(DaikonFunctionInfoTable, gennext(it));

      if (!cur_entry)
        continue;

      printf("\n%s (%s) startPC=%p\n\n",
             cur_entry->daikon_name,
             cur_entry->filename,
	     (void*)cur_entry->startPC);

      for (formalParamNode = cur_entry->formalParameters.first;
           formalParamNode != 0; formalParamNode = formalParamNode->next)
        {
          printf("  PARAM: ");
          printOneDaikonVariable(&(formalParamNode->var), 0, 1);
        }

      for (localArrayVarNode = cur_entry->localArrayVariables.first;
           localArrayVarNode != 0; localArrayVarNode = localArrayVarNode->next)
        {
          printf("  LOCAL: ");
          printOneDaikonVariable(&(localArrayVarNode->var), 0, 1);
        }

      for (returnVarNode = cur_entry->returnValue.first;
           returnVarNode != 0; returnVarNode = returnVarNode->next)
        {
          printf("  RETURN: ");
          printOneDaikonVariable(&(returnVarNode->var), 0, 1);
        }
    }

  genfreeiterator(it);
}

void printDaikonGlobalVars()
{
  VarNode* globalVarNode = 0;

  printf("\nGlobal variables:\n\n");

  for (globalVarNode = globalVars.first;
       globalVarNode != 0;
       globalVarNode = globalVarNode->next)
    {
          printf("  GLOBAL: ");
          printOneDaikonVariable(&(globalVarNode->var), 0, 1);
    }
}

void printVariablesInList(VarList* varListPtr, int leadingSpaces, DaikonType* structType)
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
	  printOneDaikonVariable(&(curNode->var), 1, 0);
	}
      else
	{
	  printOneDaikonVariable(&(curNode->var), 0, 0);
	}
    }
}

// Prints one DaikonVariable on one line followed by the type information
// of its DaikonType on the next line and then a newline
void printOneDaikonVariable(DaikonVariable* var, char doNotRecurse, char firstTimePrinting)
{
  DaikonType* t;
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
      printf("\n     %s, decType: %s, repType: %s, byteSize: %d",
	     t->collectionName,
	     DaikonDeclaredTypeNames[t->declaredType],
	     DaikonRepTypeNames[t->repType],
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

// Pre: All entries in DaikonTypesTable have already been set
//      so run this AFTER we've set up all the stuff in DaikonTypesTable
// Effect: Iterate through all collection (Struct/Union/Class)
// entries in DaikonTypesTable, and for each one, iterate
// through its member_funcs_array, visit every member function
// in there, and set each one's parentClass field to this struct
void initializeAllClassMemberFunctions() {
  struct geniterator* it = gengetiterator(DaikonTypesTable);
  UInt i;
  // Iterate through member_funcs and set the classParent
  // field of each member function entry in DaikonFunctionInfoTable
  // to point to this struct t

  while (!it->finished) {
    DaikonType* t = (DaikonType*)
      gengettable(DaikonTypesTable, gennext(it));

    // Skip unnamed structs or types which aren't structs
    if (!t->collectionName) {
      continue;
    }

    //    VG_(printf)("STRUCT %s\n", t->collectionName);
    for (i = 0; i < t->num_member_funcs; i++) {
      function* funcPtr = (function*)((t->member_funcs[i])->entry_ptr);

      DaikonFunctionInfo* entry = findFunctionInfoByStartAddr(funcPtr->start_pc);
      if (entry) {
        //        VG_(printf)("   member function: %s (%s)\n",
        //                    entry->name, entry->mangled_name);
        entry->parentClass = t;
      }
    }
  }
  genfreeiterator(it);
}

// DaikonTypesTable - hash table containing DaikonType entries
// DaikonFunctionInfoTable - hash table containing DaikonFunctionInfo entries
// Super-trivial division hashing method - do nothing, hehe, ummm, we could
// improve upon this to increase efficiency, but I don't care right now
unsigned int hashID(int ID) {
  return ID;
}

// Super-trivial key comparison method -
int equivalentIDs(int ID1, int ID2) {
  return (ID1 == ID2);
}


// DaikonFunctionInfoTable

// This is SLOW because we must traverse all values,
// looking for the Daikon name
DaikonFunctionInfo* findFunctionInfoByDaikonNameSlow(char* daikon_name) {
  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);
  DaikonFunctionInfo* entry = 0;

  while (!it->finished) {

    entry = (DaikonFunctionInfo*)
      gengettable(DaikonFunctionInfoTable, gennext(it));

    if (!entry)
      continue;

    if (VG_STREQ(entry->daikon_name, daikon_name)) {
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
DaikonFunctionInfo* findFunctionInfoByAddrSlow(unsigned int addr) {
  struct geniterator* it = gengetiterator(DaikonFunctionInfoTable);
  DaikonFunctionInfo* entry = 0;

  while (!it->finished) {

    entry = (DaikonFunctionInfo*)
      gengettable(DaikonFunctionInfoTable, gennext(it));

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
inline DaikonFunctionInfo* findFunctionInfoByStartAddr(unsigned int startPC) {
  return (DaikonFunctionInfo*)gengettable(DaikonFunctionInfoTable, (void*)startPC);
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


// Returns the first DaikonType entry found in DaikonTypesTable with
// collectionName matching the given name, and return 0 if nothing
// found.
DaikonType* findDaikonTypeByName(char* name) {
  struct geniterator* it = gengetiterator(DaikonTypesTable);

  while (!it->finished) {
    DaikonType* cur_type = (DaikonType*)
      gengettable(DaikonTypesTable, gennext(it));

    if (cur_type->collectionName &&
        VG_STREQ(cur_type->collectionName, name)) {
      genfreeiterator(it);
      return cur_type;
    }
  }

  genfreeiterator(it);
  return 0;
}
