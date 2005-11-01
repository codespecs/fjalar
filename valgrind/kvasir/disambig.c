/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* disambig.c:
   Implements the pointer-type disambiguation feature of Kvasir
   (--disambig and --disambig-file=<string> command-line options)
*/

#include "disambig.h"
#include "kvasir_main.h"
#include "decls-output.h"
#include "generate_daikon_data.h"
#include "GenericHashtable.h"
#include <stdlib.h>
#include <string.h>

FILE* disambig_fp = 0; // File pointer for either reading or writing to .disambig file
Bool disambig_writing = False; // True for writing to .disambig, False for reading
// Invariant: If disambig_writing = True, then disambig_fp is valid

// For struct/union types:
const char* USERTYPE_PREFIX = "usertype.";
const char* FUNCTION_PREFIX = "function: ";

// Pre: disambig_fp has been initialized and disambig_writing is True
void generateDisambigFile() {
  struct geniterator* it = 0;
  struct geniterator* DaikonFunctionInfoIt = 0;
  DaikonFunctionInfo* cur_func_info_entry = 0;

  // Hashtable which contains the names of structs already printed in
  // the .disambig file.  This is so that we can allow duplicate entries
  // in DaikonTypesTable but only print out ONE "usertype" section for each
  // entry with a particular name.
  // Key: Class name, Value: Doesn't matter - we only check if the table
  // "contains the entry"
  struct genhashtable* UsertypeNamesAlreadyPrinted =
    genallocatehashtable((unsigned int (*)(void *)) & hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  VG_(printf)("\nBegin generating disambiguation file: \"%s\" ...\n",
              kvasir_disambig_filename);

  if (!disambig_writing || !disambig_fp) {
    VG_(printf)( "Error. There is no .disambig file to write in generateDisambigFile()");
    return;
  }

  // Print out a .disambig section for each function
  DaikonFunctionInfoIt = gengetiterator(DaikonFunctionInfoTable);

  while (!DaikonFunctionInfoIt->finished)
    {
      cur_func_info_entry = (DaikonFunctionInfo*)
        gengettable(DaikonFunctionInfoTable, gennext(DaikonFunctionInfoIt));

      if (!cur_func_info_entry)
        continue;

      if (!kvasir_trace_prog_pts_filename ||
          // If kvasir_trace_prog_pts_filename is on (we are reading in
          // a ppt list file), then DO NOT OUTPUT .disambig entries for
          // program points that we are not interested in tracing.  This
          // decreases the clutter of the .decls file and speeds up
          // processing time
          prog_pts_tree_entry_found(cur_func_info_entry)) {
        fputs(ENTRY_DELIMETER, disambig_fp);
        fputs("\n", disambig_fp);
        printOneFunctionDisambig(cur_func_info_entry);
      }
    }

  // Print out a .disambig section for globals
  fputs(ENTRY_DELIMETER, disambig_fp);
  fputs("\n", disambig_fp);

  fputs(GLOBAL_STRING, disambig_fp);
  fputs("\n", disambig_fp);
  printVariablesInVarList(0, 0, GLOBAL_VAR, 0,
			  DISAMBIG_FILE, 0, 0, 0, 0);

  // Print out a .disambig section for each
  // aggregate (struct/union) type,
  // with each type's name preceded by "usertype."
  /*
    usertype.fooStruct
    firstMember
    A
    secondMember
    P
    ...
  */

  // Iterate through all DaikonType entries in
  // DaikonTypesTable and pick out struct/union types:
  it = gengetiterator(DaikonTypesTable);

  while (!it->finished) {
     DaikonType* cur_type = (DaikonType*)
       gengettable(DaikonTypesTable, gennext(it));

     if (!cur_type)
       continue;

     // Pick off struct/union types
     // TODO: We currently support only structs/unions
     // which are named (i.e. NOT those anonymous
     // ones which are declared within other types) ...
     // In the future, we may want to have a serial
     // naming system for unnamed structs/unions so that
     // we can uniquely identify unnamed ones
     // (We have implemented a technique where we use the ID
     //  fields of the entries in the DWARF2 info to uniquely
     //  identify unnamed structs/unions)
     //
     // Remember to NOT PRINT OUT DUPLICATE ENTRIES, those with the
     // same name in DaikonTypesTable!  An irritating thing about the
     // DWARF2 debugging information is that it can contain multiple
     // entries for the SAME struct type.  When we read in the
     // .disambig file in processDisambigFile(), we assign the
     // disambiguation properties to ALL the entries in
     // DaikonTypesTable with the matching name.
     if (((cur_type->declaredType == D_STRUCT) ||
	  (cur_type->declaredType == D_UNION))
	 && cur_type->collectionName &&
         !gencontains(UsertypeNamesAlreadyPrinted, cur_type->collectionName)) {

       char* typeName = cur_type->collectionName;
       VarNode* cur_node = 0;

       //       VG_(printf)("TYPE NAME: %s\n", cur_type->collectionName);

       fputs("\n", disambig_fp);

       fputs(ENTRY_DELIMETER, disambig_fp);
       fputs("\n", disambig_fp);
       fputs(USERTYPE_PREFIX, disambig_fp);
       fputs(typeName, disambig_fp);
       fputs("\n", disambig_fp);

       // Iterate through each member of the struct
       // and print out its information:
       for (cur_node = cur_type->memberListPtr->first;
	    cur_node != 0; cur_node = cur_node->next) {

	 DaikonVariable* var = &(cur_node->var);

	 // Only output certain member variables
	 // to .disambig
	 if (!shouldOutputVarToDisambig(var)) {
	   continue;
	 }

	 stringStackPush(fullNameStack, &fullNameStackSize, var->name);

         visitVariable(var,
                       0,
                       0,
                       GLOBAL_VAR, // TODO: Check to make sure this is okay
                       DISAMBIG_FILE,
                       0,
                       0,
                       0,
                       0);

	 stringStackPop(fullNameStack, &fullNameStackSize);
       }

       genputtable(UsertypeNamesAlreadyPrinted, cur_type->collectionName, 0);
     }
  }

  genfreeiterator(it);
  genfreeiterator(DaikonFunctionInfoIt);
  genfreehashtable(UsertypeNamesAlreadyPrinted);

  VG_(printf)("Done generating disambiguation file: \"%s\"\n\n",
              kvasir_disambig_filename);

  if (disambig_fp) {
    fclose(disambig_fp);
    disambig_fp = 0;
  }
}

// Pre: disambig_writing = True and disambig_fp is initialized
void printOneFunctionDisambig(DaikonFunctionInfo* funcPtr) {
  fputs(FUNCTION_PREFIX, disambig_fp);
  fputs(funcPtr->daikon_name, disambig_fp);
  fputs("\n", disambig_fp);

  // We only want one disambig section for each function, so just
  // pretend like it's the EXIT section.

  // Now print out one entry for every formal parameter (actual and derived)
  printVariablesInVarList(funcPtr, 0,
			   FUNCTION_EXIT_FORMAL_PARAM,
			  0, DISAMBIG_FILE, 0, 0, 0, 0);

  // Print out return value
  printVariablesInVarList(funcPtr, 0, FUNCTION_RETURN_VAR, 0,
                          DISAMBIG_FILE, 0, 0, 0, 0);

  fputs("\n", disambig_fp);
}

// Returns True if var should be output to .disambig:
// - Any var of type "char" or "unsigned char"
// - Any pointer
Bool shouldOutputVarToDisambig(DaikonVariable* var) {
  if (var->declaredPtrLevels > 0) {
    return True;
  }
  else if ((D_UNSIGNED_CHAR == var->varType->declaredType) ||
	   (D_CHAR == var->varType->declaredType)) {
    return True;
  }
  else {
    return False;
  }
}

// Returns a DisambigOverride value read from 'var':
DisambigOverride returnDisambigOverride(DaikonVariable* var) {
  DisambigOverride override = OVERRIDE_NONE;

  if ((kvasir_disambig_filename && !disambig_writing) || // When we are reading .disambig file
      VG_STREQ("this", var->name)) { // Always disambiguate C++ 'this' variable
    char disambig_letter = disambig_letter = var->disambig;

    if (disambig_letter) {
      if (var->repPtrLevels == 0) {
	// 'C' denotes to print out as a one-character string
	if (var->isString) { // pointer to "char" or "unsigned char"
	  if ('C' == disambig_letter) {
	    DPRINTF("String C - %s\n\n", var->name);
	    override = OVERRIDE_STRING_AS_ONE_CHAR_STRING;
	  }
	  else if ('A' == disambig_letter) {
	    DPRINTF("String A - %s\n\n", var->name);
	    override = OVERRIDE_STRING_AS_INT_ARRAY;
	  }
	  else if ('P' == disambig_letter) {
	    DPRINTF("String P - %s\n\n", var->name);
	    override = OVERRIDE_STRING_AS_ONE_INT;
	  }
	}
	else if ((D_CHAR == var->varType->declaredType) ||  // "char" or "unsigned char" (or string of chars)
		 (D_UNSIGNED_CHAR == var->varType->declaredType)) { // "char" or "unsigned char"
	  if ('C' == disambig_letter) {
	    DPRINTF("Char C - %s\n\n", var->name);
	    override = OVERRIDE_CHAR_AS_STRING;
	  }
	}
      }
      // Ordinary pointer
      else if ('P' == disambig_letter) {
	override = OVERRIDE_ARRAY_AS_POINTER;
      }
    }
  }

  return override;
}


// Reads in a .disambig file and inserts the appropriate .disambig info
// into each DaikonVariable
// Pre: DaikonFunctionInfoTable and globalVars are initialized so that
//      we can directly modify the DaikonVariable entries within those structures;
//      disambig_fp is valid and disambig_writing = False
//      * Run AFTER updateAllDaikonFunctionInfoEntries() so that
//        DaikonVariable names are properly initialized
void processDisambigFile() {
  // TODO: This is crude and unsafe but works for now
  char line[200];
  char nextLineIsEntry = 0;
  int lineLen = 0;
  DisambigEntryType type = NONE;
  char* entryName = 0; // either a function or struct name
                       // Only relevant when type == {FUNCTION, USERTYPE}

  VarList** VarListArray = 0; // Array of VarList* of size VarListArraySize
  int VarListArraySize = 0;

  if (!disambig_fp || disambig_writing) {
    VG_(printf)( "Error in processDisambigFile(). Either there is no disambig_file or it is being written.");
    return;
  }

  while (fgets(line, 200, disambig_fp)) {
    lineLen = VG_(strlen)(line);

    // Blank lines only have a "\n" so skip them
    if (lineLen <= 1)
      continue;

    // Strip '\n' off the end of the line
    // NOTE: Only do this if the end of the line is a newline character.
    // If the very last line of a file is not followed by a newline character,
    // then blindly stripping off the last character will truncate the actual
    // string, which is undesirable.
    if (line[lineLen - 1] == '\n') {
      line[lineLen - 1] = '\0';
    }

    if VG_STREQ(line, ENTRY_DELIMETER) {
      if (entryName) {
	VG_(free)(entryName);
	entryName = 0;
      }

      if (VarListArray) {
	VG_(free)(VarListArray);
	VarListArray = 0;
	VarListArraySize = 0;
      }

      nextLineIsEntry = 1;
    }
    else {
      // 3 possibilities for an entry:
      //   1) A function name - e.g. "..foo()"
      //   2) "globals"
      //   3) A user-defined type (ie. struct) name - e.g. "usertype.fooStruct"
      if (nextLineIsEntry) {
	char* marker = 0;
	// 1) A function name
	if ((marker = strstr(line, FUNCTION_PREFIX))) {
          DaikonFunctionInfo* cur_entry = 0;
	  DPRINTF("FUNCTION_PREFIX");
	  type = FUNCTION;
	  // Strip off the prefix by moving forward that many spots in the buffer:
	  entryName = VG_(strdup)(&line[VG_(strlen)(FUNCTION_PREFIX)]);
          //          VG_(printf)("Function! %s\n", entryName);

	  VarListArraySize = 1;
	  VarListArray = (VarList**)VG_(calloc)(VarListArraySize, sizeof(*VarListArray));

	  // Find the appropriate function by name:
          cur_entry = findFunctionInfoByDaikonNameSlow(entryName);
          if (cur_entry) {
            VarListArray[0] = &(cur_entry->formalParameters);
          }
	}
	// 2) "globals"
	else if (VG_STREQ(line, GLOBAL_STRING)) {
	  type = GLOBAL;
	  DPRINTF("GLOBAL");
	  VarListArraySize = 1;
	  VarListArray = (VarList**)VG_(calloc)(VarListArraySize, sizeof(*VarListArray));

	  VarListArray[0] = &globalVars;
	}
	// 3) A user-defined type
	//    (USERTYPE_PREFIX must be the prefix of the string)
	else if (strstr(line, USERTYPE_PREFIX) == line) {
          struct geniterator* it = 0;
          int i = 0;
	  type = USERTYPE;
	  DPRINTF("USERTYPE");
	  // Strip off the prefix:
	  entryName = VG_(strdup)(line + VG_(strlen)(USERTYPE_PREFIX));

	  // Find ALL THE DaikonType entries with the matching name
	  // and throw their memberListPtr entries in VarListArray
	  // This is due to the fact that DWARF debugging info allows
	  // multiple identical DaikonType entries (with the same
	  // name) to co-exist since struct DWARF entries are replicated
	  // for every compilation unit which includes the struct's definition

	  // Go through it TWICE - the first time we look up how many entries
	  // there are so we can set the size for VarListArray
	  // and the second time we actually fill up VarListArray

	  VarListArraySize = 0;

	  it = gengetiterator(DaikonTypesTable);

	  while (!it->finished) {
	    DaikonType* cur_type = (DaikonType*)
	      gengettable(DaikonTypesTable, gennext(it));

	    if (cur_type->collectionName &&
		VG_STREQ(cur_type->collectionName, entryName)) {
	      DPRINTF(" FAKE [%s]\n", cur_type->collectionName);
	      VarListArraySize++;
	    }
	  }

	  genfreeiterator(it);

	  VarListArray = (VarList**)VG_(calloc)(VarListArraySize, sizeof(*VarListArray));

	  it = gengetiterator(DaikonTypesTable);
	  i = 0;

	  while (!it->finished) {
	    DaikonType* cur_type = (DaikonType*)
	      gengettable(DaikonTypesTable, gennext(it));

	    if (cur_type->collectionName &&
		VG_STREQ(cur_type->collectionName, entryName)) {
	      DPRINTF(" REAL [%s]\n", cur_type->collectionName);
	      VarListArray[i] = cur_type->memberListPtr;
	      i++;
	    }
	  }

	  genfreeiterator(it);
	}

	DPRINTF(" ENTRY: %s\n", (entryName ? entryName : "<no name>"));
      }
      // A line that doesn't immediately follow ENTRY_DELIMETER
      // The idea here is to find the correct DaikonVariable entry and
      // modify its "disambig" field
      else {
	DaikonVariable* target = 0;

	char* varName = VG_(strdup)(line);
        char disambig_letter;

	// Eat up the next line, which should be just one character:
	fgets(line, 10, disambig_fp);
	disambig_letter = line[0];

	if (VarListArraySize > 0) {
	  int j;
	  // Iterate through all VarList* entries in VarListArray
	  for (j = 0; j < VarListArraySize; j++) {
	    VarList* varList = VarListArray[j];

	    VarNode* i;

	    for (i = varList->first; i != 0; i = i->next) {
	      DaikonVariable* var = &(i->var);
	      if (VG_STREQ(varName, var->name)) {
		target = var;
		break;
	      }
	    }

	    if (target) {
	      switch (type) {
	      case FUNCTION:
		target->disambig = disambig_letter;
		break;
	      case GLOBAL:
	      case USERTYPE:
		target->disambig = disambig_letter;
		break;
	      default:
		break;
	      }

	      DPRINTF("VarListArray[%d]: var:%s [%c]\n", j, target->name, target->disambig);
	    }
	  }
	}
	VG_(free)(varName);
      }

      nextLineIsEntry = 0;
    }
  }

  fclose(disambig_fp);
  disambig_fp = 0;
}
