/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* disambig.c:
   Implements the pointer-type disambiguation feature of Fjalar
   (--disambig and --disambig-file=<string> command-line options)
*/

#include "disambig.h"
#include "fjalar_main.h"
#include "fjalar_select.h"
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
  VG_(printf)("\ngenerateDisambigFile() not yet implemented\n");
}

// Returns True if var should be output to .disambig:
// - Any var of type "char" or "unsigned char"
// - Any pointer
Bool shouldOutputVarToDisambig(VariableEntry* var) {
  if (var->ptrLevels > 0) {
    return True;
  }
  else if ((D_UNSIGNED_CHAR == var->varType->decType) ||
	   (D_CHAR == var->varType->decType)) {
    return True;
  }
  else {
    return False;
  }
}

// Returns a DisambigOverride value read from 'var':
DisambigOverride returnDisambigOverride(VariableEntry* var) {
  DisambigOverride override = OVERRIDE_NONE;

  if ((fjalar_disambig_filename && !disambig_writing) || // When we are reading .disambig file
      VG_STREQ("this", var->name)) { // Always disambiguate C++ 'this' variable
    char disambig_letter = disambig_letter = var->disambig;

    if (disambig_letter) {
      if ((!var->isString && (var->ptrLevels == 0)) ||
	  (var->isString && (var->ptrLevels == 1))) {
	// 'C' denotes to print out as a one-character string
	if (var->isString) { // pointer to "char" or "unsigned char"
	  if ('C' == disambig_letter) {
	    FJALAR_DPRINTF("String C - %s\n\n", var->name);
	    override = OVERRIDE_STRING_AS_ONE_CHAR_STRING;
	  }
	  else if ('A' == disambig_letter) {
	    FJALAR_DPRINTF("String A - %s\n\n", var->name);
	    override = OVERRIDE_STRING_AS_INT_ARRAY;
	  }
	  else if ('P' == disambig_letter) {
	    FJALAR_DPRINTF("String P - %s\n\n", var->name);
	    override = OVERRIDE_STRING_AS_ONE_INT;
	  }
	}
	else if ((D_CHAR == var->varType->decType) ||  // "char" or "unsigned char" (or string of chars)
		 (D_UNSIGNED_CHAR == var->varType->decType)) { // "char" or "unsigned char"
	  if ('C' == disambig_letter) {
	    FJALAR_DPRINTF("Char C - %s\n\n", var->name);
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
// into each VariableEntry
// Pre: FunctionTable and globalVars are initialized so that
//      we can directly modify the VariableEntry entries within those structures;
//      disambig_fp is valid and disambig_writing = False
//      * Run AFTER updateAllFunctionEntries() so that
//        VariableEntry names are properly initialized
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
          FunctionEntry* cur_entry = 0;
	  FJALAR_DPRINTF("FUNCTION_PREFIX");
	  type = FUNCTION;
	  // Strip off the prefix by moving forward that many spots in the buffer:
	  entryName = VG_(strdup)(&line[VG_(strlen)(FUNCTION_PREFIX)]);
          //          VG_(printf)("Function! %s\n", entryName);

	  VarListArraySize = 1;
	  VarListArray = (VarList**)VG_(calloc)(VarListArraySize, sizeof(*VarListArray));

	  // Find the appropriate function by name:
          cur_entry = findFunctionEntryByFjalarNameSlow(entryName);
          if (cur_entry) {
            VarListArray[0] = &(cur_entry->formalParameters);
          }
	}
	// 2) "globals"
	else if (VG_STREQ(line, GLOBAL_STRING)) {
	  type = GLOBAL;
	  FJALAR_DPRINTF("GLOBAL");
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
	  FJALAR_DPRINTF("USERTYPE");
	  // Strip off the prefix:
	  entryName = VG_(strdup)(line + VG_(strlen)(USERTYPE_PREFIX));

	  // Find ALL THE TypeEntry entries with the matching name
	  // and throw their memberVarList entries in VarListArray
	  // This is due to the fact that DWARF debugging info allows
	  // multiple identical TypeEntry entries (with the same
	  // name) to co-exist since struct DWARF entries are replicated
	  // for every compilation unit which includes the struct's definition

	  // Go through it TWICE - the first time we look up how many entries
	  // there are so we can set the size for VarListArray
	  // and the second time we actually fill up VarListArray

	  VarListArraySize = 0;

	  it = gengetiterator(TypesTable);

	  while (!it->finished) {
	    TypeEntry* cur_type = (TypeEntry*)
	      gengettable(TypesTable, gennext(it));

	    if (cur_type->collectionName &&
		VG_STREQ(cur_type->collectionName, entryName)) {
	      FJALAR_DPRINTF(" FAKE [%s]\n", cur_type->collectionName);
	      VarListArraySize++;
	    }
	  }

	  genfreeiterator(it);

	  VarListArray = (VarList**)VG_(calloc)(VarListArraySize, sizeof(*VarListArray));

	  it = gengetiterator(TypesTable);
	  i = 0;

	  while (!it->finished) {
	    TypeEntry* cur_type = (TypeEntry*)
	      gengettable(TypesTable, gennext(it));

	    if (cur_type->collectionName &&
		VG_STREQ(cur_type->collectionName, entryName)) {
	      FJALAR_DPRINTF(" REAL [%s]\n", cur_type->collectionName);
	      VarListArray[i] = cur_type->memberVarList;
	      i++;
	    }
	  }

	  genfreeiterator(it);
	}

	FJALAR_DPRINTF(" ENTRY: %s\n", (entryName ? entryName : "<no name>"));
      }
      // A line that doesn't immediately follow ENTRY_DELIMETER
      // The idea here is to find the correct VariableEntry entry and
      // modify its "disambig" field
      else {
	VariableEntry* target = 0;

	char* varName = VG_(strdup)(line);
        char* disambigLine = 0;

        char* firstToken = 0;
        char* secondToken = 0;

        char disambig_letter;
        char* coercion_type = 0;

	// Eat up the next line
        // There are two possibilities here:
        //   1.) It is just a single disambig letter (e.g., "A", "P")
        //   2.) It consists of a type coercion statement after the
        //   single disambig letter (e.g., "P foo_type")
	fgets(line, 200, disambig_fp);
        lineLen = VG_(strlen)(line);
        // Strip '\n' off the end of the line
        // NOTE: Only do this if the end of the line is a newline character.
        // If the very last line of a file is not followed by a newline character,
        // then blindly stripping off the last character will truncate the actual
        // string, which is undesirable.
        if (line[lineLen - 1] == '\n') {
          line[lineLen - 1] = '\0';
        }

        disambigLine = VG_(strdup)(line);

        firstToken = strtok(disambigLine, " ");
        secondToken = strtok(NULL, " ");

        //        VG_(printf)(" first_token: %s| second_token: %s|\n",
        //                    firstToken, secondToken);

        // The first token should always be the disambig letter
        tl_assert(VG_(strlen)(firstToken) == 1);
	disambig_letter = *firstToken;

        //        VG_(printf)(" var_name: %s\n", varName);
        //        VG_(printf)("  disambig_letter: %c\n", disambig_letter);

        // If the second token is non-empty, then it is the coercion type
        if (secondToken) {
          coercion_type = secondToken;
          //          VG_(printf)("  coercion_type: %s\n", coercion_type);
        }

	if (VarListArraySize > 0) {
	  int j;
	  // Iterate through all VarList* entries in VarListArray
	  for (j = 0; j < VarListArraySize; j++) {
	    VarList* varList = VarListArray[j];

	    VarNode* i;

	    for (i = varList->first; i != 0; i = i->next) {
	      VariableEntry* var = i->var;
	      if (VG_STREQ(varName, var->name)) {
		target = var;
		break;
	      }
	    }

	    if (target) {
	      switch (type) {
	      case FUNCTION:
	      case GLOBAL:
	      case USERTYPE:
		target->disambig = disambig_letter;
                // Change the type of the variable to point to the one
                // named by coercion_type:
                if (coercion_type) {
                  TypeEntry* new_type = findTypeEntryByName(coercion_type);
                  if (new_type) {
                    target->varType = new_type;
                    VG_(printf)("  .disambig: Coerced variable %s into type '%s'\n",
                                varName, coercion_type);
                  }
                }
		break;
	      default:
		break;
	      }

	      FJALAR_DPRINTF("VarListArray[%d]: var:%s [%c]\n", j, target->name, target->disambig);
	    }
	  }
	}
	VG_(free)(varName);
        VG_(free)(disambigLine);
      }

      nextLineIsEntry = 0;
    }
  }

  fclose(disambig_fp);
  disambig_fp = 0;
}
