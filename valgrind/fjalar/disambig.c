/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* disambig.c:
   Implements the pointer-type disambiguation feature of Fjalar
   (--disambig and --disambig-file=<string> command-line options)
*/

#include "my_libc.h"

#include "disambig.h"
#include "fjalar_main.h"
#include "fjalar_select.h"
#include "fjalar_traversal.h"
#include "GenericHashtable.h"

FILE* disambig_fp = 0; // File pointer for either reading or writing to .disambig file
Bool disambig_writing = False; // True for writing to .disambig, False for reading
// Invariant: If disambig_writing = True, then disambig_fp is valid

// For struct/union types:
const char* USERTYPE_PREFIX = "usertype.";
const char* FUNCTION_PREFIX = "function: ";

static Bool shouldOutputVarToDisambig(VariableEntry* var);
static void processDisambigFile(void);

// Call this AFTER initializeAllFjalarData() so that all relevant data
// structures are already initialized.
// Try to open a .disambig file for reading, but if it doesn't exist,
// create a new file by writing to it.
// Pre: fjalar_disambig_filename is non-null
void handleDisambigFile() {
  tl_assert(fjalar_disambig_filename);

  if ((disambig_fp = fopen(fjalar_disambig_filename, "r"))) {
    FJALAR_DPRINTF("\n\nREADING %s\n", fjalar_disambig_filename);
    disambig_writing = False;

    printf( "\nBegin processing disambiguation file \"%s\" ...\n",
                 fjalar_disambig_filename);

    processDisambigFile();

    printf( "Done processing disambiguation file \"%s\"\n",
                 fjalar_disambig_filename);
  }
  else if ((disambig_fp = fopen(fjalar_disambig_filename, "wx"))) {
    FJALAR_DPRINTF("\n\nWRITING %s\n", fjalar_disambig_filename);
    disambig_writing = True;

    // If we are writing a .disambig file, then we always want to
    // visit all the struct variables so that we can generate
    // .disambig entries for them:
    fjalar_output_struct_vars = True;

    // If fjalar_smart_disambig is on, then we need to wait until the
    // END of program execution before printing out the .disambig
    // information (see fjalar_finish()):
    if (!fjalar_smart_disambig) {
      generateDisambigFile();
      printf("\nDone generating .disambig file %s\n",
                  fjalar_disambig_filename);
      fclose(disambig_fp);
      disambig_fp = 0;
      VG_(exit)(0);
    }
  }
}


// Prints a .disambig file entry for a given variable
// This consists of 2 lines:
//   variable name, disambig type
// e.g.,
// /foo       <-- variable name
// S          <-- disambig type
static TraversalResult
printDisambigAction(VariableEntry* var,
                    const HChar* varName,
                    VariableOrigin varOrigin,
                    UInt numDereferences,
                    UInt layersBeforeBase,
                    Bool overrideIsInit,
                    DisambigOverride disambigOverride,
                    Bool isSequence,
                    Addr pValue,
                    Addr pValueGuest,
                    Addr* pValueArray,
                    Addr* pValueArrayGuest,
                    UInt numElts,
                    FunctionEntry* varFuncInfo,
                    Bool isEnter) {
  /* silence unused variable warnings */
  (void)varOrigin; (void)numDereferences; (void)layersBeforeBase;
  (void)overrideIsInit; (void)disambigOverride; (void)isSequence;
  (void)pValue; (void)pValueArray; (void)numElts; (void)varFuncInfo;
  (void)isEnter; (void)pValueGuest; (void)pValueArrayGuest;


  FJALAR_DPRINTF(" printDisambigAction: %s\n", varName);

  // If this is not a variable that's worthy of being outputted to the
  // .disambig file, then punt:
  if (!shouldOutputVarToDisambig(var)) {
    // We do not want to traverse any further than the surface level
    // for .disambig:
    return STOP_TRAVERSAL;
  }

  // Line 1: Variable name
  fputs(varName, disambig_fp);
  fputs("\n", disambig_fp);

  // Line 2: Disambig type

  /* Default values:
     Base type "char" and "unsigned char": 'I' for integer
     Pointer to "char": 'S' for string
     Pointer to all other types:
       - 'A' for array if var->disambigMultipleElts,
             which means that we've observed array
             behavior during program's execution
         or if !var->pointerHasEverBeenObserved,
            which means that the pointer has never
            been observed so a conservative guess
            of 'A' should be the default
         or if var->isStructUnionMember - don't try
            to be smart about member variables
            within structs/unions - just default to "A"
       - 'P' for pointer if (var->pointerHasEverBeenObserved &&
             !var->disambigMultipleElts)
  */

  if (0 == var->ptrLevels) {
    if ((D_CHAR == var->varType->decType) ||
        (D_UNSIGNED_CHAR == var->varType->decType)) {
      fputs("I", disambig_fp);
    }
  }
  // Special case for C++ 'this' parameter - always make it 'P'
  else if (VG_STREQ(var->name, "this")) {
    fputs("P", disambig_fp);
  }
  // Normal string, not pointer to string
  else if (IS_STRING(var) &&
           (1 == var->ptrLevels)) {
    fputs("S", disambig_fp);
  }
  else if (var->ptrLevels > 0) {
    if (IS_MEMBER_VAR(var)) {
      fputs("A", disambig_fp);
    }
    else {
      if (var->pointerHasEverBeenObserved) {
        if (var->disambigMultipleElts) {
          fputs("A", disambig_fp);
        }
        else {
          fputs("P", disambig_fp);
        }
      }
      // default behavior for variable that was
      // never observed during the execution
      else {
        fputs("A", disambig_fp);
      }
    }
  }

  fputs("\n", disambig_fp);

  // We do not want to traverse any further than the surface level for
  // .disambig:
  return STOP_TRAVERSAL;
}

// Pre: disambig_fp has been initialized and disambig_writing is True
void generateDisambigFile() {
  FuncIterator* funcIt;
  TypeIterator* typeIt;

  FJALAR_DPRINTF("\n=> generateDisambigFile: Start Processing\n");

  // Write entries for global variables:
  fputs(ENTRY_DELIMETER, disambig_fp);
  fputs("\n", disambig_fp);
  fputs(GLOBAL_STRING, disambig_fp);
  fputs("\n", disambig_fp);

  visitVariableGroup(GLOBAL_VAR,
                     0,
                     0,
                     0,
                     0,
                     &printDisambigAction);

  FJALAR_DPRINTF("=> generateDisambigFile: Finished Globals\n\n");

  fputs("\n", disambig_fp);

  // Write entries for function parameters and return values:
  funcIt = newFuncIterator();

  while (hasNextFunc(funcIt)) {
    FunctionEntry* cur_entry = nextFunc(funcIt);

    tl_assert(cur_entry);

    // Only write .disambig entries for program points that are listed
    // in prog-pts-file, if we are using the --prog-pts-file option:
    if (!fjalar_trace_prog_pts_filename ||
        // If fjalar_trace_prog_pts_filename is on (we are reading in
        // a ppt list file), then DO NOT OUTPUT entries for program
        // points that we are not interested in.
        prog_pts_tree_entry_found(cur_entry)) {
      fputs(ENTRY_DELIMETER, disambig_fp);
      fputs("\n", disambig_fp);
      fputs(FUNCTION_PREFIX, disambig_fp);
      fputs(cur_entry->fjalar_name, disambig_fp);
      fputs("\n", disambig_fp);

      // Print out all function parameter return value variable names:
      visitVariableGroup(FUNCTION_FORMAL_PARAM,
                         cur_entry,
                         0,
                         0,
                         0,
                         &printDisambigAction);

      visitVariableGroup(FUNCTION_RETURN_VAR,
                         cur_entry,
                         0,
                         0,
                         0,
                         &printDisambigAction);

      fputs("\n", disambig_fp);
    }
  }
  deleteFuncIterator(funcIt);

  FJALAR_DPRINTF("=> generateDisambigFile: Finished Functions\n\n");

  // Write entries for every struct/class in TypesTable, with the
  // type's name prefixed by 'usertype.':
  typeIt = newTypeIterator();

  while (hasNextType(typeIt)) {
    TypeEntry* cur_entry = nextType(typeIt);

    tl_assert(cur_entry && cur_entry->typeName);

    fputs(ENTRY_DELIMETER, disambig_fp);
    fputs("\n", disambig_fp);
    fputs(USERTYPE_PREFIX, disambig_fp);
    fputs(cur_entry->typeName, disambig_fp);
    fputs("\n", disambig_fp);

    visitClassMembersNoValues(cur_entry,
                              &printDisambigAction);

    fputs("\n", disambig_fp);
  }
  deleteTypeIterator(typeIt);

  FJALAR_DPRINTF("=> generateDisambigFile: Finished Types\n\n");
}

// Returns True if var should be output to .disambig:
// - Any var of type "char" or "unsigned char"
// - Any pointer
static Bool shouldOutputVarToDisambig(VariableEntry* var) {
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
      if ((!IS_STRING(var) && (var->ptrLevels == 0)) ||
          (IS_STRING(var) && (var->ptrLevels == 1))) {
        // 'C' denotes to print out as a one-character string
        if (IS_STRING(var)) { // pointer to "char" or "unsigned char"
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
static void processDisambigFile() {
  // (comment added 2005)  
  // TODO: This is crude and unsafe but works for now
  char line1[200];
  char nextLineIsEntry = 0;
  int lineLen = 0;
  DisambigEntryType type = NONE;
  char* entryName = 0; // either a function or struct name
                       // Only relevant when type == {FUNCTION, USERTYPE}

  VarList** VarListArray = 0; // Array of VarList* of size VarListArraySize
  int VarListArraySize = 0;

  if (!disambig_fp || disambig_writing) {
    printf( "Error in processDisambigFile(). Either there is no disambig_file or it is being written.");
    return;
  }

  while (fgets(line1, 200, disambig_fp)) {
    lineLen = VG_(strlen)(line1);
    // FJALAR_DPRINTF("input-line: %s length: %d\n", line1, lineLen);

    // Blank lines only have a "\n" so skip them
    if (lineLen <= 1)
      continue;

    // Strip '\n' off the end of the line
    // NOTE: Only do this if the end of the line is a newline character.
    // If the very last line of a file is not followed by a newline character,
    // then blindly stripping off the last character will truncate the actual
    // string, which is undesirable.
    if (line1[lineLen - 1] == '\n') {
      line1[lineLen - 1] = '\0';
    }

    if VG_STREQ(line1, ENTRY_DELIMETER) {
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
      //   1) A function name - e.g. "function: ..foo()"
      //   2) "globals"
      //   3) A user-defined type (ie. struct) name - e.g. "usertype.fooStruct"
      if (nextLineIsEntry) {
        char* marker = 0;
        // 1) A function name
        if ((marker = VG_(strstr)(line1, FUNCTION_PREFIX))) {
          FunctionEntry* cur_entry = 0;
          FJALAR_DPRINTF("FUNCTION_PREFIX");
          type = FUNCTION;
          // Strip off the prefix by moving forward that many spots in the buffer:
          entryName = VG_(strdup)("disambig.c: processDisambigFile.0.1", &line1[VG_(strlen)(FUNCTION_PREFIX)]);
          //          printf("Function! %s\n", entryName);

          VarListArraySize = 1;
          VarListArray = (VarList**)VG_(calloc)("disambig.c: processDisambigFile.1",  VarListArraySize, sizeof(*VarListArray));

          // Find the appropriate function by name:
          cur_entry = getFunctionEntryFromFjalarName(entryName);
          if (cur_entry) {
            VarListArray[0] = &(cur_entry->formalParameters);
          }
        }
        // 2) "globals"
        else if (VG_STREQ(line1, GLOBAL_STRING)) {
          type = GLOBAL;
          FJALAR_DPRINTF("GLOBAL");
          VarListArraySize = 1;
          VarListArray = (VarList**)VG_(calloc)("disambig.c: processDisambigFile.2", VarListArraySize, sizeof(*VarListArray));

          VarListArray[0] = &globalVars;
        }
        // 3) A user-defined type
        //    (USERTYPE_PREFIX must be the prefix of the string)
        else if (VG_(strstr)(line1, USERTYPE_PREFIX) == (HChar *)line1) {
          TypeIterator* typeIt;
          int i = 0;
          type = USERTYPE;
          FJALAR_DPRINTF("USERTYPE");
          // Strip off the prefix:
          entryName = VG_(strdup)("disambig.c: processDisambigFile.2.1", line1 + VG_(strlen)(USERTYPE_PREFIX));

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

          typeIt = newTypeIterator();

          while (hasNextType(typeIt)) {
            TypeEntry* cur_type = nextType(typeIt);

            if (cur_type->typeName &&
                VG_STREQ(cur_type->typeName, entryName)) {
              FJALAR_DPRINTF(" FAKE [%s]\n", cur_type->typeName);
              VarListArraySize++;
            }
          }

          deleteTypeIterator(typeIt);

          VarListArray = (VarList**)VG_(calloc)("disambig.c: processDisambigFile.3", VarListArraySize, sizeof(*VarListArray));

          typeIt = newTypeIterator();
          i = 0;

          while (hasNextType(typeIt)) {
            TypeEntry* cur_type = nextType(typeIt);

            tl_assert(IS_AGGREGATE_TYPE(cur_type));

            if (cur_type->typeName &&
                VG_STREQ(cur_type->typeName, entryName)) {
              FJALAR_DPRINTF(" REAL [%s]\n", cur_type->typeName);
              VarListArray[i] = cur_type->aggType->memberVarList;
              i++;
            }
          }

          deleteTypeIterator(typeIt);
        }

        FJALAR_DPRINTF(" ENTRY: %s\n", (entryName ? entryName : "<no name>"));
      }
      // A line that doesn't immediately follow ENTRY_DELIMETER
      // The idea here is to find the correct VariableEntry entry and
      // modify its "disambig" field
      else {
        VariableEntry* target = 0;

        char* varName = VG_(strdup)("disambig.c: processDisambigFile.3.1", line1);
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
        fgets(line1, 200, disambig_fp);
        lineLen = VG_(strlen)(line1);
        // Strip '\n' off the end of the line
        // NOTE: Only do this if the end of the line is a newline character.
        // If the very last line of a file is not followed by a newline character,
        // then blindly stripping off the last character will truncate the actual
        // string, which is undesirable.
        if (line1[lineLen - 1] == '\n') {
          line1[lineLen - 1] = '\0';
        }

        disambigLine = VG_(strdup)("disambig.c: processDisambigFile.4.1", line1);

        firstToken = strtok(disambigLine, " ");
        secondToken = strtok(NULL, " ");

        //        printf(" first_token: %s| second_token: %s|\n",
        //                    firstToken, secondToken);

        // The first token should always be the disambig letter
        tl_assert(VG_(strlen)(firstToken) == 1);
        disambig_letter = *firstToken;

        //        printf(" var_name: %s\n", varName);
        //        printf("  disambig_letter: %c\n", disambig_letter);

        // If the second token is non-empty, then it is the coercion type
        if (secondToken) {
          coercion_type = secondToken;
          //          printf("  coercion_type: %s\n", coercion_type);
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
                  TypeEntry* new_type = getTypeEntry(coercion_type);
                  if (new_type) {
                    target->varType = new_type;
                    printf("  .disambig: Coerced variable %s into type '%s'\n",
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
