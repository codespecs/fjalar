/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* decls-output.c:

   Functions for creating .decls and .dtrace files and outputting
   name and type information into a Daikon-compatible .decls file

*/

//#include "mc_include.h"
#include "decls-output.h"
#include "kvasir_main.h"
#include "dyncomp_runtime.h"

#include "../fjalar_traversal.h"

#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/errno.h>
#include <limits.h>

const char* ENTER_PPT = ":::ENTER";
const char* EXIT_PPT = ":::EXIT0";

extern const char* DeclaredTypeString[];

// This array can be indexed using the DaikonRepType enum
static const char* DaikonRepTypeString[] = {
  "no_rep_type", //R_NO_TYPE, // Create padding
  "int", //R_INT,
  "double", //R_DOUBLE,
  "hashcode", //R_HASHCODE,
  "java.lang.String", //R_STRING
  "boolean" //R_BOOL
};


static void printDeclsHeader();
static void printAllFunctionDecls(char faux_decls);
void printAllObjectAndClassDecls();

// This has different behavior depending on if faux_decls is on.  If
// faux_decls is on, then we do all the processing but don't actually
// output anything to the .decls file.
void outputDeclsFile(char faux_decls)
{
  if (!faux_decls) {
    printDeclsHeader();
  }

  printAllFunctionDecls(faux_decls);

  // For DynComp, print this out at the end of execution
  if (!kvasir_with_dyncomp) {
    printAllObjectAndClassDecls();
  }

  // Clean-up:
  // Only close decls_fp if we are generating it separate of .dtrace

  if (!faux_decls) {
    if (actually_output_separate_decls_dtrace) {
      fclose(decls_fp);
      decls_fp = 0;
    }
  }
}

// Print .decls at the end of program execution and then close it
// (Only used when DynComp is on)
void DC_outputDeclsAtEnd() {
  VG_(printf)("DC_outputDeclsAtEnd()\n");
  printAllFunctionDecls(0);
  printAllObjectAndClassDecls();

  fclose(decls_fp);
  decls_fp = 0;
}


// Converts a Fjalar DeclaredType into a Daikon rep. type:
DaikonRepType decTypeToDaikonRepType(DeclaredType decType,
                                     char isString) {
  if (isString) {
    return R_STRING;
  }

  switch (decType) {
  case D_UNSIGNED_CHAR:
  case D_CHAR:
  case D_UNSIGNED_SHORT:
  case D_SHORT:
  case D_UNSIGNED_INT:
  case D_INT:
  case D_UNSIGNED_LONG_LONG_INT:
  case D_LONG_LONG_INT:
  case D_ENUMERATION:
    return R_INT;

  case D_BOOL:            // C++ only
    return R_BOOLEAN;

  case D_UNSIGNED_FLOAT: // currently unused
  case D_FLOAT:
  case D_UNSIGNED_DOUBLE: // currently unused
  case D_DOUBLE:
  case D_UNSIGNED_LONG_DOUBLE: // currently unused
  case D_LONG_DOUBLE:
    return R_DOUBLE;

  case D_STRUCT:
  case D_UNION:
  case D_FUNCTION:
  case D_VOID:
    return R_HASHCODE;

  case D_CHAR_AS_STRING: // when .disambig 'C' option is used with chars
    return R_STRING;

  default:
    tl_assert(0);
    return R_NO_TYPE;
  }
}

// Do absolutely nothing but keep on letting Fjalar traverse over all
// of the variables.  This is used by DynComp to see how many
// variables (both actual and derived) are present at a program point
// (g_variableIndex increments during each variable visit).
TraversalResult nullAction(VariableEntry* var,
                           char* varName,
                           VariableOrigin varOrigin,
                           UInt numDereferences,
                           UInt layersBeforeBase,
                           char overrideIsInit,
                           DisambigOverride disambigOverride,
                           char isSequence,
                           // pValue only valid if isSequence is false
                           void* pValue,
                           // pValueArray and numElts only valid if
                           // isSequence is true
                           void** pValueArray,
                           UInt numElts,
                           FunctionEntry* varFuncInfo,
                           char isEnter) {
  return DISREGARD_PTR_DEREFS;
}


// This is where all of the action happens!
// Print a .decls entry for a particular variable:
// Pre: varName is allocated and freed by caller
// This consists of 4 lines:
// var. name, declared type, rep. type, comparability number
// e.g.,
// /foo                 <-- variable name
// char*                <-- declared type
// java.lang.String     <-- rep. type
// 22                   <-- comparability number
TraversalResult printDeclsEntryAction(VariableEntry* var,
                                      char* varName,
                                      VariableOrigin varOrigin,
                                      UInt numDereferences,
                                      UInt layersBeforeBase,
                                      char overrideIsInit,
                                      DisambigOverride disambigOverride,
                                      char isSequence,
                                      // pValue only valid if isSequence is false
                                      void* pValue,
                                      // pValueArray and numElts only valid if
                                      // isSequence is true
                                      void** pValueArray,
                                      UInt numElts,
                                      FunctionEntry* varFuncInfo,
                                      char isEnter) {
  DeclaredType dType = var->varType->decType;
  DaikonRepType rType = decTypeToDaikonRepType(dType, var->isString);
  UInt layers;
  char printingFirstAnnotation = 1;
  char alreadyPutDerefOnLine3;

  char printAsSequence = isSequence;

  // Line 1: Variable name
  fprintf(decls_fp, "%s\n", varName);

  // Line 2: Declared type
  if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
    fputs(DaikonRepTypeString[R_INT], decls_fp);
    fputs(DEREFERENCE, decls_fp);
  }
  else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
    fputs(DaikonRepTypeString[R_INT], decls_fp);
  }
  // named struct/union or enumeration
  else if (((dType == D_ENUMERATION) || (dType == D_STRUCT) || (dType == D_UNION)) &&
           var->varType->collectionName) {
    fputs(var->varType->collectionName, decls_fp);

    // For the repair tool, concatenate all of the field names
    // after the 'unnamed' struct name (after an underscore)

    // TODO: Re-implement all the stuff for the repair tool because
    // they involve both Fjalar and Kvasir changes:

/*     if (kvasir_repair_format && */
/*         VG_STREQ(var->varType->collectionName, "unnamed")) { */
/*       VarList* memberVars = var->varType->memberListPtr; */
/*       VarNode* i = 0; */
/*       DaikonVariable* curVar = 0; */

/*       fputs("_", decls_fp); */

/*       for (i = memberVars->first; i != 0; i = i->next) { */
/*         curVar = &(i->var); */
/*         if (curVar->name) { */
/*           fputs(curVar->name, decls_fp); */
/*         } */
/*       } */
/*     } */
  }
  else {
    // Normal type (or unnamed struct/union/enum)
    fputs(DeclaredTypeString[dType], decls_fp);
    // If we have a string, print it as char*
    // because the dType of string is "char"
    // so we need to append a "*" to it
    if (var->isString) {
      fputs(STAR, decls_fp);
    }
  }

  // For the declared type, print out one level of '*' for every
  // layer above base to denote pointer types
  for (layers = 0; layers < layersBeforeBase; layers++) {
    fputs(STAR, decls_fp);
    // TODO: Determine later whether this special case is worth it:
    // Special case for static array types: use a '[]' to
    // replace the LAST '*'
    //        if ((var->isStaticArray) &&
    //            (layers == (layersBeforeBase - 1))) {
    //          fputs(DEREFERENCE, decls_fp);
    //        }
    //        else {
    //          fputs(STAR, decls_fp);
    //        }
  }

  // If we print this as a sequence, then we must append '[]'
  if (printAsSequence) {
    fputs(DEREFERENCE, decls_fp);
  }

  // Add annotations as comments in .decls file
  // (The first one is preceded by ' # ' and all subsequent ones are
  // preceded by ',')

  // Original vars in function parameter lists have "isParam=true"

  if (varOrigin == FUNCTION_FORMAL_PARAM) {
    if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
    else {fputs(",", decls_fp);}

    fputs("isParam=true", decls_fp);
  }

  // Struct variables are annotated with "isStruct=true"
  // in order to notify Daikon that the hashcode values printed
  // out for that variable have no semantic meaning
  if (fjalar_output_struct_vars &&
      (layersBeforeBase == 0) &&
      (var->varType->isStructUnionType)) {
    if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
    else {fputs(",", decls_fp);}

    fputs("isStruct=true", decls_fp);
  }

  // Hashcode variables that can never be null has "hasNull=false".
  // (e.g., statically-allocated arrays)
  if (var->isStaticArray && (layersBeforeBase == 1)) {
    if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
    else {fputs(",", decls_fp);}

    fputs("hasNull=false", decls_fp);
  }

  fputs("\n", decls_fp);


  // Line 3: Rep. type
  alreadyPutDerefOnLine3 = 0;

  // Print out rep. type as hashcode when you are not done dereferencing
  // pointer layers:
  if (layersBeforeBase > 0) {
    fputs(DaikonRepTypeString[R_HASHCODE], decls_fp);
  }
  else {
    // Special handling for strings and 'C' chars in .disambig
    if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
      fputs(DaikonRepTypeString[R_INT], decls_fp);
      fputs(DEREFERENCE, decls_fp);
      alreadyPutDerefOnLine3 = 1;
    }
    else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
      fputs(DaikonRepTypeString[R_INT], decls_fp);
    }
    else if ((var->isString) ||
             (OVERRIDE_CHAR_AS_STRING == disambigOverride)) {
      fputs(DaikonRepTypeString[R_STRING], decls_fp);
    }
    else {
      tl_assert(rType != 0);
      fputs(DaikonRepTypeString[rType], decls_fp);
    }
  }

  // Append "[]" onto the end of the rep. type if necessary
  if (!alreadyPutDerefOnLine3 &&
      printAsSequence) {
    fputs(DEREFERENCE, decls_fp);
  }

  fputs("\n", decls_fp);


  // Line 4: Comparability number

  // If we are outputting a REAL .decls with DynComp, that means
  // that the program has already finished execution so that all
  // of the comparability information would be already updated:
  if (kvasir_with_dyncomp) {
    // Remember that comp_number is a SIGNED INTEGER but the
    // tags are UNSIGNED INTEGERS so be careful of overflows
    // which result in negative numbers, which are useless
    // since Daikon ignores them.
    int comp_number = DC_get_comp_number_for_var(varFuncInfo,
                                                 isEnter,
                                                 g_variableIndex);
    fprintf(decls_fp, "%d", comp_number);
    fputs("\n", decls_fp);
  }
  else {
    // Otherwise, print out unknown comparability type "22"
    fputs("22", decls_fp);
    fputs("\n", decls_fp);
  }

  // We are done!
  return DISREGARD_PTR_DEREFS;
}

// Print out the Daikon .decls header depending on whether DynComp is
// activated or not
static void printDeclsHeader()
{
  if (kvasir_with_dyncomp) {
    // VarComparability implicit is the DEFAULT so we don't need to
    // write anything here:
    //    fputs("VarComparability\nimplicit\n\n", decls_fp);
  }
  else {
    fputs("VarComparability\nnone\n\n", decls_fp);
  }
}

// Print out one individual function declaration
// Example:
/*
DECLARE
printHelloWorld():::ENTER
routebaga
double # isParam=true
double
1
turnip
char # isParam=true
int
2
*/
// char isEnter = 1 for function ENTER, 0 for EXIT
// faux_decls = True if we are making the FIRST pass with DynComp to count up
// how many Daikon variables exist at a program point so that we can initialize
// the proper data structures (no .decls output is made during this dry run)
// and faux_decls = False if we are really outputting .decls, which is in the
// beginning of execution without DynComp and at the END of execution with DynComp
static void printOneFunctionDecl(FunctionEntry* funcPtr,
                                 char isEnter,
                                 char faux_decls) {
  // This is a GLOBAL so be careful :)
  // Reset it before doing any traversals
  g_variableIndex = 0;

  if (!faux_decls) {
    fputs("DECLARE\n", decls_fp);
    fputs(funcPtr->fjalar_name, decls_fp);

    if (isEnter) {
      fputs(ENTER_PPT, decls_fp);
      fputs("\n", decls_fp);
    }
    else {
      fputs(EXIT_PPT, decls_fp);
      fputs("\n", decls_fp);
    }

    // For outputting real .decls when running with DynComp,
    // initialize a global hashtable which associates tags with
    // sequentially-assigned comparability numbers
    if (kvasir_with_dyncomp) {
      // This is a GLOBAL so be careful :)
      g_compNumberMap = genallocatehashtable(NULL, // no hash function needed for u_int keys
                                             (int (*)(void *,void *)) &equivalentIDs);

      g_curCompNumber = 1;
    }
  }

  // Print out globals (visitVariableGroup() ignores the globals if
  // --ignore-globals is used):
  visitVariableGroup(GLOBAL_VAR,
                     funcPtr, // need this for DynComp to work properly
                     isEnter,
                     0,
                     (faux_decls ?
                      &nullAction : &printDeclsEntryAction));

  // Now print out one entry for every formal parameter (actual and derived)
  visitVariableGroup(FUNCTION_FORMAL_PARAM,
                     funcPtr,
                     isEnter,
                     0,
                     (faux_decls ?
                      &nullAction : &printDeclsEntryAction));

  // If EXIT, print out return value
  if (!isEnter) {
  visitVariableGroup(FUNCTION_RETURN_VAR,
                     funcPtr,
                     0,
                     0,
                     (faux_decls ?
                      &nullAction : &printDeclsEntryAction));
  }

  if (!faux_decls) {
    fputs("\n", decls_fp);
  }

  if (kvasir_with_dyncomp) {
    if (faux_decls) {
      // Allocate program point data structures if we are using DynComp:
      // (This should only be run once for every ppt)
      // This must be run at the end because its results depend on
      // g_variableIndex being properly incremented
      allocate_ppt_structures(funcPtr, isEnter, g_variableIndex);
    }
    else {
      genfreehashtable(g_compNumberMap);
    }
  }

}


// Print out all function declarations in Daikon .decls format
static void printAllFunctionDecls(char faux_decls)
{
  struct geniterator* it = gengetiterator(FunctionTable);

  while(!it->finished) {
    FunctionEntry* cur_entry =
      (FunctionEntry*)gengettable(FunctionTable, gennext(it));

    tl_assert(cur_entry);

    // If fjalar_trace_prog_pts_filename is OFF, then ALWAYS
    // print out all program point .decls
    if (!fjalar_trace_prog_pts_filename ||
        // If fjalar_trace_prog_pts_filename is on (we are reading in
        // a ppt list file), then DO NOT OUTPUT .decls entries for
        // program points that we are not interested in tracing.  This
        // decreases the clutter of the .decls file and speeds up
        // processing time
        prog_pts_tree_entry_found(cur_entry)) {
      printOneFunctionDecl(cur_entry, 1, faux_decls);
      printOneFunctionDecl(cur_entry, 0, faux_decls);
    }
  }

  genfreeiterator(it);
}


// TODO: REWRITE THIS!!!

// For C++ only: Print out an :::OBJECT program point.
// The object program point should consist of class_name:::OBJECT
// and all information from 'this'

// For C++ only: Print out a :::CLASS program point.
// The class program point should consist of class_name:::CLASS
// and all information about only STATIC variables belonging to this class

// DynComp: Right now, do NOT try to print out comparability
// information for OBJECT and CLASS program points.  We may support
// this in the future if necessary.

void printAllObjectAndClassDecls() {
#ifdef BLAHBLAH
  struct geniterator* it = gengetiterator(DaikonTypesTable);

  // Hashtable which contains the names of classes which have already printed
  // OBJECT and CLASS program points.  This is so that we can allow duplicate
  // entries in DaikonTypesTable but only print out ONE OBJECT/CLASS .decls program
  // point for each entry with a particular name
  // Key: Class name, Value: Doesn't matter - we only check if the table
  // "contains the entry"
  struct genhashtable* ClassNamesAlreadyPrinted =
    genallocatehashtable((unsigned int (*)(void *)) & hashString,
                         (int (*)(void *,void *)) &equivalentStrings);

  Bool hacked_dyncomp_switch = False;

  // HACK ALERT: We need to temporarily pretend that we are not using
  // kvasir_with_dyncomp in order to print out the OBJECT and CLASS
  // program points normally.  We need to set this back at the end of
  // the function:
  if (kvasir_with_dyncomp) {
    kvasir_with_dyncomp = False;
    hacked_dyncomp_switch = True;
  }

  while(!it->finished) {
    DaikonType* cur_type = (DaikonType*)
         gengettable(DaikonTypesTable, gennext(it));

    if (!cur_type)
         continue;

    // Only print out .decls for :::OBJECT and :::CLASS program points
    // if num_member_funcs > 0 - otherwise we have no member functions
    // so these program points will never be reached :)
    // Also, only print them out if their name is NOT contained in
    // ClassNamesAlreadyPrinted - otherwise there is a duplicate so don't
    // print it out!
    if ((cur_type->num_member_funcs > 0) &&
        (cur_type->collectionName) && // Do NOT try to print out unnamed anonymous classes
                                      // because we will have a naming ambiguity
        !gencontains(ClassNamesAlreadyPrinted, cur_type->collectionName)) {
         // Make up a fake DaikonFunctionInfo entry and populate the parentClass field
         DaikonFunctionInfo fakeFuncInfo;

         // Make up a fake DaikonVariable named 'this' and set its type to cur_type
         DaikonVariable fakeThisVar;

         memset(&fakeFuncInfo, 0, sizeof(fakeFuncInfo));
         fakeFuncInfo.parentClass = cur_type;

         memset(&fakeThisVar, 0, sizeof(fakeThisVar));
         fakeThisVar.name = "this";
         fakeThisVar.varType = cur_type;
         fakeThisVar.repPtrLevels = 1;
         fakeThisVar.declaredPtrLevels = 1;
         // Remember the .disambig for "this" so that it prints
         // out as ONE element and not an array
         fakeThisVar.disambig = 'P';

         fputs("DECLARE\n", decls_fp);
         fputs(cur_type->collectionName, decls_fp);
         fputs(":::OBJECT\n", decls_fp);

         stringStackPush(fullNameStack, &fullNameStackSize, "this");

         visitVariable(&fakeThisVar,
                       0,
                       0,
                       FUNCTION_ENTER_FORMAL_PARAM,
                       DECLS_FILE,
                       0,
                       0,
                       0,
                       0);

         stringStackPop(fullNameStack, &fullNameStackSize);


         fputs("\n", decls_fp);

         fputs("DECLARE\n", decls_fp);
         fputs(cur_type->collectionName, decls_fp);
         fputs(":::CLASS\n", decls_fp);

         printVariablesInVarList(&fakeFuncInfo, 1, // set 'isEnter' to 1 here (arbitrary choice)
                                 GLOBAL_VAR,
                                 0,
                                 DECLS_FILE,
                                 0,
                                 0,
                                 1,
                                 0);

         fputs("\n", decls_fp);

         genputtable(ClassNamesAlreadyPrinted, cur_type->collectionName, 0);
    }
  }

  genfreeiterator(it);
  genfreehashtable(ClassNamesAlreadyPrinted);

  // HACK ALERT! Remember to restore original state
  if (hacked_dyncomp_switch) {
    kvasir_with_dyncomp = True;
  }

#endif // #ifdef BLAHBLAH
}
