/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* decls-output.c:

   Functions for creating .decls and .dtrace files and outputting
   name and type information into a Daikon-compatible .decls file

*/

#include "decls-output.h"
#include "kvasir_main.h"
#include "dyncomp_runtime.h"

#include "pub_tool_libcbase.h" // For VG_STREQ

#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/errno.h>
#include <limits.h>

const char* ENTER_PPT = ":::ENTER";
const char* EXIT_PPT = ":::EXIT0";
const char* SIMPLE_EXIT_PPT = ":::EXIT";
const char* OBJECT_PPT = ":::OBJECT";

extern const char* DeclaredTypeString[];

// Hack alert: Necessary for printing out object program points
// properly ...
TypeEntry* cur_type_for_printing_object_ppt = 0;

// Another hack alert ... this is a string that represents the name of
// the top-level type (that appears in typeNameStrTable) which we are
// currently traversing through.  We need to print this instead of the
// real type because Daikon likes it that way.
char* cur_top_level_type_name_for_printing_all_ppts = 0;

// Maps strings to a junk number 1 - simply here to prevent duplicates
// when printing out variable and program point parent entries: (This
// is initialized at the beginning of every program point and freed at
// the end)
struct genhashtable* typeNameStrTable = 0;


// This array can be indexed using the DaikonRepType enum
static const char* DaikonRepTypeString[] = {
  "no_rep_type", //R_NO_TYPE, // Create padding
  "int", //R_INT,
  "double", //R_DOUBLE,
  "hashcode", //R_HASHCODE,
  "java.lang.String", //R_STRING
  "boolean" //R_BOOL
};

// Changes ' ' to '\_' to eliminate spaces in declared types
void printDeclaredType(char* name, FILE* fp) {
  // Change ' ' to '\_' and change '\' to '\\'.
  while (*name != '\0') {
    if (*name == ' ') {
      fputs("\\_", fp);
    }
    else if (*name == '\\') {
      fputs("\\\\", fp);
    }
    else {
      fputc(*name, fp);
    }
    name++;
  }
}

// Use this function to print out a function name for .decls/.dtrace.
void printDaikonFunctionName(FunctionEntry* f, FILE* fp) {
  if (kvasir_new_decls_format) {
    char* name = f->fjalar_name;

    // Spaces in program point names must be backslashed,
    // so change ' ' to '\_'.

    // Backslashes should be double-backslashed,
    // so change '\' to '\\'.

    while (*name != '\0') {
      if (*name == ' ') {
        fputs("\\_", fp);
      }
      else if (*name == '\\') {
        fputs("\\\\", fp);
      }
      else {
        fputc(*name, fp);
      }
      name++;
    }
  }
  else {
    fputs(f->fjalar_name, fp);
  }
}


// Converts a variable name given by Fjalar into a Daikon external
// name and prints it out to FILE*.  Currently, two changes need to be made:
//   1. Change '[]' into '[..]' for array indexing.  However, we
//      should only change the first instance of '[]' because Daikon
//      only currently supports one level of sequences.
//   2. Change ' ' to '\_' (spaces to backslash-underscore) and '\' to '\\'
//      (backslash to double-backslash)
//   3. Change the leading '/' that Fjalar uses to denote global variables
//      to '::' in order to be compatible with C++ syntax.
//      (e.g., change "/foo" to "::foo")
//   4. Strip off everything before the LAST '/' for a global variable to
//      eliminate all disambiguation information for static variables.
//      (e.g., change "custom-dir/ArrayTest_c@returnIntSum/static_local_array"
//       to "::static_local_array".  In this example, static_local_array is
//       a static variable declared within the returnIntSum() function of
//       the file 'custom-dir/ArrayTest.c'.)
// For new .decls format (designed in April 2006)
void printDaikonExternalVarName(char* fjalarName, FILE* fp) {
  int indexOfLastSlash = -1;
  int len = VG_(strlen)(fjalarName);
  int i;
  char* working_name = 0;
  Bool alreadyPrintedBrackets = False; // Only print out one set of "[..]" max.

  tl_assert(kvasir_new_decls_format);

  for (i = 0; i < len; i++) {
    if (fjalarName[i] == '/') {
      indexOfLastSlash = i;
    }
  }

  if (indexOfLastSlash >= 0) {
    // Ignore everything before the final slash:
    working_name = &fjalarName[indexOfLastSlash];
  }
  // No slashes found, just use the name as is
  else {
    working_name = fjalarName;
  }

  // Special case for printing out leading '/' as '::':
  if (*working_name == '/') {
    fputs("::", fp);
    working_name++;
  }

  while (*working_name != '\0') {
    if ((*working_name == '[') &&
        (*(working_name + 1) == ']') &&
        !alreadyPrintedBrackets) {
      fputs("[..", fp);
      alreadyPrintedBrackets = True;
    }
    else if (*working_name == ' ') {
        fputs("\\_", fp);
    }
    else if (*working_name == '\\') {
      fputs("\\\\", fp);
    }
    // Default ... simply output the current character
    else {
      fputc(*working_name, fp);
    }

    working_name++;
  }
}


static void printDeclsHeader(void);
static void printAllFunctionDecls(char faux_decls);
static void printAllObjectPPTDecls(void);

// This has different behavior depending on if faux_decls is on.  If
// faux_decls is on, then we do all the processing but don't actually
// output anything to the .decls file.
void outputDeclsFile(char faux_decls)
{
  // Punt if you are not printing declarations at all:
  if (!print_declarations) {
    return;
  }

  if (!faux_decls) {
    printDeclsHeader();
  }

  printAllFunctionDecls(faux_decls);

  // For DynComp, print this out at the end of execution
  if (!kvasir_with_dyncomp) {
    printAllObjectPPTDecls();
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
  //  VG_(printf)("DC_outputDeclsAtEnd()\n");
  printAllFunctionDecls(0);

  printAllObjectPPTDecls();

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

  case D_FLOAT:
  case D_DOUBLE:
  case D_LONG_DOUBLE:
    return R_DOUBLE;

  case D_STRUCT_CLASS:
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
                                      Bool overrideIsInit,
                                      DisambigOverride disambigOverride,
                                      Bool isSequence,
                                      // pValue only valid if isSequence is false
                                      void* pValue,
                                      // pValueArray and numElts only valid if
                                      // isSequence is true
                                      void** pValueArray,
                                      UInt numElts,
                                      FunctionEntry* varFuncInfo,
                                      Bool isEnter) {
  DeclaredType dType = var->varType->decType;
  DaikonRepType rType = decTypeToDaikonRepType(dType, var->isString);
  UInt layers;
  char printingFirstAnnotation = 1;
  char alreadyPutDerefOnLine3;

  char printAsSequence = isSequence;

  if (kvasir_new_decls_format) {
    int len = VG_(strlen)(varName);

    Bool special_zeroth_elt_var = False;

    // Boolean flags for variables:
    // TODO: Add more flags later as necessary
    Bool is_param_flag = False;
    Bool non_null_flag = False;

    // The format: (entries in brackets are optional, indentation
    //              doesn't matter)
    //
    //      variable <external-name>
    //        var-kind <variable-kinds>
    //        [enclosing-var <external-name>]
    //        [reference-type pointer|offset]
    //        [array <dim-cnt>]
    //        [function-args <arg-list>]
    //        rep-type <representation-type>
    //        dec-type <declared-type>
    //        [flags <variable-flags>]
    //        [lang-flags <language-specific-flags>]
    //        [parent <parent-ppt-name> [<parent-var-name>]]
    //        [comparability <comparability-value>]

    // ****** External variable name ******
    fputs("  variable ", decls_fp);
    printDaikonExternalVarName(varName, decls_fp);
    fputs("\n", decls_fp);

    // ****** Variable kind ******

    fputs("    var-kind ", decls_fp);

    // For a very special case where the suffix of the variable is
    // ZEROTH_ELT ("[0]"), that represents a pointer deference, so we
    // will represent it as of var-kind "field [0]".  Thus, for
    // variable "foo[0]", the var-kind will be "field [0]".
    if ((varName[len - 3] == '[') &&
        (varName[len - 2] == '0') &&
        (varName[len - 1] == ']')) {
      special_zeroth_elt_var = True;
      fputs("field [0]", decls_fp);
    }
    // If numDereferences > 0, then it's an array variable that's the
    // result of the dereference of either a field or a top-level
    // variable:
    else if (numDereferences > 0) {
      fputs("array", decls_fp);
    }
    else if (IS_MEMBER_VAR(var)) {
      fputs("field ", decls_fp);
      // Print out just this variable's name as the field name
      fputs(var->name, decls_fp);
    }
    else {
      fputs("variable", decls_fp);
    }

    fputs("\n", decls_fp);

    // ****** Enclosing variable (optional) ******

    // There is an enclosing variable if enclosingVarNamesStackSize > 0
    if (enclosingVarNamesStackSize > 0) {

      fputs("    enclosing-var ", decls_fp);
      printDaikonExternalVarName(enclosingVarNamesStack[enclosingVarNamesStackSize - 1],
                                 decls_fp);
      fputs("\n", decls_fp);
    }

    // ****** Reference type (optional) ******

    // If it's a static array, set reference type to 'offset'.
    // Otherwise, just leave it as the default of 'pointer'.
    if ((layersBeforeBase == 0) && IS_STATIC_ARRAY_VAR(var)) {
      fputs("    reference-type offset\n", decls_fp);
    }

    // ****** Array dimensions (optional) ******

    // Note that currently Daikon does not support more than 1 level
    // of sequences so the only possible (non-default) value for this
    // is 'array 1'.
    if (isSequence) {
      fputs("    array 1\n", decls_fp);
    }

    // ****** Rep. type ******
    fputs("    rep-type ", decls_fp);

    // This code is copied and pasted from code in the 'else' branch
    // (old .decls format)
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
        // TODO: Change this permanently from "java.lang.String" to
        // "string" in DaikonRepTypeString[] when we're done with the
        // switch-over to the new .decls format
        fputs("string", decls_fp);
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

    // ****** Declared type ******
    fputs("    dec-type ", decls_fp);

    // This code is copied and pasted from code in the 'else' branch
    // (old .decls format)
    if (OVERRIDE_STRING_AS_INT_ARRAY == disambigOverride) {
      fputs(DaikonRepTypeString[R_INT], decls_fp);
      fputs(DEREFERENCE, decls_fp);
    }
    else if (OVERRIDE_STRING_AS_ONE_INT == disambigOverride) {
      fputs(DaikonRepTypeString[R_INT], decls_fp);
    }
    // named struct/union or enumeration
    else if (((dType == D_ENUMERATION) || (dType == D_STRUCT_CLASS) || (dType == D_UNION)) &&
             var->varType->typeName) {
      printDeclaredType(var->varType->typeName, decls_fp);
    }
    else {
      // Normal type (or unnamed struct/union/enum)
      printDeclaredType(DeclaredTypeString[dType], decls_fp);
      // If we have a string, print it as char* because the dType of
      // string is "char" so we need to append a "*" to it
      if (var->isString) {
        fputs(STAR, decls_fp);
      }
    }

    // For the declared type, print out one level of '*' for every
    // layer above base to denote pointer types
    for (layers = 0; layers < layersBeforeBase; layers++) {
      fputs(STAR, decls_fp);
    }

    // If we print this as a sequence, then we must append '[]'
    if (printAsSequence) {
      fputs(DEREFERENCE, decls_fp);
    }

    fputs("\n", decls_fp);


    // ****** Flags ****** (optional)
    if (varOrigin == FUNCTION_FORMAL_PARAM) {
      is_param_flag = True;
    }

    if (IS_STATIC_ARRAY_VAR(var) && (layersBeforeBase == 1)) {
      non_null_flag = True;
    }


    // Only print out optional flags line if at least one flag is True
    if (is_param_flag || non_null_flag /* || other flags ... */) {
      fputs("    flags ", decls_fp);

      if (is_param_flag) {
        fputs("is_param ", decls_fp);
      }

      if (non_null_flag) {
        fputs("non_null ", decls_fp);
      }
      // TODO: Add output for other supported flags

      fputs("\n", decls_fp);
    }

    // ****** Parent ****** (optional)

    // All non-static struct/class member variables should list the
    // :::OBJECT program points of their struct/class as its parent,
    // but actually, it should be
    // cur_top_level_type_name_for_printing_all_ppts because that name
    // must appear in typeNameStrTable and be printed at the program
    // point level too.

    // However, it should only list as parents variables that have the
    // SAME rep./declared type.

    // E.g., the line "parent _buffers:::OBJECT this->age" in this
    // example is incorrect because this->age is of type 'int' and
    // ::population[..].age is of type 'int[]'.

    //  variable ::population[..]
    //     var-kind array
    //     enclosing-var ::population
    //     reference-type offset
    //     array 1
    //     rep-type hashcode[]
    //     dec-type _buffers[]
    //   variable ::population[..].age
    //     var-kind field age
    //     enclosing-var ::population[..]
    //     array 1
    //     rep-type int[]
    //     dec-type int[]
    //     parent _buffers:::OBJECT this->age  <--- WRONG - CUT IT OUT!

    // (TODO: Add support for static member variables at :::OBJECT
    //  program points.  This is just implementation effort ...)
    // Static member variables return True for IS_GLOBAL_VAR(), so
    // don't count those.

    // Hack alert: For OBJECT program points, we don't want to print a
    // parent entry going back to itself, which currently happens for
    // top-level fields (no nesting) ... e.g.,:

    // ppt A:::OBJECT
    //   ppt-type object
    //   variable this->foo_head
    //     var-kind field foo_head
    //     rep-type int
    //     dec-type int
    //     parent A:::OBJECT this->foo_head   <--- This is WRONG
    //   variable this->B
    //     var-kind field B
    //     rep-type hashcode
    //     dec-type unnamed_0x2586*
    //     flags non_null
    //     parent A:::OBJECT this->B          <--- This is WRONG

    // The hack is that we want to prevent those entries from being
    // printed.  One simple check is to see whether the parent type
    // matches cur_type_for_printing_object_ppt, and if so, ignore it.

    if (IS_MEMBER_VAR(var) && !(IS_GLOBAL_VAR(var)) &&
        // Make sure that the type matches up with the type of
        // this->field ...  A hack is to check whether printAsSequence
        // is True and numDereferences == 0 ... if so, then don't
        // create the entry because chances are, the field is not a
        // sequence (since even array fields are represented as a
        // SINGLE hashcode; the array contents variable derived from
        // them represent a sequence.)
        !(isSequence && (numDereferences == 0)) &&
        // Don't print out 'parent' entry for special foo[0]
        // dereferences either ... uhhh
        !special_zeroth_elt_var) {
      // Grab the name of the class that this variable belongs to ...
      tl_assert(IS_AGGREGATE_TYPE(var->memberVar->structParentType));

      // Hack alert ... to prevent loops in OBJECT program points (see
      // the description above)
      if (var->memberVar->structParentType != cur_type_for_printing_object_ppt) {
        // Another hack alert!  We need to print out only types that
        // appear in typeNameStrTable and nothing else, so we use the
        // cur_top_level_type_name_for_printing_all_ppts to take care
        // of this ...

        // Check to see if we are at a new top-level type:
        if (gencontains(typeNameStrTable, var->memberVar->structParentType->typeName)) {
          cur_top_level_type_name_for_printing_all_ppts = var->memberVar->structParentType->typeName;
        }

        if (cur_type_for_printing_object_ppt &&
            VG_STREQ(cur_top_level_type_name_for_printing_all_ppts, cur_type_for_printing_object_ppt->typeName)) {
          cur_top_level_type_name_for_printing_all_ppts = 0;
        }

        if (cur_top_level_type_name_for_printing_all_ppts) {
          fputs("    parent ", decls_fp);
          fputs(cur_top_level_type_name_for_printing_all_ppts, decls_fp);
          fputs(OBJECT_PPT, decls_fp);

          // Now print the field name at the :::OBJECT program point,
          // which should always be "this->field_name" if the field name
          // is field_name:
          fputs(" this->", decls_fp);
          fputs(var->name, decls_fp);

          // Super hack alert: Append a "[..]" if necessary:
          if (printAsSequence) {
          fputs("[..]", decls_fp);
          }

          fputs("\n", decls_fp);
        }
      }
    }


    // ****** Comparability ****** (optional)

    // If we are outputting a REAL .decls with DynComp, that means
    // that the program has already finished execution so that all
    // of the comparability information would be already updated:
    if (kvasir_with_dyncomp) {
      // Remember that comp_number is a SIGNED INTEGER but the
      // tags are UNSIGNED INTEGERS so be careful of overflows
      // which result in negative numbers, which are useless
      // since Daikon ignores them.
      int comp_number = DC_get_comp_number_for_var((DaikonFunctionEntry*)varFuncInfo,
                                                   isEnter,
                                                 g_variableIndex);
      fputs("    comparability ", decls_fp);
      fprintf(decls_fp, "%d", comp_number);
      fputs("\n", decls_fp);
    }
  }
  else {
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
    else if (((dType == D_ENUMERATION) || (dType == D_STRUCT_CLASS) || (dType == D_UNION)) &&
             var->varType->typeName) {
      fputs(var->varType->typeName, decls_fp);
    }
    else {
      // Normal type (or unnamed struct/union/enum)
      fputs(DeclaredTypeString[dType], decls_fp);
      // If we have a string, print it as char* because the dType of
      // string is "char" so we need to append a "*" to it
      if (var->isString) {
        fputs(STAR, decls_fp);
      }
    }

    // For the declared type, print out one level of '*' for every
    // layer above base to denote pointer types
    for (layers = 0; layers < layersBeforeBase; layers++) {
      fputs(STAR, decls_fp);
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
        (IS_AGGREGATE_TYPE(var->varType))) {
      if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
      else {fputs(",", decls_fp);}

      fputs("isStruct=true", decls_fp);
    }

    // Hashcode variables that can never be null has "hasNull=false".
    // (e.g., statically-allocated arrays)
    if (IS_STATIC_ARRAY_VAR(var) && (layersBeforeBase == 1)) {
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
      int comp_number = DC_get_comp_number_for_var((DaikonFunctionEntry*)varFuncInfo,
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
  }


  // We are done!
  return DISREGARD_PTR_DEREFS;
}

// Print out the Daikon .decls header depending on whether DynComp is
// activated or not
static void printDeclsHeader(void)
{
  if (kvasir_new_decls_format) {
    // These are the global records that go at the top of the .decls file

    // TODO: Make separate flags for C and C++; right now this simply
    // prints C/C++.  This information can be grabbed from the DWARF2
    // debug. info. using the DW_AT_language tags (try "readelf -w" on
    // the target program's binary to see what I mean)
    fputs("input-language C/C++\n", decls_fp);
    if (kvasir_with_dyncomp) {
      fputs("var-comparability implicit\n", decls_fp);
    }
    else {
      fputs("var-comparability none\n", decls_fp);
    }
    fputs("\n", decls_fp);
  }
  else {
    if (kvasir_with_dyncomp) {
      // VarComparability implicit is the DEFAULT so we don't need to
      // write anything here:
      //    fputs("VarComparability\nimplicit\n\n", decls_fp);
    }
    else {
      fputs("VarComparability\nnone\n\n", decls_fp);
    }
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
void printOneFunctionDecl(FunctionEntry* funcPtr,
                          char isEnter,
                          char faux_decls) {
  // This is a GLOBAL so be careful :)
  // Reset it before doing any traversals
  g_variableIndex = 0;

  if (!faux_decls) {
    if (kvasir_new_decls_format) {
      // The format: (entries in brackets are optional, indentation
      //              doesn't matter)

      //    ppt <pptname>
      //      ppt-type <ppt-type>
      //      [parent* <relation-type> <parent-ppt-name>]
      //      [flags <ppt-flags>]

      fputs("ppt ", decls_fp);
      printDaikonFunctionName(funcPtr, decls_fp);

      // Append ":::ENTER" or ":::EXIT"
      if (isEnter) {
        fputs(ENTER_PPT, decls_fp);
      }
      else {
        fputs(SIMPLE_EXIT_PPT, decls_fp);
      }
      fputs("\n  ppt-type ", decls_fp);

      if (isEnter) {
        fputs("enter\n", decls_fp);
      }
      else{
        fputs("exit\n", decls_fp);

        // If it's an exit program point, print out an 'enter_exit'
        // parent point to refer back to the ENTER ppt for this
        // function:
        fputs("  parent enter_exit ", decls_fp);
        printDaikonFunctionName(funcPtr, decls_fp);
        fputs(ENTER_PPT, decls_fp);
        fputs("\n", decls_fp);
      }
      // If it's a member function, then print out its parent, which
      // is the object program point of its enclosing class:
      if (funcPtr->parentClass && funcPtr->parentClass->typeName) {
        fputs("  parent parent ", decls_fp);
        fputs(funcPtr->parentClass->typeName, decls_fp);
        fputs(OBJECT_PPT, decls_fp);
        fputs("\n", decls_fp);
      }

      // If any of the formal parameters are struct/class or
      // struct/class pointer types, then add a 'parent' parent entry to
      // link this program point to the :::OBJECT program point of the
      // struct/class.  If any GLOBAL variables are struct/class or
      // struct/class pointer types, then also do the same thing.

      // DON'T HAVE DUPLICATES, THOUGH!  So use a Hashtable to prevent
      // the printing of duplicates:
      {
        // Maps strings to a junk number 1 - simply here to prevent
        // duplicates:
        typeNameStrTable =
          genallocatehashtable((unsigned int (*)(void *)) &hashString,
                               (int (*)(void *,void *)) &equivalentStrings);

        struct geniterator* typeNameStrIt = 0;

        if (funcPtr->formalParameters.numVars > 0) {
          VarNode* n;
          for (n = funcPtr->formalParameters.first;
               n != 0;
               n = n->next) {
            VariableEntry* v = n->var;
            if (IS_AGGREGATE_TYPE(v->varType)) {
              tl_assert(v->varType->typeName);
              if (!gencontains(typeNameStrTable, v->varType->typeName)) {
                genputtable(typeNameStrTable, v->varType->typeName, 1);
              }
            }
          }
        }
        if (globalVars.numVars > 0) {
          VarNode* n;
          for (n = globalVars.first;
               n != 0;
               n = n->next) {
            VariableEntry* v = n->var;
            if (IS_AGGREGATE_TYPE(v->varType)) {
              tl_assert(v->varType->typeName);
              if (!gencontains(typeNameStrTable, v->varType->typeName)) {
                genputtable(typeNameStrTable, v->varType->typeName, 1);
              }
            }
          }
        }

        typeNameStrIt = gengetiterator(typeNameStrTable);
        // Print everything out, without duplicates!
        while (!typeNameStrIt->finished) {
          char* typeName = (char*)gennext(typeNameStrIt);

          // Don't duplicate ...
          if (!funcPtr->parentClass ||
              (!VG_STREQ(funcPtr->parentClass->typeName, typeName))) {
            fputs("  parent parent ", decls_fp);
            fputs(typeName, decls_fp);
            fputs(OBJECT_PPT, decls_fp);
            fputs("\n", decls_fp);
          }
        }

        genfreeiterator(typeNameStrIt);
      }

    }
    else {
      fputs("DECLARE\n", decls_fp);
      printDaikonFunctionName(funcPtr, decls_fp);

      if (isEnter) {
        fputs(ENTER_PPT, decls_fp);
        fputs("\n", decls_fp);
      }
      else {
        fputs(EXIT_PPT, decls_fp);
        fputs("\n", decls_fp);
      }
    }

    // For outputting real .decls when running with DynComp,
    // initialize a global hashtable which associates tags with
    // sequentially-assigned comparability numbers
    if (kvasir_with_dyncomp) {
      // This is a GLOBAL so be careful :)
      g_compNumberMap = genallocatehashtable(NULL, // no hash function needed for u_int keys
                                             (int (*)(void *,void *)) &equivalentIDs);

      g_curCompNumber = 1;

      if (dyncomp_detailed_mode) {
        DC_convert_bitmatrix_to_sets(funcPtr, isEnter);
      }
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
      allocate_ppt_structures((DaikonFunctionEntry*)funcPtr, isEnter, g_variableIndex);
    }
    else {
      genfreehashtable(g_compNumberMap);
    }
  }

  if (!faux_decls && kvasir_new_decls_format) {
    genfreehashtable(typeNameStrTable);
    typeNameStrTable = 0;
  }
}


// Print out all function declarations in Daikon .decls format
static void printAllFunctionDecls(char faux_decls)
{
  FuncIterator* funcIt = newFuncIterator();

  while (hasNextFunc(funcIt)) {
    FunctionEntry* cur_entry = nextFunc(funcIt);

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

  deleteFuncIterator(funcIt);
}


// For C++ only: Print out an :::OBJECT program point.
// The object program point should consist of class_name:::OBJECT
// and all information from 'this'

// DynComp: Right now, do NOT try to print out comparability
// information for OBJECT program points.  We may support this in the
// future if necessary.
static void printAllObjectPPTDecls(void) {
  TypeIterator* typeIt = newTypeIterator();

  Bool hacked_dyncomp_switch = False;

  extern void stringStackPush(char** stringStack, int* pStringStackSize, char* str);
  extern char* stringStackPop(char** stringStack, int* pStringStackSize);

  extern char* fullNameStack[];
  extern int fullNameStackSize;


  // HACK ALERT: We need to temporarily pretend that we are not using
  // kvasir_with_dyncomp in order to print out the OBJECT program
  // points normally.  We need to set this back at the end of the
  // function:
  if (kvasir_with_dyncomp) {
    kvasir_with_dyncomp = False;
    hacked_dyncomp_switch = True;
  }

  while (hasNextType(typeIt)) {
    TypeEntry* cur_type = nextType(typeIt);
    tl_assert(cur_type);

    if (IS_AGGREGATE_TYPE(cur_type)) {

      // If we are using the old .decls format (before April 2006):

      // Only print out .decls for :::OBJECT program points if there
      // is at least 1 member function.  Otherwise, don't bother
      // because object program points will never be printed out for
      // this class in the .dtrace file.  Also, only print it out if
      // there is at least 1 member variable, or else there is no
      // point.

      // If we are using the new .decls format (after April 2006) with
      // --new-decls-format flag active:

      // Print :::OBJECT program points for all structs and classes
      // with at least 1 member var.

      if ((kvasir_new_decls_format ||
           (cur_type->aggType->memberFunctionList && (cur_type->aggType->memberFunctionList->numElts > 0))) &&
          (cur_type->aggType->memberVarList && (cur_type->aggType->memberVarList->numVars > 0)) &&
          cur_type->typeName) {
        tl_assert(cur_type->typeName);

        if (kvasir_new_decls_format) {
          // Maps strings to a junk number 1 - simply here to prevent
          // duplicates:
          typeNameStrTable =
            genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                 (int (*)(void *,void *)) &equivalentStrings);

          struct geniterator* typeNameStrIt = 0;

          VarNode *n;

          // Example output:
          //   ppt Stack
          //   ppt-type object
          fputs("ppt ", decls_fp);
          fputs(cur_type->typeName, decls_fp);
          fputs(OBJECT_PPT, decls_fp);
          fputs("\n  ppt-type object\n", decls_fp);

          // Now comes time to print the 'parent user' entries.  We
          // need to print one for every field inside of this struct
          // that's of a struct type, but not to have duplicates.

          // DON'T ADD YOURSELF as an entry in typeNameStrTable
          for (n = cur_type->aggType->memberVarList->first;
               n != 0;
               n = n->next) {
            VariableEntry* v = n->var;
            if (IS_AGGREGATE_TYPE(v->varType) &&
                v->varType != cur_type) {
              tl_assert(v->varType->typeName);
              if (!gencontains(typeNameStrTable, v->varType->typeName)) {
                genputtable(typeNameStrTable, v->varType->typeName, 1);
              }
            }
          }

          typeNameStrIt = gengetiterator(typeNameStrTable);
          // Print everything out, without duplicates!
          while (!typeNameStrIt->finished) {
            char* typeName = (char*)gennext(typeNameStrIt);
            // Gotta use 'parent user' to prevent infinite recursion
            // (or something like that)
            fputs("  parent user ", decls_fp);
            fputs(typeName, decls_fp);
            fputs(OBJECT_PPT, decls_fp);
            fputs("\n", decls_fp);
          }

          genfreeiterator(typeNameStrIt);
        }
        else {
          fputs("DECLARE\n", decls_fp);
          fputs(cur_type->typeName, decls_fp);
          fputs(OBJECT_PPT, decls_fp);
          fputs("\n", decls_fp);
        }

        stringStackPush(fullNameStack, &fullNameStackSize, "this");
        stringStackPush(fullNameStack, &fullNameStackSize, ARROW);

        // Print out regular member vars.
        cur_type_for_printing_object_ppt = cur_type;
        visitClassMembersNoValues(cur_type, &printDeclsEntryAction);
        cur_type_for_printing_object_ppt = 0;

        stringStackPop(fullNameStack, &fullNameStackSize);
        stringStackPop(fullNameStack, &fullNameStackSize);

        fputs("\n", decls_fp);

        if (kvasir_new_decls_format) {
          genfreehashtable(typeNameStrTable);
          typeNameStrTable = 0;
        }

        // TODO: What do we do about static member vars?
        // Right now we just print them out like globals

        // (TODO: Add support for static member variables at :::OBJECT
        //  program points.  This is just implementation effort ...)
      }
    }
  }

  deleteTypeIterator(typeIt);

  cur_type_for_printing_object_ppt = 0;

  // HACK ALERT! Remember to restore original state
  if (hacked_dyncomp_switch) {
    kvasir_with_dyncomp = True;
  }
}
