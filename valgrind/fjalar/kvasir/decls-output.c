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
#include "pub_tool_libcprint.h"

#include "../my_libc.h"

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

// Similar to the above table. Used for functions. C/C++ programs can
// Occasionally have duplicate symbols in their symbol tables. This
// However causes problems if a ppt or variable name is printed twice
struct genhashtable* funcNameTable = 0;

// We need one more table in addition to the above. The above is for
// detecting if a collision has occured. However, since the dtrace
// pass happens independently of the decls pass, and we need to
// ensure that the dtrace pass uses similar names, we will keep
// a table containing all function startPCs(The memory location of
// the function) to identify acollided function
struct genhashtable* funcIdToNameTable = 0;

// Contains all variable declarations printed for a given program point
// using this while transitioning. It is a requirement for enclosing-
// vars to have an actual variable entry. Thus a variable will check
// if a variable is in this table before adding a enclosing-var
struct genhashtable* varsDeclaredTable = 0;

// All Object ID's in the decls 2.0 format require a unique parent ID.
// This variable contains the smallest integer that has yet to be used
// for a parent ID.
static int curr_par_id = 1;

// Contains a mapping between an object name and it's unique ID
struct genhashtable* objectIdTable = 0;

// Contains a mapping between a string and it's typename
// RUDD TODO: When I get a chance I need to allow Fjalar to pass
// more non-string information, so I don't have to resort to so many
// hashes of strings.
struct genhashtable* nameToType = 0;

// Table to prevent infinite recursion when recursing through nested structs.
struct genhashtable* nestedTraversalTable = 0;

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
static void printDeclaredType(const char* name, FILE* fp) {
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
  if (!kvasir_old_decls_format) {
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
// name. Caller is responsible for destroying the string
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
void printDaikonExternalVarName(VariableEntry* var, char* fjalarName, FILE* fp) {
  int indexOfLastSlash = -1;
  int len = VG_(strlen)(fjalarName);
  int i;
  char* working_name;
  (void) var;
  Bool alreadyPrintedBrackets = False; // Only print out one set of "[..]" max.

  tl_assert(!kvasir_old_decls_format);

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
    }else if(*working_name == ' ') {
      fputs("\\_", fp);
    }else if(*working_name == '\\') {
      fputs("\\\\", fp);
    }else {
      fputc(*working_name, fp);
    }
    working_name++;
  }
}


static void printDeclsHeader(void);
static void printAllFunctionDecls(char faux_decls);
static void printAllObjectPPTDecls(void);

// Initializes all the data structures needed to perform decls
void initDecls()
{
  //Initialize needed hash tables.
  if(!nameToType) {
     nameToType =
        genallocatehashtable((unsigned int (*)(void *)) &hashString,
                             (int (*)(void *,void *)) &equivalentStrings);
  }
  if(!objectIdTable) {
      objectIdTable  =
        genallocatehashtable((unsigned int (*)(void *)) &hashString,
                             (int (*)(void *,void *)) &equivalentStrings);
  }

  if(!funcIdToNameTable)
    {
      funcIdToNameTable =
        genallocatehashtable(0,
                             (int (*)(void *,void *)) &equivalentIDs);
    }

}

void cleanupDecls()
{
  // Clean-up tables.
  if(nameToType) {
    genfreehashtable(nameToType);
    nameToType = 0;
  }
  if(objectIdTable) {
    genfreehashtable(objectIdTable);
    objectIdTable  = 0;
  }


}

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

  initDecls();
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
  cleanupDecls();
}

// Print .decls at the end of program execution and then close it
// (Only used when DynComp is on)
void DC_outputDeclsAtEnd() {
  //  VG_(printf)("DC_outputDeclsAtEnd()\n");
  initDecls();
  printAllFunctionDecls(0);

  printAllObjectPPTDecls();

  fclose(decls_fp);
  decls_fp = 0;
  cleanupDecls();
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
static TraversalResult
nullAction(VariableEntry* var,
	   char* varName,
	   VariableOrigin varOrigin,
	   UInt numDereferences,
	   UInt layersBeforeBase,
	   Bool overrideIsInit,
	   DisambigOverride disambigOverride,
	   Bool isSequence,
	   // pValue only valid if isSequence is false
	   Addr pValue,
	   Addr pValueGuest,
	   // pValueArray and numElts only valid if
	   // isSequence is true
	   Addr* pValueArray,
	   Addr* pValueArrayGuest,
	   UInt numElts,
	   FunctionEntry* varFuncInfo,
	   Bool isEnter) {
  /* silence unused variable warnings */
  (void)var; (void)varName; (void)varOrigin; (void)numDereferences;
  (void)layersBeforeBase; (void)overrideIsInit; (void)disambigOverride;
  (void)isSequence; (void)pValue; (void)pValueArray; (void)numElts;
  (void)varFuncInfo; (void)isEnter; (void)pValueGuest; (void)pValueArrayGuest;

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
static TraversalResult
printDeclsEntryAction(VariableEntry* var,
		      char* varName,
		      VariableOrigin varOrigin,
		      UInt numDereferences,
		      UInt layersBeforeBase,
		      Bool overrideIsInit,
		      DisambigOverride disambigOverride,
		      Bool isSequence,
		      // pValue only valid if isSequence is false
		      Addr pValue,
		      Addr pValueGuest,
		      // pValueArray and numElts only valid if
		      // isSequence is true
		      Addr* pValueArray,
		      Addr* pValueArrayGuest,
		      UInt numElts,
		      FunctionEntry* varFuncInfo,
		      Bool isEnter) {
  DeclaredType dType = var->varType->decType;
  DaikonRepType rType = decTypeToDaikonRepType(dType, var->isString);
  UInt layers;
  int i;
  char printingFirstAnnotation = 1;
  char alreadyPutDerefOnLine3;
  char printAsSequence = isSequence;
  Bool shortSuper = 0;

  /* silence unused variable warnings */
  (void)overrideIsInit; (void)pValue; (void)pValueArray; (void)numElts;
  (void)pValueGuest; (void)pValueArrayGuest;

  DPRINTF("*********************************\n%s\n*********************************\n", varName);
  if(fullNameStackSize > 0)
    for(i=0; i< fullNameStackSize; i++)
      {
        DPRINTF("fullNameStack[%d] = %s\n", i,  fullNameStackPtr[i]);
      }

  if(enclosingVarNamesStackSize > 0)
    for(i=0; i< enclosingVarNamesStackSize; i++)
      {
        DPRINTF("enclosingVarNamesStack[%d] = %s\n", i, enclosingVarNamesStack[i]);
      }
  DPRINTF("Address %8x \n", pValue);

  if (!kvasir_old_decls_format) {
    int len = VG_(strlen)(varName);
    char *shortName;
    Bool special_zeroth_elt_var = False;

    // Boolean flags for variables:
    // TODO: Add more flags later as necessary
    Bool is_param_flag = False;
    Bool non_null_flag = False;


    tl_assert(nameToType);

    if(!gencontains(nameToType, varName))
    {
      genputtable(nameToType, varName, var->varType->typeName);
    }


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



    // Readability improvements. Fjalar represents superclass variables
    // similar to how fields are represented. For example in the case:
    // Class B { int c; }
    // Class A : Public B ...
    // Fjalar will pass us the name A.B.c. While, this does provide us
    // the advantage of overcoming diamond-inheritence probelms, it
    // isn't the most intuitive way to represent the variable in the
    // output. This attempts to collapse any superclass variables at
    // the END of the string. isSuperMember refers to how many
    // levles of superclasses up this variable is.

    // RUDD Beautification. Not for release
    //if(var->isSuperMember && !kvasir_unambiguous_fields)
    if(0) {
      shortSuper = 1; //Flag to denote this is a shortened name
      shortName = removeSuperElements(fullNameStackPtr, var);
      printDaikonExternalVarName(var, shortName, decls_fp);
      VG_(free)(shortName);
      printDaikonExternalVarName(var, fullNameStackPtr[fullNameStackSize-1], decls_fp);
    }
    else {
      shortName = varName;
      printDaikonExternalVarName(var, shortName, decls_fp);
    }


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

       int enclosing_len;


       // We need to ensure we get enclosing variables right when using short supers
       // This means we need to remove var->isSuperMember * 2 elements from the full
       // name stack(fully documented in fjalar_traversal.c.) The fullNameStack contains
       // one array element for each element of the name. for example outer.middle.inner,
       // would be represented as a 5 elements array {"outer",".", "middle", "." "inner"}
       if(0) {
         /*  if(shortSuper) {
                  char* enclosingVar =  stringArrayFlatten(fullNameStackPtr, 0, fullNameStackSize-2*var->isSuperMember-2);
          if(enclosingVar && gencontains(varsDeclaredTable, enclosingVar)) {
            fputs("    enclosing-var ", decls_fp);
            printDaikonExternalVarName(var, enclosingVar, decls_fp);
            //fputs(enclosingVar, decls_fp);
            fputs("\n", decls_fp);
          }
         */
        }
        else if (gencontains(varsDeclaredTable, enclosingVarNamesStack[enclosingVarNamesStackSize - 1])) {
          fputs("    enclosing-var ", decls_fp);
          enclosing_len = VG_(strlen)(enclosingVarNamesStack[enclosingVarNamesStackSize - 1]);

          // Ugly check. As a way to improve readability, Fjalar simplifies varnames in the form
          // var[0].field to var->field. Unfortunately it still passes var[0] as the enclosing
          // variable which is most likely not even present in the file somewhere. It also may cause
          // problems with how the enclosing variables are handled. Thus we can detect this condition
          // if we both have an enclosing variable and it ends in [0]. If this is the case, simply
          // print var as the enclosing variable.
          if( (enclosing_len > 3) && !special_zeroth_elt_var &&
              (enclosingVarNamesStack[enclosingVarNamesStackSize - 1][enclosing_len - 3] == '[') &&
              (enclosingVarNamesStack[enclosingVarNamesStackSize - 1][enclosing_len - 2] == '0') &&
              (enclosingVarNamesStack[enclosingVarNamesStackSize - 1][enclosing_len - 1] == ']'))
            {
              printDaikonExternalVarName(var, enclosingVarNamesStack[enclosingVarNamesStackSize - 2],
                                         decls_fp);
            }
          else
            {
              printDaikonExternalVarName(var, enclosingVarNamesStack[enclosingVarNamesStackSize - 1],
                                         decls_fp);
            }
          fputs("\n", decls_fp);
        }
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
      // later due to the nature of the declso-2.0
      if (kvasir_parent_records && IS_MEMBER_VAR(var)
          && !(IS_GLOBAL_VAR(var))
          // RUDD - Not dealing with return variables for now. Though we can
          && (varOrigin != FUNCTION_RETURN_VAR)
          && VG_(strcmp)("return", enclosingVarNamesStack[0])) {

        // Make sure that the type matches up with the type of
        // this->field ...  A hack is to check whether printAsSequence
        // is True and numDereferences == 0 ... if so, then don't
        // create the entry because chances are, the field is not a
        // sequence (since even array fields are represented as a
        // SINGLE hashcode; the array contents variable derived from
        // them represent a sequence.)
        //!(isSequence && (numDereferences == 0)) &&
        // Don't print out 'parent' entry for special foo[0]
        // dereferences either ... uhhh
        //!special_zeroth_elt_var


        // RUDD - I'm not so sure the above is necessary. Doing this
        // has caused some variables to not have relations to their
        // parents simply because they were zeroth elements
        // however special care must be taken to ensure the fields match
        // up against their parent's fields. So make sure you print the
        // [0]. Sequences do cause a problem in general, however we can
        // still handle sequences for object methods and the this pointer
        // (It is (I think) unlikely for there to be an array of this[]
        // so we can safely assume the sequence is actually a field of
        // the object



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

          // Link the variable to a corresponding variable in the parent object record
          // This is somewhat tricky due to the nesting. A variable entry only contains
          // information on its most immediate parent. Unfortunately, to have useful
          // invariants, we must link a variable to it's topmost parent. For example
          // If we had
          // struct outer {
          //   struct middle {
          //     int inner;
          //   }
          // }
          // We would want to link inner to outer's middle.inner variable, as opposed
          // To middle's inner variable. To do this we must make use of Fjalar's full
          // name stack

          if (cur_top_level_type_name_for_printing_all_ppts) {
            char* ppt_par_id=0, *field_name=0, *str_arr=0, *parent_name=0;

            // There are 2 cases:
            // 1. 'this->' for object methods as they require some extra work to find out
            //    what to link to(Unfortunately, there is no way to determine whether or
            //    not something is a 'this' parameter for an object for simply a varaible
            //    named this. I haven't run across any problems on test cases thus far, but
            //    I can conceive their being a potnetial problem)
            // 2. all other member variables that are not sequences(See above
            //    comment for problem with sequences)
           if((VG_(strstr)(varName, "this->"))) {

             // I'm not quite sure how varFuncInfo can ever be null, I'll have to
             // look into it. Either way, if we don't have varFuncInfo, attempt to
             // pull type name from the current ppt's name
             // cur_top_level_type_name_for_printing_all_ppts
             parent_name = (varFuncInfo)?
               varFuncInfo->parentClass->typeName:
               cur_top_level_type_name_for_printing_all_ppts;


             // Print name of the Object ppt which includes the object's
             // name and the :::OBJECT tag
             fputs("    parent ", decls_fp);
             fputs(parent_name, decls_fp);
             fputs(OBJECT_PPT, decls_fp);

             // Retrieve (or generate one if one doesn't exist) a parentID
             ppt_par_id = getParentId(parent_name);
             fputs(ppt_par_id, decls_fp);

             // We have to ensure that the above readability improvements do no
             // break parent relations

             // Now print the field name at the :::OBJECT program point,
             // which should always be "this->field_name" if the field name
             // is field_name if we're set up to use the readability improvements
             // RUDD Beautification
             //if(var->isSuperMember && !kvasir_unambiguous_fields) {
             if (0) {
               field_name = fullNameStackPtr[fullNameStackSize-1];
             }
             else {
               str_arr = field_name = stringArrayFlatten(fullNameStackPtr, 2, fullNameStackSize);
             }

             fputs(" this->", decls_fp);
             printDaikonExternalVarName(var,field_name, decls_fp);
             // Be careful about remembering to print the [0] if necessary
             //             if(special_zeroth_elt_var)
             //               fputs("[0]", decls_fp);
             fputs("\n", decls_fp);
           }
           // We have to punt if it's a non 'this' variable that is a sequence
           // RUDD - sequence variables are a bit hairy
           else if(!isSequence && gengettable(nameToType,enclosingVarNamesStack[0])) {
             fputs("    parent ", decls_fp);


             //fputs(gengettable(nameToType,enclosingVarNamesStack[0]), decls_fp);

             fputs(var->memberVar->structParentType->typeName, decls_fp);
             fputs(OBJECT_PPT, decls_fp);
             //ppt_par_id = getParentId(gengettable(nameToType,enclosingVarNamesStack[0]));
             ppt_par_id = getParentId(var->memberVar->structParentType->typeName);

             fputs(ppt_par_id, decls_fp);
             fputs(" this->", decls_fp);
             fputs(fullNameStackPtr[fullNameStackSize-1], decls_fp);
             if(special_zeroth_elt_var)
               fputs("[0]", decls_fp);
             fputs("\n", decls_fp);
           }

          }

        }

      }
      // ****** Comparability ****** (optional)

      // If we are outputting a REAL .decls with DynComp, that means
      // that the program has already finished execution so that all
      // of the comparability information would be already updated:
      if (kvasir_with_dyncomp) {
	VG_(printf)("Getting comp number for varaible %s\n", varName);
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
        printingFirstAnnotation = False;
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
        printingFirstAnnotation = False;
      }

      // Hashcode variables that can never be null has "hasNull=false".
      // (e.g., statically-allocated arrays)
      if (IS_STATIC_ARRAY_VAR(var) && (layersBeforeBase == 1)) {
        if (printingFirstAnnotation) {fputs(" # ", decls_fp);}
        else {fputs(",", decls_fp);}

        fputs("hasNull=false", decls_fp);
        printingFirstAnnotation = False;
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
	VG_(printf)("Getting comp number for varaible %s ", varName);
        DaikonFunctionEntry *entry = (DaikonFunctionEntry *)varFuncInfo;
        // Remember that comp_number is a SIGNED INTEGER but the
        // tags are UNSIGNED INTEGERS so be careful of overflows
        // which result in negative numbers, which are useless
        // since Daikon ignores them.
        int comp_number = DC_get_comp_number_for_var((DaikonFunctionEntry*)varFuncInfo,
                                                     isEnter,
                                                   g_variableIndex);
        DYNCOMP_TPRINTF("%s[%d](%s) value tag is %d\n",
                        entry->funcEntry.name, g_variableIndex, varName,
                        entry->ppt_exit_var_tags[g_variableIndex]);
        fprintf(decls_fp, "%d", comp_number);
        fputs("\n", decls_fp);
      }
      else {
        // Otherwise, print out unknown comparability type "22"
        fputs("22", decls_fp);
        fputs("\n", decls_fp);
      }
    }

    //Insert this variable into the declared vars table
    genputtable(varsDeclaredTable, varName, (void *)1);

    // We are done!
    return DISREGARD_PTR_DEREFS;
  }

  // Print out the Daikon .decls header depending on whether DynComp is
  // activated or not
  static void printDeclsHeader(void)
  {
    if (!kvasir_old_decls_format) {
      // These are the global records that go at the top of the .decls file

      // TODO: Make separate flags for C and C++; right now this simply
      // prints C/C++.  This information can be grabbed from the DWARF2
      // debug. info. using the DW_AT_language tags (try "readelf -w" on
      // the target program's binary to see what I mean)
      fputs("input-language C/C++\n", decls_fp);

      //Decls version
      fputs("decl-version 2.0\n", decls_fp);

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
      if (!kvasir_old_decls_format) {
        // The format: (entries in brackets are optional, indentation
        //              doesn't matter)

        //    ppt <pptname>
        //      ppt-type <ppt-type>
        //      [parent* <relation-type> <parent-ppt-name>]
        //      [flags <ppt-flags>]

        fputs("ppt ", decls_fp);
        printDaikonFunctionName(funcPtr, decls_fp);

        if (isEnter) {
          fputs(ENTER_PPT, decls_fp);

        }
        else {
          fputs(EXIT_PPT, decls_fp);
        }


        fputs("\n  ppt-type ", decls_fp);

        if (isEnter) {
          fputs("enter\n", decls_fp);
        }
        else{
          //fputs("exit\n", decls_fp);
          fputs("subexit\n", decls_fp);

          // If it's an exit program point, print out an 'enter_exit'
          // parent point to refer back to the ENTER ppt for this
          // function:

          // parent enter_exit has not been working for me.
          // Daikon can interpret correctly with subexit and the # at the end
          // of the name

          /*fputs("  parent enter_exit ", decls_fp);
          printDaikonFunctionName(funcPtr, decls_fp);
          fputs(ENTER_PPT, decls_fp);
          fputs("\n", decls_fp);*/
        }
        // If it's a member function, then print out its parent, which
        // is the object program point of its enclosing class:
        if (kvasir_parent_records && funcPtr->parentClass && funcPtr->parentClass->typeName &&
            (funcPtr->parentClass->aggType->memberVarList &&
             (funcPtr->parentClass->aggType->memberVarList->numVars > 0))) {
          char* ppt_par_id;
          ppt_par_id = getParentId(funcPtr->parentClass->typeName);

          fputs("  parent parent ", decls_fp);
          fputs(funcPtr->parentClass->typeName, decls_fp);
          fputs(OBJECT_PPT, decls_fp);
          fputs(" ", decls_fp);
          fputs(ppt_par_id, decls_fp);
          fputs("\n", decls_fp);
        }

        // If any of the formal parameters are struct/class or
        // struct/class pointer types, then add a 'parent' parent entry to
        // link this program point to the :::OBJECT program point of the
        // struct/class.  If any GLOBAL variables are struct/class or
        // struct/class pointer types, then also do the same thing.

        // We need to have all used object variables at the time of printing
        // the ppt name. Since Fjalar doesn't provide us with this, go through
        // all the variables we will be printing, and see what structs/classes
        // they are members of and print those. We may end up printing more than
        // we actually end up using(Due to nesting) but that should be fine.

        // DON'T HAVE DUPLICATES, THOUGH!  So use a Hashtable to prevent
        // the printing of duplicates:

        {
          struct geniterator* typeNameStrIt = 0;

          // Maps strings to a junk number 1 - simply here to prevent
          // duplicates:
          typeNameStrTable =
            genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                 (int (*)(void *,void *)) &equivalentStrings);

          if (funcPtr->formalParameters.numVars > 0) {
            VarNode* n;
            for (n = funcPtr->formalParameters.first;
                 n != 0;
                 n = n->next) {
              VariableEntry* v = n->var;
              if (IS_AGGREGATE_TYPE(v->varType)) {
                tl_assert(v->varType->typeName);


                nestedTraversalTable =
                  genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                       (int (*)(void *,void *)) &equivalentStrings);

                getUsedObjects(v, typeNameStrTable);
                genfreehashtable(nestedTraversalTable);

                if (!gencontains(typeNameStrTable, v->varType->typeName) &&
                    v->varType->aggType->memberVarList &&
                    (v->varType->aggType->memberVarList->numVars > 0)) {
                  genputtable(typeNameStrTable, v->varType->typeName, (void *)1);
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

                nestedTraversalTable =
                  genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                       (int (*)(void *,void *)) &equivalentStrings);

                getUsedObjects(v, typeNameStrTable);
                genfreehashtable(nestedTraversalTable);

                if (!gencontains(typeNameStrTable, v->varType->typeName) &&
                    v->varType->aggType->memberVarList &&
                    (v->varType->aggType->memberVarList->numVars > 0)) {
                  genputtable(typeNameStrTable, v->varType->typeName, (void *)1);
                }
              }
            }
          }
          typeNameStrIt = gengetiterator(typeNameStrTable);
          // Print everything out, without duplicates!
          while (!typeNameStrIt->finished) {
            char* typeName = (char*)gennext(typeNameStrIt);

            // Don't duplicate ...
            if ((kvasir_parent_records &&
                 (!funcPtr->parentClass || (!VG_STREQ(funcPtr->parentClass->typeName, typeName))))) {
              char* ppt_par_id = getParentId(typeName);
              fputs("  parent parent ", decls_fp);
              fputs(typeName, decls_fp);
              fputs(OBJECT_PPT, decls_fp);
              fputs(" ", decls_fp);
              fputs(ppt_par_id, decls_fp);
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
          DC_convert_bitmatrix_to_sets((DaikonFunctionEntry *)funcPtr, isEnter);
        }
      }
    }

    // Create hash table for all variables printed for an individual ppt
    varsDeclaredTable =
      genallocatehashtable((unsigned int (*)(void *)) &hashString,
                           (int (*)(void *,void *)) &equivalentStrings);

    // Print out globals (visitVariableGroup() ignores the globals if
    // --ignore-globals is used):
    visitVariableGroup(GLOBAL_VAR,
                       funcPtr, // need this for DynComp to work properly
                       isEnter,
                       0,
                       0,
                       (faux_decls ?
                        &nullAction : &printDeclsEntryAction));

    // Now print out one entry for every formal parameter (actual and derived)
    visitVariableGroup(FUNCTION_FORMAL_PARAM,
                       funcPtr,
                       isEnter,
                       0,
                       0,
                       (faux_decls ?
                        &nullAction : &printDeclsEntryAction));

    // If EXIT, print out return value
    if (!isEnter) {
      visitVariableGroup(FUNCTION_RETURN_VAR,
                         funcPtr,
                         0,
                         0,
                         0,
                         (faux_decls ?
                          &nullAction : &printDeclsEntryAction));
    }

    genfreehashtable(varsDeclaredTable);

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

    if (!faux_decls && !kvasir_old_decls_format) {
      genfreehashtable(typeNameStrTable);
      typeNameStrTable = 0;
    }
  }


  // Print out all function declarations in Daikon .decls format
  static void printAllFunctionDecls(char faux_decls)
  {
   if(!funcNameTable) {
       funcNameTable  =
         genallocatehashtable((unsigned int (*)(void *)) &hashString,
                              (int (*)(void *,void *)) &equivalentStrings);
   }

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

   if(funcNameTable) {
     genfreehashtable(funcNameTable);
     funcNameTable = 0;
   }

  }


  // For C++ only: Print out an :::OBJECT program point.
  // The object program point should consist of class_name:::OBJECT
  // and all information from 'this'

  // DynComp: Right now, do NOT try to print out comparability
  // information for OBJECT program points.  We may support this in the
  // future if necessary.
  static void printAllObjectPPTDecls(void) {

    // Object records aren't needed in new decls format unless parent relations are used
    if (!kvasir_parent_records && !kvasir_old_decls_format)
      return;

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

        // We need to print :::OBJECT points regardless for the new decls
        // format, due to the tendency for the ppt printer to print all
        // possible Objects associated with av ariable. So if a variable
        // subclasses a class B, which has no fields, we will still need
        // to have an OBJECT ppt for it.

        if ((!kvasir_old_decls_format ||
             (cur_type->aggType->memberFunctionList &&
              (cur_type->aggType->memberFunctionList->numElts > 0)))&&
            (cur_type->aggType->memberVarList && (cur_type->aggType->memberVarList->numVars > 0)) &&
            cur_type->typeName) {
          tl_assert(cur_type->typeName);

          if (!kvasir_old_decls_format) {
            struct geniterator* typeNameStrIt = 0;
            char* ppt_par_id;
            VarNode *n;

            // Maps strings to a junk number 1 - simply here to prevent
            // duplicates:
            typeNameStrTable =
              genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                   (int (*)(void *,void *)) &equivalentStrings);

            ppt_par_id = getParentId(cur_type->typeName);
            // Example output:
            //   ppt Stack
            //   ppt-type object
            fputs("ppt ", decls_fp);
            fputs(cur_type->typeName, decls_fp);
            fputs(OBJECT_PPT, decls_fp);
            fputs(" ", decls_fp);
            fputs(ppt_par_id, decls_fp);
            fputs("\n  ppt-type object\n", decls_fp);

            // Now comes time to print the 'parent user' entries.  We
            // need to print one for every field inside of this struct
            // that's of a struct type, but not to have duplicates.
            for (n = cur_type->aggType->memberVarList->first;
                 n != 0;
                 n = n->next) {
              VariableEntry* v = n->var;
              if (IS_AGGREGATE_TYPE(v->varType) &&
                  v->varType != cur_type) {
                tl_assert(v->varType->typeName);

                //check for nested Aggregates
                nestedTraversalTable =
                  genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                       (int (*)(void *,void *)) &equivalentStrings);

                getUsedObjects(v, typeNameStrTable);
                genfreehashtable(nestedTraversalTable);

                if (!gencontains(typeNameStrTable, v->varType->typeName) &&
                    v->varType->aggType->memberVarList &&
                    (v->varType->aggType->memberVarList->numVars > 0)) {
                  genputtable(typeNameStrTable, v->varType->typeName, (void *)1);
                }
              }
            }

            // In addition to traversing all arguments, if this is an object method
            // We need to check if we are a subclass. If so traverse all super classes
            traverseNestedClasses(cur_type->aggType, typeNameStrTable);

            typeNameStrIt = gengetiterator(typeNameStrTable);
            // Print everything out, without duplicates!
            while (!typeNameStrIt->finished) {
              char* typeName = (char*)gennext(typeNameStrIt);
              char* ppt_par_id = getParentId(typeName);
              // Gotta use 'parent user' to prevent infinite recursion
              // (or something like that)
              fputs("  parent user ", decls_fp);
              fputs(typeName, decls_fp);
              fputs(OBJECT_PPT, decls_fp);
              fputs(" ", decls_fp);
              fputs(ppt_par_id, decls_fp);
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

          // Create table for all variables printed over a single ppt
          varsDeclaredTable =
            genallocatehashtable((unsigned int (*)(void *)) &hashString,
                                 (int (*)(void *,void *)) &equivalentStrings);

          visitClassMembersNoValues(cur_type, &printDeclsEntryAction);
          cur_type_for_printing_object_ppt = 0;

          genfreehashtable(varsDeclaredTable);

          stringStackPop(fullNameStack, &fullNameStackSize);
          stringStackPop(fullNameStack, &fullNameStackSize);

          fputs("\n", decls_fp);

          if (!kvasir_old_decls_format) {
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




 // Gets all types that this variable may be used to reference
 // (through nesting or otherwise). Caller needs to Allocate
 // nestedTraversalTable before call, and remove it after call
 // to prevent infinite recursion.
 // TODO: Base this on typeEntries instead of strings? Would be
 // interesting, however the fact that classes have no typeEntries
 // may be problematic
 void getUsedObjects(VariableEntry* ent, struct genhashtable* ht)
 {
   AggregateType* agg = 0;
   //nestedTraversalTable should be allocated for us
   tl_assert(nestedTraversalTable);

   if (IS_AGGREGATE_TYPE(ent->varType)) {
     agg = ent->varType->aggType;
   }
   //Punt if not an aggregate type
   else
     return;

   //Member variables
   VarList* members = agg->memberVarList;
   if(members)
     {
       VarNode* n;
       for (n = members->first;
            n != 0;
            n = n->next) {
         VariableEntry* v = n->var;
         if (IS_AGGREGATE_TYPE(v->varType)) {;
         tl_assert(v->varType->typeName);
         if (!gencontains(ht, v->varType->typeName) &&
             v->varType->aggType->memberVarList &&
             (v->varType->aggType->memberVarList->numVars > 0)) {
           //Only add to table if it has variables.
           DPRINTF("Adding %s to referenced objects list\n", v->varType->typeName);
           genputtable(ht, v->varType->typeName, (void *)1);
          }
         if (!gencontains(nestedTraversalTable, v->varType->typeName)) {
           genputtable(nestedTraversalTable, v->varType->typeName, (void *)1);
           getUsedObjects(v, ht);
          }
          }
        }
      }

   // SuperClasses need to be done separately as they are represented differently
   traverseNestedClasses(agg, ht);

  }

 // Helper recursive function for obtaining superclasses of a variable
 // needed because we don't get full variable entries for superclasses, just
 // these AggregateTypes/Superclass structs
 void traverseNestedClasses(AggregateType* agg, struct genhashtable *ht)
  {
   //Super Class Variables
   SimpleList* supers =  agg->superclassList;
   if(supers) {
     SimpleNode* n;
     for (n = supers->first;
          n != 0;
          n = n->next) {
       Superclass* s = (Superclass *)n->elt;
       if (IS_AGGREGATE_TYPE(s->class)) {
         tl_assert(s->class->typeName);
         if (!gencontains(ht, s->class->typeName)) {
           DPRINTF("Adding %s to referenced objects list\n", s->class->typeName);
           genputtable(ht, s->class->typeName, (void *)1);
           AggregateType* subAgg = s->class->aggType;
           if(subAgg)
             {
               traverseNestedClasses(subAgg,ht);
              }
          }
        }
      }
    }
 }


 // Gets the unique ID for a given type. Will generate an ID
 // and insert into table if non existant.
 // CALLER IS RESPONSIBLE FOR FREEING RETURNED STRING
 char* getParentId(char* typeName){

   int digits = 0, cur_id=curr_par_id, *par_id;
   char* ppt_par_id;

   // objectIdTable should be instantiated by now
   tl_assert(objectIdTable);

   // We return the id as a string for convenicence
   // However, we need to allocate enough room in
   // the string for however large the number is.
   while (cur_id > 0) {
       digits++;
       cur_id = cur_id/10;
     }

   ppt_par_id = VG_(calloc)("decls-output.c: gPID", 1, digits+1); // Digits + whitespace

   if(!objectIdTable) {
       objectIdTable =
         genallocatehashtable((unsigned int (*)(void *)) &hashString,
                              (int (*)(void *,void *)) &equivalentStrings);
   }

   if(!gencontains(objectIdTable, typeName)) {
       int *new_id = VG_(malloc)("decls-output.c: gPID.2", sizeof(int));
       *new_id = curr_par_id;
       genputtable(objectIdTable, typeName, new_id);
       curr_par_id++;
     }
   par_id = gengettable(objectIdTable, typeName);
   sprintf(ppt_par_id, " %d", *par_id);
   return ppt_par_id;
  }

 /** The next 3 functions are utilities for dealing with the string arrays
     Fjalar provides for enclosing variables **/

 // Utility function for getting the (string) length of
 // some portion of a string array
 int stringArrayLen(char** stringArr,int start, int end)
  {
   int i, len = 0;
   for(i=start; i < end; i++) {
     len += VG_(strlen)(stringArr[i]);
    }
   return len;
  }

 // Utility function for flattening a string array into
 // a single string.
 // CALLER IS RESPONSIBLE FOR FREEING RETURNED STRING
 char* stringArrayFlatten(char** stringArr, int start, int end)
 {
   int i, str_len = stringArrayLen(stringArr, start, end);
   char* str = VG_(calloc)("decls-output.c: stringArrayFlatten", str_len, sizeof(char));

   for(i = start; i < end; i++) {
     VG_(strcat)(str, stringArr[i]);
    }

   return str;
 }


 // Remove the super Entries from a stringArray
 // I.E. if we have A.B.c where B is a superclass
 // of A, this will return A.c
 // CALLER IS RESPONSIBLE FOR FREEING RETURNED STRING
 char* removeSuperElements(char** stringArr, VariableEntry* var)
 {
   // RUDD Beautificatn. Next Release.
   //   int len = fullNameStackSize-2*var->isSuperMember-1;
   int len = fullNameStackSize;
   char*  name = stringArrayFlatten(stringArr, 0, len);
   return name;
 }
