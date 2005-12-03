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

#ifndef GENERATE_FJALAR_ENTRIES_H
#define GENERATE_FJALAR_ENTRIES_H

#include "fjalar_include.h"
#include "tool.h"
#include "typedata.h"
#include "GenericHashtable.h"
#include <stdio.h>


// Hash table containing structs already visited while
// deriving variables
// Keys: address of struct TypeEntry
// Values: number of times that this type has been hit while deriving
//         variables
struct genhashtable* VisitedStructsTable;


// Hashtable that holds information about all functions
// Key: (unsigned int) address of the function's first instruction (startPC)
// Value: (FunctionEntry*) Pointer to FunctionEntry
struct genhashtable* FunctionTable;


// WARNING: The only entries in TypesTable are for types that are
// actually associated with variables used in the program.  If no
// variable in your program uses a certain type, then it does not have
// an entry in here!!!  This prevents us from including all sorts of
// junky types from libraries in this table (which have entries in the
// debug. info.) and ensures that we only have types in here that are
// referenced by variables that we are tracing.  The one down-side of
// this strategy is that when you are coercing types using a .disambig
// file, you must coerce it to a type that is used by some other
// variable, or else it doesn't appear in this table.

// Hash table containing TypeEntry entries
// Keys: the name of a TypeEntry (TypeEntry::collectionName)
// Values: TypeEntry corresponding to that name
//         (Hopefully, if all goes well, the only TypeEntry values
//          in this table are REAL entries whose dwarf_entry has
//          is_declaration NULL, not fake declaration entries)

// Only non-basic types (IS_BASIC_TYPE(t) == 0) should appear in
// TypesTable:
struct genhashtable* TypesTable;

// List of all global variables
// (including C++ static member variables - these have structParentType initialized
//  so DON'T TRY TO PRINT THEM AT ALL PROGRAM POINTS OR ELSE WE WILL SEGFAULT OFTEN!
//  only try to print them during program points whose FunctionEntry::parentClass ==
//  VariableEntry::structParentType
VarList globalVars;

void initializeAllFjalarData();

// Call this function whenever you want to check that the data
// structures in this file all satisfy their respective
// rep. invariants.  This can only be run after
// initializeAllFjalarData() has initialized these data structures.
void repCheckAllEntries();

int determineFormalParametersStackByteSize(FunctionEntry* f);

FILE* xml_output_fp;
void outputAllXMLDeclarations();

char* getRawCppFunctionName(char* cppFnName);

#endif
