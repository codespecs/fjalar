/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

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

#include "typedata.h"
#include "GenericHashtable.h"


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

// Like FunctionTable, but indexed by the address where we do entry
// instrumentation.
struct genhashtable* FunctionTable_by_entryPC;

// Like the above 2, except it is indexed by the end of the first
// basic block of a function. This is needed for the main
// special case. See "HANDLING MAIN" in fjalar_main.c:handle_possible_entry()
struct genhashtable* FunctionTable_by_endOfBb;

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
// Keys: the name of a TypeEntry (TypeEntry::typeName)
// Values: TypeEntry corresponding to that name
//         (Hopefully, if all goes well, the only TypeEntry values
//          in this table are REAL entries whose dwarf_entry has
//          is_declaration NULL, not fake declaration entries)

// Only non-basic types (IS_BASIC_TYPE(t) == 0) should appear in
// TypesTable:
struct genhashtable* TypesTable;

void initializeAllFjalarData(void);

// Call this function whenever you want to check that the data
// structures in this file all satisfy their respective
// rep. invariants.  This can only be run after
// initializeAllFjalarData() has initialized these data structures.
void repCheckAllEntries(void);

FILE* xml_output_fp;
void outputAllXMLDeclarations(void);

char* getRawCppFunctionName(char* cppFnName);
#endif
