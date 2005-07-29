/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* typedata.h:
   Everything here attempts to extract the information directly
   from the DWARF2 debugging information embedded within an ELF
   executable, piggy-backing off of readelf.c code. These data
   structures mimic the types of DWARF2 entries that we are interested
   in tracking.
*/

#ifndef TYPEDATA_H
#define TYPEDATA_H

#include "GenericHashtable.h"

// Type information data structures

// Contains one entry that holds data for one of many possible types
// depending on tag_name
typedef struct
{
  unsigned long ID; // Unique ID for each entry
  unsigned long tag_name; // DW_TAG_____ for the type of this entry
  int level; // The level of this entry (useful for nested structs and function local vars.)
  unsigned long sibling_ID; // for DW_AT_sibling
  void* entry_ptr; // Cast this pointer depending on value of tag_name, which specifies
                   // the "type" of this dwarf_entry
} dwarf_entry;

// Entries for individual types

typedef struct
{
  unsigned long byte_size; // DW_AT_byte_size
  unsigned long encoding;

  // TODO: support for bit fields not yet implemented
  //  char is_bit_field; // 1 = bit field
  // Only relevant for bit fields
  unsigned long bit_size;
  unsigned long bit_offset;
} base_type; // DW_TAG_base_type

// modifier_type corresponds to the following DWARF2 types:
//   {DW_TAG_const_type, _pointer_type, _reference_type, _volatile_type}
typedef struct
{
  unsigned long target_ID; // ID of the entry that contains the type that this modifies
  dwarf_entry* target_ptr; // Type that this entry modifies (DW_AT_type)
} modifier_type;

// collection_type corresponds to the following DWARF2 types:
//   {DW_TAG_structure_type, _union_type, _enumeration_type}
typedef struct
{
  char* name;
  unsigned long byte_size;

  unsigned long num_member_vars;
  dwarf_entry** member_vars; // Array of size num_members; Each element is a
                            // POINTER to a dwarf_entry of type = {member, enumerator}

  unsigned long num_member_funcs; // C++ only - for member functions
  dwarf_entry** member_funcs; // Array of size num_members; Each element is a
                              // POINTER to a dwarf_entry of type = {function}
                              // but these functions are only "declarations" and we need
                              // to look elsewhere in DWARF to find their true definitions
                              // (This is only true if function definitions and declarations
                              //  are made in separate .h and .cpp files in typical C++ fashion)

  unsigned long num_static_member_vars; // C++ only - for static member variables
  dwarf_entry** static_member_vars; // Array of size num_static_member_vars; Each element is a
                                    // POINTER to a dwarf_entry of type = {variable}
} collection_type;

// struct or union member
typedef struct
{
  char* name;
  unsigned long type_ID;
  dwarf_entry* type_ptr;
  unsigned long data_member_location;
                             // Addr offset relative to struct head
                             // This will be 0 for a union
                             // This is stored as:
                             // (DW_OP_plus_uconst: x)
                             // where x is the location relative to struct head

  // TODO: support for bit fields not yet implemented
  //  char is_bit_field; // 1 = bit field
  // Only relevant for bit fields
  unsigned long internal_byte_size;
  unsigned long internal_bit_offset;
  unsigned long internal_bit_size;
} member;

// enumeration member
typedef struct
{
  char* name;
  long const_value; // Enumeration value
                    // (SIGNED!) Negative enum values are possible
} enumerator;

// function
typedef struct
{
  char* name;
  char* mangled_name; // The mangled name of the function (only relevant for C++)
  char* filename; // The file name relative to the compilation directory

  unsigned long return_type_ID;
  dwarf_entry* return_type;

  // This array is NO LONGER inlined within dwarf_entry_array
  unsigned long num_formal_params;
  dwarf_entry** params; // Array of size num_formal_params, type = {formal_parameter}
                        // Each entry of this array is a POINTER to a dwarf_entry
                        // of type {formal_parameter}

  // This array is NO LONGER inlined within dwarf_entry_array
  unsigned long num_local_vars;
  dwarf_entry** local_vars; // Array of size num_local_vars, type = {variable}
                            // Each entry of this array is a POINTER to a dwarf_entry
                            // of type {variable}

  char is_external; /* Is it extern? If so, probably want to skip it */
  char is_member_func; /* 1 if it's a member function (within a class or struct) */
  char is_declaration; // Relevant for C++: 1 if this function is an empty
  // declaration - all of the important info. about this function comes from
  // the matching entry whose specification_ID field is the ID of this entry
  // Do NOT add an entry with is_declaration == 1 to
  // DaikonFunctionInfoTable because it's an empty shell ...
  // instead add its analogue whose specification_ID points to this entry
  char accessibility; // 0 if none - ASSUMED TO BE PUBLIC!!!
                      // 1 (DW_ACCESS_public) if public,
                      // 2 (DW_ACCESS_protected) if protected,
                      // 3 (DW_ACCESS_private) if private

  unsigned long specification_ID; // Relevant for C++: This is a valid ID
  // of a dwarf_entry (of type function) if this function entry represents
  // the actual data for the entry with ID equal to specification_ID

  unsigned long start_pc; /* Location of the function in memory */
  unsigned long end_pc;   /* Location of the highest address of an
                             instruction in the function */

} function;

// TODO: support for function pointer parameters not yet implemented
/* This is for abstract function types, as might be used in declaring
   a parameter as taking a function pointer. At least for the moment, we
   won't bother about the parameters. */
typedef struct {
  unsigned long return_type_ID;
  dwarf_entry* return_type;
} function_type;

// function formal parameter
typedef struct
{
  char* name;
  unsigned long type_ID;
  dwarf_entry* type_ptr;
  unsigned long location; // Offset from function base
                 // This is stored as: (DW_OP_fbreg: x),
                 // where x is location offset
                 // TODO: DW_OP_fbreg: seems unreliable - gives flaky
                 //       values sometimes - look into finding a better
                 //       way to get the parameter location
} formal_parameter;

// compile_unit - only used to figure out filename and compilation directory
// We assume that every function belongs to the file specified
// by the nearest compile_unit entry (to its left) in dwarf_entry_array
typedef struct
{
  char* filename;
  char* comp_dir;
} compile_unit;

// array type - each one has an array_subrange_type entry denoting
//              the size of each dimension in the array
typedef struct
{
  unsigned long type_ID;
  dwarf_entry* type_ptr;

  // This array is NO LONGER inlined within dwarf_entry_array
  // There is one array_subrange_type entry for each dimension of the array
  unsigned long num_subrange_entries;
  dwarf_entry** subrange_entries; // Array of size num_subrange_entries; Each element
                                  // is a POINTER to a dwarf_entry of type = {subrange_type}
} array_type;

// array subrange type - each one belongs to a particular array_type entry
typedef struct
{
  unsigned long upperBound; // max. index of the array in this particular dimension
} array_subrange_type;

// typedef type - specifies a typedef to another type
typedef struct
{
  char* name;
  unsigned long target_type_ID;
  dwarf_entry* target_type_ptr;
} typedef_type;

// variable - specifies a variable, either global or local,
typedef struct
{
  char* name;
  char* mangled_name;    // only for C++ static member variables
  unsigned long type_ID;
  dwarf_entry* type_ptr;

  int is_external; // is it accessible from outside the file scope?

  char couldBeGlobalVar; // true if it COULD BE a global variable, false if local
  // global variables have DW_OP_addr attribute defined, but ...
  // C++ bizarre counter-example: DW_OP_addr is sometimes defined
  // for weird empty variables so this does not imply that it's global
  // However, it is a truly global variable if couldBeGlobalVar is true
  // and both specification_ID and is_declaration are false

  char is_declaration_or_artificial;
  // Relevant for C++: 1 if this variable is an empty declaration
  // Do NOT add an entry with is_declaration non-null to
  // any variable lists because it's an empty shell
  // Set this to 1 if you encounter a DW_AT_artificial attribute
  // for a DWARF variable entry as well as a DW_AT_declaration attribute

  char isStaticMemberVar; // only for C++ static member variables

  unsigned long specification_ID; // Relevant fo C++:
  // DO NOT add an entry with specification_ID non-null to any variable
  // lists because it's an empty shell

  unsigned long globalVarAddr; // only valid for global variables
  int offset; // only valid for local variables

} variable;

// Globals

extern dwarf_entry* dwarf_entry_array;
extern unsigned long dwarf_entry_array_size;

unsigned int hashString(char* str);
int equivalentStrings(char* str1, char* str2);


// Function declarations

// From readelf.c
char *get_TAG_name(unsigned long tag);
int process_elf_binary_data(char* filename);

// From typedata.c
char tag_is_relevant_entry(unsigned long tag);
char tag_is_modifier_type(unsigned long tag);
char tag_is_collection_type(unsigned long tag);
char tag_is_base_type(unsigned long tag);
char tag_is_member(unsigned long tag);
char tag_is_enumerator(unsigned long tag);
char tag_is_function(unsigned long tag);
char tag_is_formal_parameter(unsigned long tag);
char tag_is_compile_unit(unsigned long tag);
char tag_is_function_type(unsigned long tag);
char entry_is_listening_for_attribute(dwarf_entry* e, unsigned long attr);

char harvest_type_value(dwarf_entry* e, unsigned long value);
char harvest_byte_size_value(dwarf_entry* e, unsigned long value);
char harvest_encoding_value(dwarf_entry* e, unsigned long value);
char harvest_bit_size_value(dwarf_entry* e, unsigned long value);
char harvest_bit_offset_value(dwarf_entry* e, unsigned long value);
char harvest_const_value(dwarf_entry* e, unsigned long value);
char harvest_name(dwarf_entry* e, const char* str);
char harvest_mangled_name(dwarf_entry* e, const char* str);
char harvest_comp_dir(dwarf_entry* e, const char* str);
char harvest_formal_param_location(dwarf_entry* e, unsigned long value);
char harvest_data_member_location(dwarf_entry* e, unsigned long value);
char harvest_string(dwarf_entry* e, unsigned long attr, const char* str);
char harvest_external_flag_value(dwarf_entry *e, unsigned long value);
char harvest_address_value(dwarf_entry* e, unsigned long attr, unsigned long value);
char harvest_variable_addr_value(dwarf_entry* e, unsigned long value);
char harvest_ordinary_unsigned_value(dwarf_entry* e, unsigned long attr, unsigned long value);
char harvest_local_var_offset(dwarf_entry* e, unsigned long value);
char harvest_sibling(dwarf_entry* e, unsigned long value);
char harvest_declaration_value(dwarf_entry* e, unsigned long value);
char harvest_artificial_value(dwarf_entry* e, unsigned long value);
char harvest_specification_value(dwarf_entry* e, unsigned long value);
char harvest_function_accessibility(dwarf_entry* e, char a);

char binary_search_dwarf_entry_array(unsigned long target_ID, unsigned long* index_ptr);

void link_array_type_to_members(dwarf_entry* e, unsigned long dist_to_end);
void link_collection_to_members(dwarf_entry* e, unsigned long dist_to_end);
void link_function_to_params_and_local_vars(dwarf_entry* e, unsigned long dist_to_end);
void determineTypedefNameForEntry(char** entry_name, dwarf_entry* e);
void print_dwarf_entry(dwarf_entry* e, char simplified);

void initialize_dwarf_entry_array(unsigned long num_entries);
void destroy_dwarf_entry_array(void);
void simple_print_dwarf_entry_array();
void print_dwarf_entry_array();
void print_dwarf_entry_array_helper(char simplified);
void initialize_dwarf_entry_ptr(dwarf_entry* e);
void finish_dwarf_entry_array_init(void);

char tag_is_modifier_type(unsigned long tag);
char tag_is_collection_type(unsigned long tag);
char tag_is_base_type(unsigned long tag);
char tag_is_member(unsigned long tag);
char tag_is_enumerator(unsigned long tag);
char tag_is_function(unsigned long tag);
char tag_is_formal_parameter(unsigned long tag);
char tag_is_array_type(unsigned long tag);
char tag_is_array_subrange_type(unsigned long tag);
char tag_is_typedef(unsigned long tag);
char tag_is_variable(unsigned long tag);

char* findFilenameForEntry(dwarf_entry* e);
unsigned long findFunctionStartPCForVariableEntry(dwarf_entry* e);

#endif
