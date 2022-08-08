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

/* typedata.c:
   This file contains functions that serve to complement readelf.c
   and parse the DWARF2 debugging information into an orderly
   format within dwarf_entry_array.

   This should NOT be visible to tools.
*/

#include "my_libc.h"

#include "typedata.h"
#include "generate_fjalar_entries.h"

#include "fjalar_main.h"
#include "fjalar_dwarf.h"

#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"

// for name demangling
#include "../coregrind/m_demangle/demangle.h"
extern char * cplus_demangle_v3 (const char *, int);


// Global array of all dwarf entries, sorted (hopefully) by dwarf_entry.ID
// so that binary search is possible
// DO NOT MODIFY THIS POINTER MANUALLY!!!
// Representation invariants:
// 1. Every entry in dwarf_entry_array is sorted by ascending ID
//    (This makes binary search possible)
// 2. dwarf_entry_array points to the beginning of the array
// 3. The size of the array is specified by dwarf_entry_array_size
// 4. All function entries are listed adjacent to their formal parameters
//    and local variables, in that specific order (NO LONGER necessarily true)
// 5. All struct, union, and enumeration entries are listed adjacent
//    to their members (NO LONGER TRUE - There can be nesting now)
// 6. All entries in the array belong to the file specified by the first
//    compile_unit entry to its left (lower indices) in the array
dwarf_entry* dwarf_entry_array = NULL;

// Global array of all compilation units. It simply contains
// their dwarf entry.
compile_unit** comp_unit_info = NULL;
static unsigned long comp_unit_info_idx = 0;

// The size of this array
unsigned long dwarf_entry_array_size = 0;

// Global hash table containing a mapping between
// Location list offsets and a linked list representing
// the location list
struct genhashtable* loc_list_map = 0;

// Linked list representing debug_frame
debug_frame* debug_frame_HEAD = 0;
debug_frame* debug_frame_TAIL = 0;

// Base of the current compilation unit

unsigned int comp_unit_base = 0;

// Target program producer info
Bool clang_producer = False;
Bool other_producer = False;

// The addresses and sizes of the sections (.data, .bss, .rodata, and .data.rel.ro)
// that hold global variables (initialized in readelf.c):
unsigned int data_section_addr = 0;
unsigned int data_section_size = 0;
unsigned int bss_section_addr = 0;
unsigned int bss_section_size = 0;
unsigned int rodata_section_addr = 0;
unsigned int rodata_section_size = 0;
unsigned int relrodata_section_addr = 0;
unsigned int relrodata_section_size = 0;

// typedef names optimization:
// This was implemented as an optimization to speed up
// determineTypedefNameForEntry(), which has been determined to be a
// major performance bottleneck:

// Key: (unsigned int) target_type_ID (the dwarf_entry ID that a typedef
// entry points to)
// Value: char* containing the NAME of the typedef entry with the
// specified target_type_ID
struct genhashtable* typedef_names_map = 0;

/*----------------------------------------
Extracting type information from DWARF tag
-----------------------------------------*/


/*
Requires:
Modifies:
Returns: 1 if tag = {DW_TAG_base_type, _const_type, _enumerator,
                     _formal_parameter, _pointer_type, _reference_type,
                     _array_type, _subprogram,
                     _union_type, _enumeration_type, _member, _subroutine_type
                     _structure_type, _volatile_type, _compile_unit,
                     _array_type, _subrange_type, _typedef, _variable, _inheritance,
                     _namespace},
                     0 otherwise
Effects: Used to determine which entries to record into a dwarf_entry structure;
         All relevant entries should be included here
*/
char tag_is_relevant_entry(unsigned long tag)
{
  switch (tag)
    {
    case DW_TAG_array_type:
    case DW_TAG_base_type:
    case DW_TAG_class_type:
    case DW_TAG_compile_unit:
    case DW_TAG_const_type:
    case DW_TAG_enumeration_type:
    case DW_TAG_enumerator:
    case DW_TAG_formal_parameter:
    case DW_TAG_inheritance:
    case DW_TAG_member:
    case DW_TAG_namespace:
    case DW_TAG_pointer_type:
    case DW_TAG_reference_type:
    case DW_TAG_structure_type:
    case DW_TAG_subprogram:
    case DW_TAG_subrange_type:
    case DW_TAG_subroutine_type:
    case DW_TAG_typedef:
    case DW_TAG_union_type:
    case DW_TAG_variable:
    case DW_TAG_volatile_type:
      return 1;
    default:
      return 0;
    }
}

/*
Requires:
Modifies:
Returns: 1 if tag = {DW_TAG_pointer_type,  _reference_type, _const_type, _volatile_type},
                     0 otherwise
Effects: Used to determine if the type is a modifier - modifier types
         refer to another type within the dwarf_entry_array after
         preprocessing
*/
char tag_is_modifier_type(unsigned long tag)
{
  switch (tag)
    {
    case DW_TAG_const_type:
    case DW_TAG_pointer_type:
    case DW_TAG_reference_type:
    case DW_TAG_volatile_type:
      return 1;
    default:
      return 0;
    }
}

/*
Requires:
Modifies:
Returns: 1 if tag = {DW_TAG_enumeration_type, _structure_type, _union_type},
                     0 otherwise
Effects: Used to determine if the type is a collection of some sort -
         collections have members and unique type names
*/
char tag_is_collection_type(unsigned long tag)
{
  switch (tag)
    {
    case DW_TAG_enumeration_type:
    case DW_TAG_structure_type:
    case DW_TAG_class_type:
    case DW_TAG_union_type:
      return 1;
    default:
      return 0;
    }
}

// The rest of these should be self-explanatory:
char tag_is_base_type(unsigned long tag)
{
  return (tag == DW_TAG_base_type);
}

char tag_is_member(unsigned long tag)
{
  return (tag == DW_TAG_member);
}

char tag_is_enumerator(unsigned long tag)
{
  return (tag == DW_TAG_enumerator);
}

char tag_is_function(unsigned long tag)
{
  return (tag == DW_TAG_subprogram);
}

char tag_is_formal_parameter(unsigned long tag)
{
  return (tag == DW_TAG_formal_parameter);
}

char tag_is_compile_unit(unsigned long tag)
{
  return (tag == DW_TAG_compile_unit);
}

char tag_is_function_type(unsigned long tag) {
  return (tag == DW_TAG_subroutine_type);
}

char tag_is_array_type(unsigned long tag) {
  return (tag == DW_TAG_array_type);
}

// Every array has one of these entries following it,
// one for each dimension
char tag_is_array_subrange_type(unsigned long tag) {
  return (tag == DW_TAG_subrange_type);
}

char tag_is_typedef(unsigned long tag) {
  return (tag == DW_TAG_typedef);
}

// Can be either global or local variable -
// but we only care about globals right now
char tag_is_variable(unsigned long tag) {
  return (tag == DW_TAG_variable);
}

char tag_is_inheritance(unsigned long tag) {
  return (tag == DW_TAG_inheritance);
}

static char tag_is_namespace(unsigned long tag) {
  return (tag == DW_TAG_namespace);
}

/*------------------
 Attribute listeners
 ------------------*/

// Each type stored in dwarf_entry.entry_ptr listens for particular
// attributes.  e.g. collection_type listens for DW_AT_name and DW_AT_byte_size

// List of attributes and the types which listen for them:

// DW_AT_abstract_origin: function, formal_parameter
// DW_AT_accessibility: function, inheritance, member, variable
// DW_AT_artificial: variable
// DW_AT_bit_offset: base_type, member
// DW_AT_bit_size: base_type, member
// DW_AT_byte_size: base_type, collection_type, member
// DW_AT_comp_dir: compile_unit
// DW_AT_const_value: enumerator
// DW_AT_data_member_location: member, inheritance
// DW_AT_declaration: function, variable, collection_type
// DW_AT_decl_file: variable, member
// DW_AT_encoding: base_type
// DW_AT_external: function, variable, member
// DW_AT_frame_base: compile_unit, function
// DW_AT_high_pc: function
// DW_AT_location: formal_parameter, variable
// DW_AT_low_pc: compile_unit, function
// DW_AT_MIPS_linkage_name: function, variable
// DW_AT_name: collection_type, member, enumerator, function, formal_parameter, compile_unit, typedef, namespace, variable
// DW_AT_producer: compile_unit
// DW_AT_sibling: collection_type, function_type, enumerator, function, array_type
// DW_AT_specification: function, variable, collection_type
// DW_AT_stmt_list: compile_unit
// DW_AT_type: modifier_type, member, function, formal_parameter, function_type, array_type, typedef, variable, inheritance
// DW_AT_upper_bound: array_subrange_type

// Returns: 1 if the entry has a type that is listening for the
// given attribute (attr), 0 otherwise
char entry_is_listening_for_attribute(dwarf_entry* e, unsigned long attr)
{
  unsigned long tag;

  if(e == 0)
    return 0;

  tag = e->tag_name;
  switch(attr)
    {
    case DW_AT_sibling:
      return (tag_is_collection_type(tag) ||
              tag_is_function_type(tag) ||
              tag_is_enumerator(tag) ||
              tag_is_function(tag) ||
              tag_is_array_type(tag));
    case DW_AT_location:
      return (tag_is_formal_parameter(tag) ||
              tag_is_variable(tag));
    case DW_AT_data_member_location:
      return (tag_is_member(tag) ||
              tag_is_inheritance(tag));
    case DW_AT_name:
      return (tag_is_collection_type(tag) ||
              tag_is_member(tag) ||
              tag_is_enumerator(tag) ||
              tag_is_function(tag) ||
              tag_is_formal_parameter(tag) ||
              tag_is_compile_unit(tag) ||
              tag_is_typedef(tag) ||
              tag_is_namespace(tag) ||
              tag_is_variable(tag));
    case DW_AT_byte_size:
      return (tag_is_base_type(tag) ||
              tag_is_collection_type(tag) ||
              tag_is_member(tag));
    case DW_AT_bit_offset:
      return (tag_is_base_type(tag) ||
              tag_is_member(tag));
    case DW_AT_bit_size:
      return (tag_is_base_type(tag) ||
              tag_is_member(tag));
    case DW_AT_const_value:
      return (tag_is_enumerator(tag) ||
              tag_is_variable(tag) ||
              tag_is_member(tag));
    case DW_AT_type:
      return (tag_is_modifier_type(tag) ||
              tag_is_member(tag) ||
              tag_is_function(tag) ||
              tag_is_formal_parameter(tag) ||
              tag_is_function_type(tag) ||
              tag_is_array_type(tag) ||
              tag_is_typedef(tag) ||
              tag_is_variable(tag) ||
              tag_is_inheritance(tag));
    case DW_AT_encoding:
      return tag_is_base_type(tag);
    case DW_AT_comp_dir:
      return tag_is_compile_unit(tag);
    case DW_AT_producer:
      return tag_is_compile_unit(tag);
    case DW_AT_external:
      return (tag_is_function(tag) ||
              tag_is_variable(tag) ||
              tag_is_member(tag));
    case DW_AT_frame_base:
    case DW_AT_low_pc:
      return (tag_is_compile_unit(tag) ||
              tag_is_function(tag));
    case DW_AT_high_pc:
      return tag_is_function(tag);
    case DW_AT_upper_bound:
      return tag_is_array_subrange_type(tag);
    case DW_AT_MIPS_linkage_name:
      return (tag_is_function(tag) ||
              tag_is_variable(tag));
    case DW_AT_specification:
      return (tag_is_function(tag) ||
              tag_is_variable(tag) ||
              tag_is_collection_type(tag));
    case DW_AT_declaration:
      return (tag_is_function(tag) ||
              tag_is_variable(tag) ||
              tag_is_collection_type(tag));
    case DW_AT_artificial:
      return tag_is_variable(tag);
    case DW_AT_accessibility:
      return (tag_is_function(tag) ||
              tag_is_inheritance(tag) ||
              tag_is_member(tag) ||
              tag_is_variable(tag));
    case DW_AT_abstract_origin:
      return (tag_is_function(tag) ||
              tag_is_formal_parameter(tag));;
    case DW_AT_stmt_list:
      return tag_is_compile_unit(tag);
    case DW_AT_decl_file:
      return (tag_is_variable(tag) ||
              tag_is_member(tag));
    default:
      return 0;
    }
}

/*--------
Harvesters
---------*/
// Harvest attribute values into the appropriate entry
// and fill up the respective data fields.
// Returns a boolean to signal success or failure
// (Remember to only harvest attribute value if the type is listening for it)

char harvest_type_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_modifier_type(tag))
    {
      ((modifier_type*)e->entry_ptr)->target_ID = value;
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->type_ID = value;
      return 1;
    }
  else if (tag_is_function(tag))
    {
      ((function*)e->entry_ptr)->return_type_ID = value;
      return 1;
    }
  else if (tag_is_formal_parameter(tag))
    {
      ((formal_parameter*)e->entry_ptr)->type_ID = value;
      return 1;
    }
  else if (tag_is_function_type(tag))
    {
      ((function_type*)e->entry_ptr)->return_type_ID = value;
      return 1;
    }
  else if (tag_is_array_type(tag))
    {
      ((array_type*)e->entry_ptr)->type_ID = value;
      return 1;
    }
  else if (tag_is_typedef(tag))
    {
      ((typedef_type*)e->entry_ptr)->target_type_ID = value;
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->type_ID = value;
      return 1;
    }
  else if (tag_is_inheritance(tag))
    {
      ((inheritance_type*)e->entry_ptr)->superclass_type_ID = value;
      return 1;
    }
  else
    return 0;
}

char harvest_byte_size_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_base_type(tag))
    {
      ((base_type*)e->entry_ptr)->byte_size = value;
      return 1;
    }
  else if (tag_is_collection_type(tag))
    {
      ((collection_type*)e->entry_ptr)->byte_size = value;
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->internal_byte_size = value;
      return 1;
    }
  else
    return 0;
}

char harvest_decl_file(dwarf_entry* e, unsigned long value)
{
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  //  FJALAR_DPRINTF("Harvesting decl_file value %lu for %p (ID: %lu)\n", value, e, e->ID);

  if (tag_is_variable(e->tag_name))
    {
      ((variable*)e->entry_ptr)->decl_file = value;
    }
  else if (tag_is_member(e->tag_name))
    {
      ((member*)e->entry_ptr)->decl_file = value;
    }
  
  return 1;
}

char harvest_file_name_table(unsigned long debug_line_offset, XArray* table) 
{ 
  int i;
  for(i = 0; i < comp_unit_info_idx; i++) {
    if (comp_unit_info[i]->stmt_list == debug_line_offset) {
      comp_unit_info[i]->file_name_table = table;
      return 1;
    }
  }
  return 0;
}

char harvest_sibling(dwarf_entry* e, unsigned long value)
{
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;
  e->sibling_ID = value;
  return 1;
}

char harvest_encoding_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_base_type(tag))
    {
      ((base_type*)e->entry_ptr)->encoding = value;
      return 1;
    }
  else
    return 0;
}

char harvest_variable_addr_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_variable(tag))
    {
       ((variable*)e->entry_ptr)->couldBeGlobalVar = 1;
      ((variable*)e->entry_ptr)->globalVarAddr = value;
      return 1;
    }
  else
    return 0;
}

static char harvest_upper_bound_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_array_subrange_type(tag))
    {

      // For some reason, a negative value for upperBound corresponds to
      // "(locationList)" but we'll ignore it for now: e.g.:
      /*
        <1><12d1>: Abbrev Number: 8 (DW_TAG_array_type)
        DW_AT_sibling     : <12e4>
        DW_AT_type        : <f1b>
        <2><12da>: Abbrev Number: 23 (DW_TAG_subrange_type)
        DW_AT_type        : <367>
        DW_AT_upper_bound : -1       (location list)
      */

      // If we have a value of -1, turn it to zero
      if ((long)value == -1) {
        value = 0;
      }

      ((array_subrange_type*)e->entry_ptr)->upperBound = value;
      return 1;
    }
  else
    return 0;
}

char harvest_declaration_value(dwarf_entry* e, unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag)) {
    ((function*)e->entry_ptr)->is_declaration = value;
    return 1;
  }
  else if (tag_is_variable(tag)) {
    ((variable*)e->entry_ptr)->is_declaration_or_artificial = value;
    return 1;
  }
  else if (tag_is_collection_type(tag)) {
    ((collection_type*)e->entry_ptr)->is_declaration = value;
    return 1;
  }
  else
    return 0;
}

char harvest_artificial_value(dwarf_entry* e, unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_variable(tag)) {
    ((variable*)e->entry_ptr)->is_declaration_or_artificial = value;
    return 1;
  }
  else
    return 0;
}

char harvest_specification_value(dwarf_entry* e, unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag)) {
    ((function*)e->entry_ptr)->specification_ID = value;

    return 1;
  }
  else if (value && (tag_is_variable(tag))) {
    ((variable*)e->entry_ptr)->specification_ID = value;
    return 1;
  } else if (value && (tag_is_collection_type(tag))) {
    ((collection_type*)e->entry_ptr)->specification_ID = value;
    return 1;
  }
  else
    return 0;
}

char harvest_abstract_origin_value(dwarf_entry* e, unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag)) {
    ((function*)e->entry_ptr)->abstract_origin_ID = value;
    return 1;
  } else if (tag_is_formal_parameter(tag)) {
    ((formal_parameter*)e->entry_ptr)->abstract_origin_ID = value;
    return 1;
  }
  else
    return 0;
}

char harvest_accessibility(dwarf_entry* e, char a) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag)) {
    ((function*)e->entry_ptr)->accessibility = a;
    //    printf("harvest_accessibility %d\n", a);
    return 1;
  }
  else if (tag_is_inheritance(tag))
    {
      ((inheritance_type*)e->entry_ptr)->accessibility = a;
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->accessibility = a;
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->accessibility = a;
      return 1;
    }
  else
    return 0;
}

char harvest_bit_size_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_base_type(tag))
    {
      ((base_type*)e->entry_ptr)->bit_size = value;
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->internal_bit_size = value;
      return 1;
    }
  else
    return 0;
}


char harvest_bit_offset_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_base_type(tag))
    {
      ((base_type*)e->entry_ptr)->bit_offset = value;
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->internal_bit_offset = value;
      return 1;
    }
  else
    return 0;
}

#define SET_AND_CHECK(ptr, type, member, value)       \
  if (tag_is_type(tag))  \
    { \
      ((type*)ptr->entry_ptr)->member = value; \
    }

char harvest_const_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_enumerator(tag))
    {
      ((enumerator*)e->entry_ptr)->is_const = 1;
      ((enumerator*)e->entry_ptr)->const_value = value;
      return 1;
    } 
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->is_const = 1;
      ((variable*)e->entry_ptr)->const_value = value;
      return 1;
    } 
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->is_const = 1;
      ((member*)e->entry_ptr)->const_value = value;
      return 1;
    }
  else
    return 0;
}

static dwarf_entry* test;

// REMEMBER to use VG_(strdup) to make a COPY of the string
// or else you will run into SERIOUS memory corruption
// problems when readelf.c frees those strings from memory!!!
char harvest_name(dwarf_entry* e, const char* str1)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_enumerator(tag))
    {
      ((enumerator*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.1", str1);
      return 1;
    }
  else if (tag_is_collection_type(tag))
    {
      ((collection_type*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.2", str1);
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.3", str1);
      return 1;
    }
  else if (tag_is_function(tag))
    {
      ((function*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.4",str1);

      if(e->ID == 0x4ce) {
        test = e;
      }

      return 1;
    }
  else if (tag_is_formal_parameter(tag))
    {
      ((formal_parameter*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.5",str1);
      return 1;
    }
  else if (tag_is_compile_unit(tag))
    {
      ((compile_unit*)e->entry_ptr)->filename = VG_(strdup)("typedata.c: harv_name.6",str1);
      return 1;
    }
  else if (tag_is_typedef(tag))
    {
      ((typedef_type*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.7",str1);
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->name = VG_(strdup)("typedata.c: harv_name.8",str1);
      return 1;
    }
  else if (tag_is_namespace(tag))
    {
      ((namespace_type*)e->entry_ptr)->namespace_name = VG_(strdup)("typedata.c: harv_name.9", str1);
      return 1;
    }
  else
    return 0;
}

// REMEMBER to use VG_(strdup) to make a COPY of the string
// or else you will run into SERIOUS memory corruption
// problems when readelf.c frees those strings from memory!!!
char harvest_mangled_name(dwarf_entry* e, const char* str1)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag))
    {

      ((function*)e->entry_ptr)->mangled_name = VG_(strdup)("typedata.c: harv_mangled_name.1",str1);
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->mangled_name = VG_(strdup)("typedata.c: harv_mangled_name.2",str1);
      return 1;
    }
  else
    return 0;
}

char harvest_comp_dir(dwarf_entry* e, const char* str1)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_compile_unit(tag))
    {
      ((compile_unit*)e->entry_ptr)->comp_dir = VG_(strdup)("typedata.c: harv_comp_dir",str1);
      return 1;
    }
  else
    return 0;
}

char harvest_producer(dwarf_entry* e, const char* str1)
{
  unsigned long tag;
  char* producer;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_compile_unit(tag))
    {
      producer = VG_(strdup)("typedata.c: harv_producer", str1);
      FJALAR_DPRINTF("  Producer: %s\n", producer);

      if (VG_(strncmp) (producer, "clang ", 6) == 0) {
        clang_producer = True;
      } else {
        other_producer = True;
      }
      if (clang_producer && other_producer) {
        printf( "  Warning! Target program created with mixed clang and non-clang compilers.\n");
      }
      return 1;
    }
  else
    return 0;
}

char harvest_stmt_list(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_compile_unit(tag))
    {
      //printf("Harvest stmt list: %lx for %lx (%p)\n", value, e->ID, e->entry_ptr);
      ((compile_unit*)e->entry_ptr)->stmt_list = value;
      return 1;
    }
  else
    return 0;
}  

// The strange thing is that variable offsets should be NEGATIVE
// but DW_OP_fbreg and DW_OP_breg5 return unsigned values
char harvest_local_var_offset(dwarf_entry* e, unsigned long value, int regNum)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_variable(tag)) {
      ((variable*)e->entry_ptr)->offset = (int)value;
      ((variable*)e->entry_ptr)->regBase = regNum;
      return 1;
  } else
      return 0;
}

char harvest_formal_param_location_atom(dwarf_entry* e, enum dwarf_location_atom atom, long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_formal_parameter(tag))
    {
      formal_parameter *paramPtr = ((formal_parameter*)e->entry_ptr);
      paramPtr->loc_atom = atom;

      tl_assert(paramPtr->dwarf_stack_size < MAX_DWARF_OPS);
      paramPtr->dwarf_stack[paramPtr->dwarf_stack_size].atom = atom;
      paramPtr->dwarf_stack[paramPtr->dwarf_stack_size].atom_offset = value;
      paramPtr->dwarf_stack_size++;
      paramPtr->valid_loc = 1;

      return 1;
    }
  else
    return 0;
}

char harvest_formal_param_location_offset(dwarf_entry* e, long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_formal_parameter(tag))
    {
      ((formal_parameter*)e->entry_ptr)->location_type = LT_FP_OFFSET;
      ((formal_parameter*)e->entry_ptr)->location = value;
      ((formal_parameter*)e->entry_ptr)->valid_loc = 1;
      return 1;
    }
  else
    return 0;
}

char harvest_data_member_location(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->data_member_location = value;
      return 1;
    }
  if (tag_is_inheritance(tag))
    {
      ((inheritance_type*)e->entry_ptr)->member_var_offset = value;
      return 1;
    }
  else
    return 0;
}

char harvest_string(dwarf_entry* e, unsigned long attr, const char* str1)
{
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  if (attr == DW_AT_name)
    return harvest_name(e, str1);
  else if (attr == DW_AT_comp_dir)
    return harvest_comp_dir(e, str1);
  else if (attr == DW_AT_producer)
    return harvest_producer(e, str1);
  else if (attr == DW_AT_MIPS_linkage_name)
    return harvest_mangled_name(e, str1);
  else
    return 0;
}

char harvest_external_flag_value(dwarf_entry *e, unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag))
    {
      ((function*)e->entry_ptr)->is_external = value;
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->is_external = value;
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->is_external = value;
      return 1;
    }
  else
    return 0;
}

char harvest_address_value(dwarf_entry* e, unsigned long attr,
                           unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (attr == DW_AT_low_pc) {
      if(tag_is_function(tag)) {
          ((function*)e->entry_ptr)->start_pc = value;
          ((function*)e->entry_ptr)->comp_pc = comp_unit_base;
#if 0
          FJALAR_DPRINTF("Harvest: start_pc: %lx  comp_pc: %lx  name: %s %s\n",
                         ((function*)e->entry_ptr)->start_pc,
                         ((function*)e->entry_ptr)->comp_pc,
                         ((function*)e->entry_ptr)->name,
                         ((function*)e->entry_ptr)->mangled_name);
#endif
          return 1;
      } else if (tag_is_compile_unit(tag)) {
          comp_unit_base = value;
          return 1;
      }
    } else if (tag_is_function(tag) && attr == DW_AT_high_pc) {
        ((function*)e->entry_ptr)->end_pc = value;
        return 1;
    } else if (attr == DW_AT_const_value) {
        return harvest_const_value(e, value);
    }

  return 0;
}


char harvest_ordinary_unsigned_value(dwarf_entry* e, unsigned long attr, unsigned long value)
{
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  // Multiplex since
  // DW_AT_byte_size, DW_AT_encoding, DW_AT_const_value,
  // DW_AT_bit_size, DW_AT_bit_offset, DW_AT_external, DW_AT_upper_bound
  // DW_AT_declaration, DW_AT_artificial
  // return ordinary unsigned data
  switch(attr)
    {
    case DW_AT_byte_size:
      return harvest_byte_size_value(e, value);
    case DW_AT_encoding:
      return harvest_encoding_value(e, value);
    case DW_AT_const_value:
      return harvest_const_value(e, value);
    case DW_AT_bit_size:
      return harvest_bit_size_value(e, value);
    case DW_AT_bit_offset:
      return harvest_bit_offset_value(e, value);
    case DW_AT_external:
      return harvest_external_flag_value(e, value);
    case DW_AT_upper_bound:
      return harvest_upper_bound_value(e, value);
    case DW_AT_declaration:
      return harvest_declaration_value(e, value);
    case DW_AT_artificial:
      return harvest_artificial_value(e, value);
    default:
      return 0;
    }
}

/*
Requires: dwarf_entry_array initialized
Modifies:
Returns: success
Effects: Performs a binary search through dwarf_entry_array, looking for
         the entry with the matching ID field (target_ID).
         Stores the index of the matching entry in index_ptr
*/
char binary_search_dwarf_entry_array(unsigned long target_ID, unsigned long* index_ptr)
{
  unsigned long upper = dwarf_entry_array_size - 1;
  unsigned long lower = 0;

  //  FJALAR_DPRINTF("--target_ID: 0x%x, index_ptr: 0x%x, upper.ID: 0x%x, lower.ID: 0x%x\n",
         //         target_ID,
         //         index_ptr,
         //         dwarf_entry_array[upper].ID,
         //         dwarf_entry_array[lower].ID);

  // First do boundary sanity check to save ourselves lots of useless work:
  if ((target_ID > dwarf_entry_array[upper].ID) ||
      (target_ID < dwarf_entry_array[lower].ID))
    return 0;

  while (upper > lower)
    {
      unsigned long mid = (upper + lower) / 2;
      unsigned long cur_ID = dwarf_entry_array[mid].ID;

      //      FJALAR_DPRINTF("**lower: %d, mid: %d, upper: %d, target_ID: 0x%x, cur_ID: 0x%x\n",
      //             lower,
      //             mid,
      //             upper,
      //             target_ID,
      //             cur_ID);

      // Special case - (upper == (lower + 1)) - that means only 2 entries left to check:
      if (upper == (lower + 1))
        {
          if (target_ID == dwarf_entry_array[lower].ID)
            {
              *index_ptr = lower;
              return 1;
            }
          else if (target_ID == dwarf_entry_array[upper].ID)
            {
              *index_ptr = upper;
              return 1;
            }
          else
            {
              // YOU LOSE!  The target_ID is BETWEEN the lower and upper entries
              return 0;
            }
        }
      else if (target_ID == cur_ID) // Right on!
        {
          *index_ptr = mid;
          return 1;
        }
      else if (target_ID < cur_ID)
        {
          upper = mid;
        }
      else if (target_ID > cur_ID)
        {
          lower = mid;
        }
    }

  // Return 0 if no answer found
  return 0;
}

/*
Requires: dwarf_entry_array initialized
Modifies: certain fields within certain entries within dwarf_entry_array
          (modifier_type::target_ptr, function::return_type,
           member::type_ptr, formal_parameter::type_ptr,
           variable::type_ptr, array_type::type_ptr,
           typedef_type::target_type_ptr)
Returns:
Effects: Links every entry with a type_ID to the actual entry of that type
         within dwarf_entry_array.  Sets the appropriate type_ptr pointers to point
         to entries within dwarf_entry_array where that type resides
         (relevant for modifier_type, member, function, formal_parameter,
         variable, array_type, and typedef_type entries)
*/
static void link_entries_to_type_entries(void)
{
  unsigned long idx;
  dwarf_entry* cur_entry = 0;

  for (idx = 0; idx < dwarf_entry_array_size; idx++)
    {
      unsigned long tag;
      cur_entry = &dwarf_entry_array[idx];
      tag = cur_entry->tag_name;

      if (tag_is_array_type(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          array_type* array_ptr = (array_type*)(cur_entry->entry_ptr);
          unsigned long target_ID = array_ptr->type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              array_ptr->type_ptr=&dwarf_entry_array[target_index];
            }
        }

      if (tag_is_typedef(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          typedef_type* typedef_ptr = (typedef_type*)(cur_entry->entry_ptr);
          unsigned long target_ID = typedef_ptr->target_type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              typedef_ptr->target_type_ptr=&dwarf_entry_array[target_index];
            }
        }

      if (tag_is_variable(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          variable* variable_ptr = (variable*)(cur_entry->entry_ptr);
          unsigned long target_ID = variable_ptr->type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              variable_ptr->type_ptr=&dwarf_entry_array[target_index];
            }

        }
      if (tag_is_modifier_type(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          modifier_type* modifier_ptr = (modifier_type*)(cur_entry->entry_ptr);
          dwarf_entry* cur_target = NULL;
          unsigned long target_ID = modifier_ptr->target_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          FJALAR_DPRINTF("Searching for all modifiers of %lud\n", cur_entry->ID);
          if (success)
            {
              cur_target = &dwarf_entry_array[target_index];
              modifier_ptr->target_ptr= cur_target;
            }


          /* while (tag_is_modifier_type(cur_target->tag_name)) { */
          /*   modifier_type* cur_modifier = (modifier_type*)(cur_target->entry_ptr);             */
          /*   if(cur_modifier->target_ID) { */
          /*     success = binary_search_dwarf_entry_array(cur_modifier->target_ID, &target_index); */
          /*     if(success) { */
          /*         cur_target = &dwarf_entry_array[target_index]; */
          /*         modifier_ptr->target_ptr= cur_target;                 */
          /*         print_dwarf_entry(cur_target, 0); */
          /*     } */
          /*   } */
          /* } */
        }
      else if (tag_is_function(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          function* function_ptr = (function*)(cur_entry->entry_ptr);
          unsigned long target_ID = function_ptr->return_type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              function_ptr->return_type=&dwarf_entry_array[target_index];
            }
        }
      else if (tag_is_function_type(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          function_type *function_ptr
            = (function_type *)(cur_entry->entry_ptr);
          unsigned long target_ID = function_ptr->return_type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              function_ptr->return_type=&dwarf_entry_array[target_index];
            }
        }
      else if (tag_is_member(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          member* member_ptr = (member*)(cur_entry->entry_ptr);
          unsigned long target_ID = member_ptr->type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              member_ptr->type_ptr=&dwarf_entry_array[target_index];
            }
        }
      else if (tag_is_formal_parameter(tag))
        {
          char success = 0;
          unsigned long target_index = 0;
          formal_parameter* formal_param_ptr = (formal_parameter*)(cur_entry->entry_ptr);
          unsigned long target_ID = formal_param_ptr->type_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              formal_param_ptr->type_ptr=&dwarf_entry_array[target_index];
            }
        }
    }
}


// C++ code produces some fun debugging information!  The basic idea
// is that we want to have the start_pc and end_pc fields of function
// entries initialized to proper values.  There can be up to 2 levels
// of indirection here.  In one case there is an entry with DW_AT_abstract_origin
// that contains the start_pc and end_pc.  That entry points to an
// entry with no name but with a DW_AT_specification, which points to
// an entry with a name.  In the other case, there is an entry with
// DW_AT_specification that contains the start_pc and end_pc.  Here too,
// the specification points to an entry with the name.
// As far as I can tell, the 'real' entry is the one with the start_pc
// and end_pc.  We want to use the entries pointed to by DW_AT_abstract_origin
// and/or DW_AT_specification to locate the name and copy it into
// the 'real' entry.
/*

This entry is the 'real' one; we need to get the name from the abstract_origin
pointer to the specification pointer to the name:

 <1><180a1>: Abbrev Number: 136 (DW_TAG_subprogram)
     DW_AT_sibling     : <180d1>
     DW_AT_abstract_origin: <18069>
     DW_AT_low_pc      : 0x8048c16
     DW_AT_high_pc     : 0x8048c5d
     DW_AT_frame_base  : 1 byte block: 55         (DW_OP_reg5)

This is a place holder entry to locate the specification entry:

 <1><18069>: Abbrev Number: 132 (DW_TAG_subprogram)
     DW_AT_sibling     : <1809c>
     DW_AT_specification: <17e25>
     DW_AT_inline      : 2        (declared as inline but ignored)

Notice that this has is_declaration == 1 so it is a 'fake'
entry, but we really want to copy its name fields:

 <2><17e25>: Abbrev Number: 56 (DW_TAG_subprogram)
     DW_AT_sibling     : <17e51>
     DW_AT_external    : 1
     DW_AT_name        : push
     DW_AT_decl_file   : 53
     DW_AT_decl_line   : 27
     DW_AT_MIPS_linkage_name: _ZN5Stack4pushEPc
     DW_AT_declaration : 1
*/

// In some cases, we only have 1 level of indirection so we don't have
// to do as much work:
/*

This is the one we want to keep, and it already has start_pc and
end_pc ... how convenient!

 <1><2fb87>: Abbrev Number: 129 (DW_TAG_subprogram)
     DW_AT_sibling     : <2fbce>
     DW_AT_specification: <18698>
     DW_AT_decl_file   : 1
     DW_AT_decl_line   : 47
     DW_AT_low_pc      : 0x8048d2e
     DW_AT_high_pc     : 0x8048d75
     DW_AT_frame_base  : 1 byte block: 55         (DW_OP_reg5)

Notice that this has is_declaration == 1 so it is a 'fake'
entry, but we really want to copy its name fields

 <2><18698>: Abbrev Number: 12 (DW_TAG_subprogram)
     DW_AT_sibling     : <186c4>
     DW_AT_external    : 1
     DW_AT_name        : push
     DW_AT_decl_file   : 2
     DW_AT_decl_line   : 14
     DW_AT_MIPS_linkage_name: _ZN5Stack4pushEPc
     DW_AT_declaration : 1
*/

/*

There are a couple of cases to consider for variables as well.  If a variable
declared in a namespace is defined outside the body of the namespace declaration,
that variable has a DW_AT_specification attribute whose value is a reference to
the debugging information entry representing the declaration of the variable.
We need to copy the name property from the declaration to the definition.

 <2><5e6>: Abbrev Number: 35 (DW_TAG_variable)
    <5e7>   DW_AT_name        : (indirect string, offset: 0x575): __ioinit        
    <5eb>   DW_AT_decl_file   : 2
    <5ec>   DW_AT_decl_line   : 75
    <5ed>   DW_AT_type        : <0x51f>
    <5f1>   DW_AT_declaration : 1

 <1><1308>: Abbrev Number: 58 (DW_TAG_variable)
    <1309>   DW_AT_specification: <0x5e6>
    <130d>   DW_AT_location    : 9 byte block: 3 f4 e 60 0 0 0 0 0 (DW_OP_addr: 600ef4)

If the variable entry represents the defining declaration for a C++ static data
member of a struction, class or union (can also occur with template classes), the entry
has a DW_AT_specification attribute whose value is a reference to the debugging
information entry representing the declaration of this data member.  In this
case the referenced entry has the tag DW_TAG_member and will be the child of
some class, structure or union.  We need to copy both the name property and
the type property from the declaration to the definition.

 <3><dfd>: Abbrev Number: 43 (DW_TAG_member)
    <dfe>   DW_AT_name        : (indirect string, offset: 0x28): __min
    <e02>   DW_AT_decl_file   : 16
    <e03>   DW_AT_decl_line   : 58
    <e04>   DW_AT_type        : <0x134>
    <e08>   DW_AT_external    : 1
    <e09>   DW_AT_declaration : 1

 <1><1317>: Abbrev Number: 59 (DW_TAG_variable)
    <1318>   DW_AT_specification: <0xdfd>
    <131c>   DW_AT_MIPS_linkage_name: _ZN9__gnu_cxx24__numeric_traits_integerIiE5__minE
    <1320>   DW_AT_const_value : -2147483648
*/

// We use two passes to copy information to where it is needed.
// First, we copy the interesting fields from the entry pointed
// to by DW_AT_specification into the entry containing the
// DW_AT_specification.  Note that we do not overwrite properties
// that are already present.
// Next, we do a similar pass that copies the interesting fields
// from the entry pointed to by DW_AT_abstract_origin into the entry
// containing the DW_AT_abstract_origin.  Again, note that we do not
// overwrite properties that are already present.
void init_specification_and_abstract_stuff(void) {
  process_specification_items();
  process_abstract_origin_items();
}

void process_abstract_origin_items(void) {
  unsigned long idx;
  dwarf_entry* cur_entry = 0;

  for (idx = 0; idx < dwarf_entry_array_size; idx++) {
    cur_entry = &dwarf_entry_array[idx];
    if (tag_is_function(cur_entry->tag_name)) {
      function* cur_func = (function*)(cur_entry->entry_ptr);

      // Look for all functions with a abstract_origin_ID field, find the targets,
      // and copy over the name field(s), return type and accessibility.
      if (cur_func->abstract_origin_ID) {
        unsigned long aliased_index = 0;

        if (binary_search_dwarf_entry_array(cur_func->abstract_origin_ID,
                                            &aliased_index)) {
          dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
          function* aliased_func_ptr = 0;

          tl_assert(tag_is_function(aliased_entry->tag_name));
          aliased_func_ptr = (function*)(aliased_entry->entry_ptr);

          // We better have start_pc and end_pc fields!
          if (cur_func->start_pc && cur_func->end_pc) {
            /* The code used to assert that cur_func->{start,end}_pc
               were non-null here, but in some unusual situations
               (e.g., statically linked libc) the assertion failed, so
               let's just keep going. -SMcC */

            if (!cur_func->name)
              cur_func->name = aliased_func_ptr->name;
            if (!cur_func->mangled_name)
              cur_func->mangled_name = aliased_func_ptr->mangled_name;
            if (!cur_func->return_type_ID)
              cur_func->return_type_ID = aliased_func_ptr->return_type_ID;
            if (!cur_func->accessibility)
              cur_func->accessibility = aliased_func_ptr->accessibility;
          }
        }
      }
    } else if(tag_is_formal_parameter(cur_entry->tag_name)) {
      formal_parameter* cur_param = (formal_parameter*) (cur_entry->entry_ptr);

      // Look for all formal parameters with a abstract_origin_ID field, find the targets,
      // and copy over the location field(s) and stack size.
      if (cur_param->abstract_origin_ID) {
        unsigned long aliased_index = 0;

        if (binary_search_dwarf_entry_array(cur_param->abstract_origin_ID,
                                            &aliased_index)) {
          dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
          formal_parameter* aliased_formal_param = NULL;

          tl_assert(tag_is_formal_parameter(aliased_entry->tag_name));
          aliased_formal_param = (formal_parameter*) (aliased_entry->entry_ptr);

          aliased_formal_param->location_type = cur_param->location_type;
          aliased_formal_param->loc_atom = cur_param->loc_atom;
          aliased_formal_param->valid_loc = cur_param->valid_loc;
          aliased_formal_param->dwarf_stack_size = cur_param->dwarf_stack_size;

          VG_(memcpy)(aliased_formal_param->dwarf_stack, cur_param->dwarf_stack,
                      sizeof(dwarf_location)*cur_param->dwarf_stack_size);

          cur_param->name = aliased_formal_param->name;
          cur_param->type_ID = aliased_formal_param->type_ID;
          //cur_param->type_ptr = aliased_formal_param->type_ptr;
        }
      }
    }
  }
}

void process_specification_items(void) {
  unsigned long idx;
  dwarf_entry* cur_entry = 0;

  // Now make a second pass looking for all functions with a
  // specification_ID field, find their targets, and copy over the
  // names:
  for (idx = 0; idx < dwarf_entry_array_size; idx++) {
    cur_entry = &dwarf_entry_array[idx];
    if (tag_is_function(cur_entry->tag_name)) {
      function* cur_func = (function*)(cur_entry->entry_ptr);

      // Look for all functions with a specification_ID field, find the targets,
      // and copy over the name field(s), return type and accessibility.
      if (cur_func->specification_ID) {
        unsigned long aliased_index = 0;
        FJALAR_DPRINTF("Trying to find %s's specification: %lx\n", cur_func->name, cur_func->specification_ID);

        if (binary_search_dwarf_entry_array(cur_func->specification_ID,
                                            &aliased_index)) {
          dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
          function* aliased_func_ptr = 0;

          tl_assert(tag_is_function(aliased_entry->tag_name));
          aliased_func_ptr = (function*)(aliased_entry->entry_ptr);

          FJALAR_DPRINTF("   Found %s\n", aliased_func_ptr->name);

          if (!cur_func->name)
            cur_func->name = aliased_func_ptr->name;
          if (!cur_func->mangled_name)
            cur_func->mangled_name = aliased_func_ptr->mangled_name;
          if (!cur_func->return_type_ID)
            cur_func->return_type_ID = aliased_func_ptr->return_type_ID;
          if (!cur_func->accessibility)
            cur_func->accessibility = aliased_func_ptr->accessibility;
        }
      }
    } else if (tag_is_collection_type(cur_entry->tag_name)) {
      collection_type* cur_coll = (collection_type*)(cur_entry->entry_ptr);

      if (cur_coll->specification_ID) {
        unsigned long aliased_index = 0;
        FJALAR_DPRINTF("Trying to find %s's specification: %lx\n", cur_coll->name, cur_coll->specification_ID);

        if (binary_search_dwarf_entry_array(cur_coll->specification_ID,
                                            &aliased_index)) {
          dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
          collection_type* aliased_coll_ptr = NULL;

          tl_assert(tag_is_collection_type(aliased_entry->tag_name));

          aliased_coll_ptr = (collection_type*)(aliased_entry->entry_ptr);

          FJALAR_DPRINTF("   Found %s\n", aliased_coll_ptr->name);

          FJALAR_DPRINTF("Linking %p and %p\n", aliased_coll_ptr, cur_coll);


          cur_coll->name = aliased_coll_ptr->name;

          aliased_coll_ptr->byte_size = cur_coll->byte_size;
          aliased_coll_ptr->num_member_vars = cur_coll->num_member_vars;
          aliased_coll_ptr->num_static_member_vars = cur_coll->num_static_member_vars;
          aliased_coll_ptr->member_vars = cur_coll->member_vars;
          aliased_coll_ptr->member_funcs = cur_coll->member_funcs;
          aliased_coll_ptr->static_member_vars = cur_coll->static_member_vars;
          aliased_coll_ptr->superclasses = cur_coll->superclasses;
        }
      }

    } else if(tag_is_variable(cur_entry->tag_name)) {

      // This is kind of bad. Usually Fjalar discards all declarations
      // as they're just 'shells' of variables with no interesting 
      // features. Unfortunately, in the case of variables declared
      // const in C++, all we get is the specification entry (which Fjalar ignores) 
      // and the declaration. So we need to propagate information from the
      // declaration entry to the definition entry.
      // This is definitely just a heuristic and we need to be careful that
      // this doesn't let unwanted variables through (i.e. unused stuff from the 
      // standard libraries)

      unsigned long aliased_index = 0;
      variable* cur_var = (variable*)(cur_entry->entry_ptr);

      if(cur_var->is_declaration_or_artificial) {
        continue;
      }

      if (binary_search_dwarf_entry_array(cur_var->specification_ID, &aliased_index)) {
        dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];

        FJALAR_DPRINTF("[init_specification_and_abstract_stuff] Linking %lx and %lx\n", 
                       aliased_entry->ID,
                       cur_entry->ID);

        // g++ Can have variable's whose specification ID points to
        // a member dwarf entry. We really need to consolidate some
        // of these dwarf entry structs, this is kind of a pain..

        tl_assert(tag_is_variable(aliased_entry->tag_name) ||
                  tag_is_member(aliased_entry->tag_name));

        if (tag_is_variable(aliased_entry->tag_name)) {
            if(!cur_var->name) {
                cur_var->name = ((variable*)(aliased_entry->entry_ptr))->name;
            }
            // see if it needs a type
            if(!cur_var->type_ID) {
                cur_var->type_ID = ((variable*)(aliased_entry->entry_ptr))->type_ID;
            }
            continue;
        }

        // alias entry must be a member
        // see if it needs a name
        if(!cur_var->name) {
            // This is non-null only if we find a valid demangled name
            char* demangled_name = 0;

            if(cur_var->mangled_name) {
                // If there is a C++ mangled name, then call Valgrind core to try to
                // demangle the name (remember the demangled name is malloc'ed)
                demangled_name = cplus_demangle_v3(cur_var->mangled_name, DMGL_PARAMS | DMGL_ANSI);

                // if we got a good demangled name, lets see if we can simplfy it a bit
                // by removing the "__gnu_cxx::" prefix that shows up alot.
                if (demangled_name) {
                    int offset = 0;
                    if (VG_(strncmp) (demangled_name, "__gnu_cxx::", 11) == 0) {
                        offset = 11;
                    }
                    demangled_name = VG_(strdup) ("typedata.c: init_specification...", demangled_name + offset);
                }    
            }    

            if (demangled_name) {
                cur_var->name = demangled_name;
                // Since we process both the variable and the aliased member,
                // better copy revised name back to member var.  (markro)
                ((member*)(aliased_entry->entry_ptr))->name = demangled_name; 
            } else {
                cur_var->name = ((member*)(aliased_entry->entry_ptr))->name;
            }
        }

        // see if it needs a type
        if(!cur_var->type_ID) {
          cur_var->type_ID = ((member*)(aliased_entry->entry_ptr))->type_ID;
        }
      }
    }
  }
}

/*
Requires: dist_to_end indicates distance from e until end of dwarf_entry_array,
          e points to an element of dwarf_entry_array
Modifies: e->num_members, e->members
Returns:
Effects: Links the array entry to its subrange members, making sure not to
         accidentally segfault by indexing out of bounds
         (indicated by dist_to_end param
          which indicates distance until the end of the array)
*/
void link_array_type_to_members(dwarf_entry* e, unsigned long dist_to_end)
{
  unsigned long member_count = 0;
  dwarf_entry* cur_entry = e;
  unsigned long local_dist_to_end = dist_to_end;
  int array_entry_level = e->level;
  array_type* array_ptr = 0;

  // If you are at the end of the array, you're screwed anyways
  if(dist_to_end == 0 || !tag_is_array_type(e->tag_name))
    return;

  array_ptr = (array_type*)(e->entry_ptr);

  // arrays expect DW_TAG_subrange_type as members
  cur_entry++; // Move to the next entry - safe since dist_to_end > 0 by this point

  // Make one pass from the array entry all the way to
  // to get the numbers of params and local vars
  // Iteration conditions:
  // 1. Make sure we don't walk off the end of dwarf_entry_array (local_dist_to_end)
  // 2. Make sure that all the entries are at least 1 level above the array entry's level
  //    so that we are not traversing its siblings
  // 3. OPTIONAL: (We don't use this right now)
  //              (sibling_entry_ID ? (cur_entry->ID < sibling_entry_ID) : 1)
  //    If a sibling ID exists for the array entry, then don't overstep this
  //    (we don't use this condition because some array entries don't
  //     have siblings - ie. they are at the end of a compile unit - so this
  //     led to some bugs)
  while ((local_dist_to_end > 0) &&
         (cur_entry->level > array_entry_level)) {

    if ((cur_entry->level == (array_entry_level + 1)) &&
        (DW_TAG_subrange_type == cur_entry->tag_name)) {
        member_count++;
    }

    cur_entry++; // Move to the next entry in dwarf_entry_array
    local_dist_to_end--;
  }

  array_ptr->num_subrange_entries = member_count;

  // Make a second pass
  // to actually populate the newly-created array with entries
  if (member_count > 0) {
    int member_index = 0;
    array_ptr->subrange_entries = (dwarf_entry**)VG_(calloc)("typedata.c: link_array_type_to_members", member_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > array_entry_level)) {

      if ((cur_entry->level == (array_entry_level + 1)) &&
          (DW_TAG_subrange_type == cur_entry->tag_name)) {
        array_ptr->subrange_entries[member_index] = cur_entry;
        member_index++;
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }

}

// Same as above except linking collections (structs, classes, unions, enums)
// with their member variables (both static and instance), functions,
// and superclasses (if any)
// Precondition: In dwarf_entry_array, all members and member functions
// are listed after the collection's entry with its "level" as 1
// greater than the "level" of the collection's dwarf_entry 'e',
// 'e' if of type {collection}
// Postcondition: num_member_vars, member_vars, num_member_funcs, member_funcs
// num_static_member_vars, static_member_vars, num_superclasses, superclasses
// are all properly initialized
void link_collection_to_members(dwarf_entry* e, unsigned long dist_to_end)
{
  unsigned short member_var_count = 0;
  unsigned short static_member_var_count = 0;
  unsigned short member_func_count = 0;
  unsigned short superclass_count = 0;

  int collection_entry_level = e->level;
  int local_dist_to_end = dist_to_end;

  dwarf_entry* cur_entry = e;
  collection_type* collection_ptr = (collection_type*)(e->entry_ptr);

  // If it's not an enumeration type, then it's a struct/class/union type
  char isEnumType = (DW_TAG_enumeration_type == e->tag_name);

  // If you are at the end of the array, you're screwed anyways
  if(dist_to_end == 0)
    return;

  // First pick off the member variables, static variables, and functions

  cur_entry++; // Move to next entry - safe since dist_to_end > 0 

  // structs/classes/unions expect DW_TAG_member as member variables
  // enumerations expect DW_TAG_enumerator as member "variables"
  // structs/classes expect DW_TAG_variable as static member variables,
  // GCC 4.4.x+ denote static member variables via
  // DW_TAG_member + DW_AT_external
  // This has changed again. GCC 4.7.x (perhaps earlier?) now represents a 
  // static member variable with a DW_TAG_member at the declation and a 
  // DW_TAG_variable at the definition.  This entry has a DW_AT_specification
  // that points back to the DW_TAG_member.                        (markro)
  // DW_TAG_subprogram as member functions, and DW_TAG_inheritance as
  // superclass identifiers

  // Make one pass from the collection entry all the way to
  // to get the numbers of member variables
  // Iteration conditions:
  // 1. Make sure we don't walk off the end of dwarf_entry_array (local_dist_to_end)
  // 2. Make sure that all the entries are at least 1 level above the function entry's level
  //    so that we are not traversing its siblings
  while ((local_dist_to_end > 0) &&
         (cur_entry->level > collection_entry_level)) {

    if (tag_is_formal_parameter(cur_entry->tag_name)) {
      ((formal_parameter*)(cur_entry->entry_ptr))->valid_loc = 1;
    }

    if (cur_entry->level == (collection_entry_level + 1)) {
      if (isEnumType) {
        if (tag_is_enumerator(cur_entry->tag_name)) {
          member_var_count++;
        }
      }
      else {
        if (tag_is_member(cur_entry->tag_name)) {
          if(((member*)cur_entry->entry_ptr)->is_external) {
            static_member_var_count++;
          } else {
            member_var_count++;
          }
        }
        else if (tag_is_variable(cur_entry->tag_name)) {
          static_member_var_count++;
        }
        else if (tag_is_function(cur_entry->tag_name)) {

          member_func_count++;
          // Set the is_member_func flag here:
          ((function*)(cur_entry->entry_ptr))->is_member_func = 1;
        }
        else if (tag_is_inheritance(cur_entry->tag_name)) {
          superclass_count++;
        }
      }
    }

    cur_entry++; // Move to the next entry in dwarf_entry_array
    local_dist_to_end--;
  }


  collection_ptr->num_member_vars = member_var_count;
  collection_ptr->num_static_member_vars = static_member_var_count;
  collection_ptr->num_member_funcs = member_func_count;
  collection_ptr->num_superclasses = superclass_count;

  // Make a second pass (actually four second passes)
  // to actually populate the newly-created arrays with entries
  if (member_var_count > 0) {
    int member_var_index = 0;
    collection_ptr->member_vars = (dwarf_entry**)VG_(calloc)("typedata.c: link_collection_to_members",
                                                              member_var_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > collection_entry_level)) {
      if (cur_entry->level == (collection_entry_level + 1)) {
        if (isEnumType) {
          if (tag_is_enumerator(cur_entry->tag_name)) {
            collection_ptr->member_vars[member_var_index] = cur_entry;
            member_var_index++;
          }
        }
        else {
          if (tag_is_member(cur_entry->tag_name) && !((member*)cur_entry->entry_ptr)->is_external) {
            collection_ptr->member_vars[member_var_index] = cur_entry;
            member_var_index++;
          }
        }
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }

  if (static_member_var_count > 0) {
    int static_member_var_index = 0;
    collection_ptr->static_member_vars =
      (dwarf_entry**)VG_(calloc)("typedata.c: link_collection_to_members.2", static_member_var_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > collection_entry_level)) {
      if (cur_entry->level == (collection_entry_level + 1)) {
        if (tag_is_variable(cur_entry->tag_name)) {
          collection_ptr->static_member_vars[static_member_var_index] = cur_entry;
          static_member_var_index++;
        } else if (tag_is_member(cur_entry->tag_name) && ((member*)cur_entry->entry_ptr)->is_external) {
            collection_ptr->static_member_vars[static_member_var_index] = cur_entry;
            static_member_var_index++;
        }
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }

  if (member_func_count > 0) {
    int member_func_index = 0;
    collection_ptr->member_funcs = (dwarf_entry**)VG_(calloc)("typedata.c: link_collection_to_members.3", member_func_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > collection_entry_level)) {
      if (cur_entry->level == (collection_entry_level + 1)) {
        if (tag_is_function(cur_entry->tag_name)) {
          collection_ptr->member_funcs[member_func_index] = cur_entry;
          member_func_index++;
        }
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }

  if (superclass_count > 0) {
    int superclass_index = 0;
    collection_ptr->superclasses = (dwarf_entry**)VG_(calloc)("typedata.c: link_collection_to_members.4", superclass_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > collection_entry_level)) {
      if (cur_entry->level == (collection_entry_level + 1)) {
        if (tag_is_inheritance(cur_entry->tag_name)) {
          collection_ptr->superclasses[superclass_index] = cur_entry;
          superclass_index++;
        }
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }
}

// Same as above except linking functions with formal parameters and local variables
// Precondition: In dwarf_entry_array, all formal parameter and local variable
//               entries are listed after the function entry with its "level" as
//               1 greater than the "level" of the function's dwarf_entry 'e',
//               'e' is of type {function}
// Postcondition: num_formal_params, params, num_local_vars, and local_vars
//                are properly initialized for the given dwarf_entry e which
//                is of type {function}
void link_function_to_params_and_local_vars(dwarf_entry* e, unsigned long dist_to_end)
{
  unsigned short param_count = 0;
  unsigned short var_count = 0;

  int function_entry_level = e->level;
  int local_dist_to_end = dist_to_end;
  //  unsigned long sibling_entry_ID = e->sibling_ID;

  dwarf_entry* cur_entry = e;
  function* function_ptr = (function*)(e->entry_ptr);

  // If you are at the end of the array, you're screwed anyways
  if(dist_to_end == 0)
    return;

  // First pick off the formal parameters ...

  cur_entry++; // Move to the next entry - safe since dist_to_end > 0 by this point
  // functions expect DW_TAG_formal_parameter as parameters

  // Make one pass from the function entry all the way to
  // to get the numbers of params and local vars
  // Iteration conditions:
  // 1. Make sure we don't walk off the end of dwarf_entry_array (local_dist_to_end)
  // 2. Make sure that all the entries are at least 1 level above the function entry's level
  //    so that we are not traversing its siblings
  // 3. OPTIONAL: (We don't use this right now)
  //              (sibling_entry_ID ? (cur_entry->ID < sibling_entry_ID) : 1)
  //    If a sibling ID exists for the function entry, then don't overstep this
  //    (we don't use this condition because some function entries don't
  //     have siblings - ie. they are at the end of a compile unit - so this
  //     led to some bugs)
  while ((local_dist_to_end > 0) &&
         (cur_entry->level > function_entry_level)) {

    if (cur_entry->level == (function_entry_level + 1)) {
      if (tag_is_formal_parameter(cur_entry->tag_name)) {
        param_count++;
      }
      else if (tag_is_variable(cur_entry->tag_name)) {
        var_count++;
      }
    }

    cur_entry++; // Move to the next entry in dwarf_entry_array
    local_dist_to_end--;
  }

  function_ptr->num_formal_params = param_count;
  function_ptr->num_local_vars = var_count;

  // Make a second pass (actually two second passes)
  // to actually populate the newly-created arrays with entries
  if (param_count > 0) {
    int param_index = 0;
    function_ptr->params = (dwarf_entry**)VG_(calloc)("typedata.c: link_function_to_params_and_local_vars", param_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > function_entry_level)) {
      if (cur_entry->level == (function_entry_level + 1)) {
        if (tag_is_formal_parameter(cur_entry->tag_name)) {
          function_ptr->params[param_index] = cur_entry;
          param_index++;
        }
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }

  if (var_count > 0) {
    int var_index = 0;
    function_ptr->local_vars = (dwarf_entry**)VG_(calloc)("typedata.c: link_function_to_params_and_local_vars.2", var_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
           (cur_entry->level > function_entry_level)) {
      if (cur_entry->level == (function_entry_level + 1)) {
        if (tag_is_variable(cur_entry->tag_name)) {
          function_ptr->local_vars[var_index] = cur_entry;
          var_index++;
        }
      }

      cur_entry++; // Move to the next entry in dwarf_entry_array
      local_dist_to_end--;
    }
  }

}

/*
Requires: dwarf_entry_array is initialized
Modifies: ((function*)cur_entry->entry_ptr)->filename for function entries
Returns:
Effects: Initialize the filename field of each function entry
         by linearly traversing dwarf_entry_array and noting that every compile_unit
         entry describes a file and all functions to the right of that entry
         (but to the left of the next entry) belong to that file
         e.g. [compile_unit foo.c][...][func1][...][func2][...][compile_unit bar.c][func3]
         func1 and func2 belong to foo.c and func3 belongs to bar.c
*/
static void initialize_function_filenames(void)
{
  unsigned long idx;
  char* cur_file = 0;
  dwarf_entry* cur_entry = 0;

  for (idx = 0; idx < dwarf_entry_array_size; idx++)
    {
      cur_entry = &dwarf_entry_array[idx];

      if (tag_is_compile_unit(cur_entry->tag_name))
        cur_file = ((compile_unit*)cur_entry->entry_ptr)->filename;
      else if (tag_is_function(cur_entry->tag_name))
        ((function*)cur_entry->entry_ptr)->filename = cur_file;
    }
}

/*
Requires: dwarf_entry_array is initialized
Modifies: function, collection, and array entries within dwarf_entry_array
Returns:
Effects: Links function, collections, and array entries to their respective members
         e.g. functions need to have a list of their formal parameters
         while structs, unions, and enumeration types need to have lists of members
         and arrays need to have a list of array_subrange_type entries
*/
static void link_array_entries_to_members(void)
{
  unsigned long idx;
  dwarf_entry* cur_entry = 0;

  // Linearly traverse the array and pick off function or collections
  // (struct, union, enumeration) entries to link to members:
  for (idx = 0; idx < dwarf_entry_array_size; idx++)
    {
      cur_entry = &dwarf_entry_array[idx];

      if (tag_is_collection_type(cur_entry->tag_name))
      {
        // Also, if the collection is named through a typedef,
        // the typedef name takes precedence over any original names
        // it may have so we will use the typedef name:
        collection_type* collectionPtr = (collection_type*)cur_entry->entry_ptr;

        if (!collectionPtr->name)
        {
            // Now we can reap the benefits of the typedef names
            // optimization by simply doing a hashtable look-up to
            // find out the name of the typedef entry whose
            // target_type_ID field matches the ID of cur_entry:
            collectionPtr->name = (char*)
              gengettable(typedef_names_map,
                          (void*)cur_entry->ID);
        }
        link_collection_to_members(cur_entry, dwarf_entry_array_size - idx - 1);
      }

      if (tag_is_array_type(cur_entry->tag_name))
        link_array_type_to_members(cur_entry, dwarf_entry_array_size - idx - 1);
      else if (tag_is_function(cur_entry->tag_name))
        link_function_to_params_and_local_vars(cur_entry, dwarf_entry_array_size - idx - 1);

      // Link C++ static member variables (as well as global variables produced in gcc 4.0)
      // Copy all the information into the version of the variable "declaration" one
      // which is INSIDE the appropriate class/struct DWARF entry
      else if (tag_is_variable(cur_entry->tag_name)) {
        variable* variablePtr = (variable*)cur_entry->entry_ptr;
        if (variablePtr->specification_ID && variablePtr->globalVarAddr) {
          unsigned long aliased_index= 0;
          if (binary_search_dwarf_entry_array(variablePtr->specification_ID, &aliased_index)) {
            dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
            if (tag_is_variable(aliased_entry->tag_name)) {
              variable* aliased_var_ptr = (variable*)(aliased_entry->entry_ptr);
              aliased_var_ptr->globalVarAddr = variablePtr->globalVarAddr;
              aliased_var_ptr->is_declaration_or_artificial = 0;

              // We distinguish between true global variables and C++
              // static member variables by whether there is a
              // non-null mangled_name.  This is just a heuristic, but
              // it seems to work in practice.  Static member
              // variables have mangled names, but global variables
              // don't:
              if (aliased_var_ptr->mangled_name) {
                aliased_var_ptr->couldBeGlobalVar = 0;
                aliased_var_ptr->isStaticMemberVar = 1;
              } else {
                aliased_var_ptr->couldBeGlobalVar = 1;
                aliased_var_ptr->isStaticMemberVar = 0;
              }
              
              /* FJALAR_DPRINTF("mangled_name: %s - ID: %x - globalVarAddr: 0x%x\n", */
              /*             aliased_var_ptr->mangled_name, */
              /*             aliased_entry->ID, */
              /*             aliased_var_ptr->globalVarAddr); */
            }
            else
            // In newer versions of gcc (at least 4.7.x, maybe sooner), static member
            // variables are indicated by the definition TAG_variable pointing back to
            // the declaration which is a TAG_member.
            // Our primary source of information is the variable entry.  (markro)
            if (tag_is_member(aliased_entry->tag_name)) {
                variablePtr->couldBeGlobalVar = 1;
                variablePtr->isStaticMemberVar = 1;
            }
          }
        }
      } else if (tag_is_collection_type(cur_entry->tag_name)) {
        collection_type* variablePtr = (collection_type*)cur_entry->entry_ptr;
        if (variablePtr->specification_ID) {
          unsigned long aliased_index= 0;
          if (binary_search_dwarf_entry_array(variablePtr->specification_ID, &aliased_index)) {
            dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
            if (tag_is_collection_type(aliased_entry->tag_name)) {

              // Let's get the name out of this specification
              collection_type* aliased_coll = (collection_type*)(aliased_entry->entry_ptr);
              variablePtr->name = aliased_coll->name;
            }
          }
        }
      }
    }
}

// Fills up typedef_names_map with key/value pairs by picking off
// the appropriate typedef_type entries in dwarf_entry_array.
// (This only has to happen once.)
static void initialize_typedef_names_map(void) {
  unsigned long idx;
  //  unsigned int totalNumTypedefs = 0;
  dwarf_entry* cur_entry = 0;

  // Linearly traverse the array and pick off typedef entries
  // to throw into typedef_names_map
  for (idx = 0; idx < dwarf_entry_array_size; idx++) {
      cur_entry = &dwarf_entry_array[idx];

      if (tag_is_typedef(cur_entry->tag_name)) {
        typedef_type* typedef_ptr = (typedef_type*)(cur_entry->entry_ptr);

        genputtable(typedef_names_map,
                    // Key: target_type_ID
                    (void*)typedef_ptr->target_type_ID,
                    // Value: name
                    typedef_ptr->name);
      }
  }
}

void add_comp_unit(compile_unit* unit) {
  comp_unit_info[comp_unit_info_idx++] = unit;
}

// Prints the contents of the entry depending on its type
void print_dwarf_entry(dwarf_entry* e, char simplified)
{
  if (e == 0)
    {
      FJALAR_DPRINTF("ERROR! Pointer e is null in print_dwarf_entry\n");
      return;
    }

  FJALAR_DPRINTF("ID:0x%lx, LVL:%d, SIB_ID:0x%lx, TAG:%s \n", e->ID, e->level, e->sibling_ID, get_TAG_name(e->tag_name));

  switch(e->tag_name)
    {
    case DW_TAG_subprogram:
      {
        function* function_ptr = (function*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, Filename: %s, Ret. ID: 0x%lx, is_ext: %d, spec_ID: 0x%lx, low_pc: 0x%lx\n",
               function_ptr->name,
               function_ptr->filename,
               function_ptr->return_type_ID,
               function_ptr->is_external,
               function_ptr->specification_ID,
               function_ptr->start_pc);
        break;
      }
    case DW_TAG_formal_parameter:
      {
        formal_parameter* formal_param_ptr = (formal_parameter*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, Type ID: 0x%lx, Location: %ld\n",
               formal_param_ptr->name,
               formal_param_ptr->type_ID,
               formal_param_ptr->location);
        break;
      }
    case DW_TAG_member:
      {
        member* member_ptr = (member*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, Type ID: 0x%x, Data member location: %u,\n"
                       "  Byte size: %u, access: %u, external: %u, is_const: %u, value: 0x%lx\n",
               member_ptr->name,
               (UInt)member_ptr->type_ID,
               (UInt)member_ptr->data_member_location,
               (UInt)member_ptr->internal_byte_size,
               (UInt)member_ptr->accessibility,
               (UInt)member_ptr->is_external,
               (UInt)member_ptr->is_const,
               (long unsigned int)member_ptr->const_value);
        break;
      }
    case DW_TAG_enumerator:
      {
        enumerator* enumerator_ptr = (enumerator*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, Const value: %ld\n",
               enumerator_ptr->name,
               enumerator_ptr->const_value);
        break;
      }

    case DW_TAG_structure_type:
    case DW_TAG_class_type:
    case DW_TAG_union_type:
    case DW_TAG_enumeration_type:
      {
        collection_type* collection_ptr = (collection_type*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, is_decl: %u, byte size: %lu, Num. members: %d %d %d %d\n",
                       collection_ptr->name,
                       (UInt)collection_ptr->is_declaration,
                       collection_ptr->byte_size,
                       collection_ptr->num_member_vars,
                       collection_ptr->num_member_funcs,
                       collection_ptr->num_static_member_vars,
                       collection_ptr->num_superclasses);
        unsigned short i;
        for (i = 0; i < collection_ptr->num_static_member_vars; i++) {
            FJALAR_DPRINTF("    0x%lx\n", (collection_ptr->static_member_vars[i])->ID);
        }

        break;
      }

    case DW_TAG_base_type:
      {
        base_type* base_ptr = (base_type*)(e->entry_ptr);
        FJALAR_DPRINTF("  Byte size: %lu, Encoding: %lu ",
               base_ptr->byte_size,
               base_ptr->encoding);

        // More detailed encoding information
        switch (base_ptr->encoding)
          {
          case DW_ATE_void:          FJALAR_DPRINTF ("(void)"); break;
          case DW_ATE_address:       FJALAR_DPRINTF ("(machine address)"); break;
          case DW_ATE_boolean:       FJALAR_DPRINTF ("(boolean)"); break;
          case DW_ATE_complex_float: FJALAR_DPRINTF ("(complex float)"); break;
          case DW_ATE_float:         FJALAR_DPRINTF ("(float)"); break;
          case DW_ATE_signed:        FJALAR_DPRINTF ("(signed)"); break;
          case DW_ATE_signed_char:   FJALAR_DPRINTF ("(signed char)"); break;
          case DW_ATE_unsigned:      FJALAR_DPRINTF ("(unsigned)"); break;
          case DW_ATE_unsigned_char: FJALAR_DPRINTF ("(unsigned char)"); break;
            /* DWARF 2.1 value.  */
          case DW_ATE_imaginary_float: FJALAR_DPRINTF ("(imaginary float)"); break;
          default:
            if (base_ptr->encoding >= DW_ATE_lo_user
                && base_ptr->encoding <= DW_ATE_hi_user)
              {
                FJALAR_DPRINTF ("(user defined type)");
              }
            else
              {
                FJALAR_DPRINTF ("(unknown type)");
              }
            break;
          }

        FJALAR_DPRINTF(", Bit size: %lu, Bit offset: %lu\n",
               base_ptr->bit_size,
               base_ptr->bit_offset);

        break;
      }
    case DW_TAG_const_type:
    case DW_TAG_pointer_type:
    case DW_TAG_reference_type:
    case DW_TAG_volatile_type:
      {
        modifier_type* modifier_ptr = (modifier_type*)(e->entry_ptr);
        FJALAR_DPRINTF("  Target ID (addr): 0x%lx (0x%lx)\n",
               modifier_ptr->target_ID,
               ((simplified && modifier_ptr->target_ptr) ?
                (UInt)(ptrdiff_t)modifier_ptr->target_ptr - (UInt)(ptrdiff_t)dwarf_entry_array :
                (unsigned long)(modifier_ptr->target_ptr)));
        break;
      }
    case DW_TAG_array_type:
      {
        array_type* array_ptr = (array_type*)(e->entry_ptr);
        FJALAR_DPRINTF("  Type ID (addr): 0x%lx (0x%lx), Num. subrange entries: %lu\n",
               array_ptr->type_ID,
               ((simplified && array_ptr->type_ptr) ?
                ((UInt)(ptrdiff_t)array_ptr->type_ptr - (UInt)(ptrdiff_t)dwarf_entry_array) :
                (unsigned long)(array_ptr->type_ptr)),
               array_ptr->num_subrange_entries);
        break;
      }
    case DW_TAG_subrange_type:
      {
        array_subrange_type* array_subrange_ptr = (array_subrange_type*)(e->entry_ptr);
        FJALAR_DPRINTF("  Upper bound: %lu\n",
               array_subrange_ptr->upperBound);
        break;
      }
    case DW_TAG_typedef:
      {
        typedef_type* typedef_ptr = (typedef_type*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, Target type ID (addr): 0x%lx (0x%lx)\n",
               typedef_ptr->name,
               typedef_ptr->target_type_ID,
               ((simplified && typedef_ptr->target_type_ptr) ?
                ((UInt)(ptrdiff_t)typedef_ptr->target_type_ptr - (UInt)(ptrdiff_t)dwarf_entry_array) :
                (unsigned long)(typedef_ptr->target_type_ptr)));
        break;
      }
    case DW_TAG_variable:
      {
        variable* variable_ptr = (variable*)(e->entry_ptr);
        FJALAR_DPRINTF("  Name: %s, Type ID: 0x%lx, is_ext: %d,\n"
                       "  cbGlobal: %d, is_static: %d, spec_ID: 0x%lx, globalVarAddr: 0x%lx,\n"
                       "  offset: %d, access: %lu, is_const: %d, const_value: 0x%lx\n",
               variable_ptr->name,
               variable_ptr->type_ID,
               variable_ptr->is_external,
               variable_ptr->couldBeGlobalVar,
               variable_ptr->isStaticMemberVar,
               variable_ptr->specification_ID,
               variable_ptr->globalVarAddr,
               variable_ptr->offset,
               variable_ptr->accessibility,
               variable_ptr->is_const,
               (long unsigned int) variable_ptr->const_value);
        break;
      }
    case DW_TAG_compile_unit:
      {
        compile_unit* compile_ptr = (compile_unit*)(e->entry_ptr);
        FJALAR_DPRINTF("  Filename: %s, Compile dir: %s\n",
               compile_ptr->filename,
               compile_ptr->comp_dir);
        break;
      }

    case DW_TAG_subroutine_type:
      {
        FJALAR_DPRINTF(  "DW_TAG_subroutine_type not yet supported\n");
        // (comment added 2005)  
        // TODO: Don't print anything out for this yet - it's still
        //       uninitialized
        //        function_type * func_type = (function_type *)(e->entry_ptr);
        //        FJALAR_DPRINTF("  Return type ID (addr): 0x%lx (%p)\n",
        //               func_type->return_type_ID,
        //               ((simplified && func_type->return_type) ?
        //                func_type->return_type - dwarf_entry_array :
        //                func_type->return_type));
        break;
      }

    default:
      return;
    }
}

/*
Requires:
Modifies: dwarf_entry_array (initializes and blanks all entries to zero)
Returns:
Effects: Initializes sets up dwarf_entry_array to hold num_entries components
*/
void initialize_dwarf_entry_array(unsigned long num_entries)
{
  // use calloc to blank everything upon initialization
  dwarf_entry_array = VG_(calloc)("typedata.c: initialize_dwarf_entry_array", num_entries, sizeof *dwarf_entry_array);

  // Also initialize typedef_names_map at this time
  typedef_names_map = genallocatehashtable(0,
                                           (int (*)(void *,void *)) &equivalentIDs);
}

/*
Requires:
Modifies: compile_unit_info (initialized and blanks all entries to zero)
Return:
Effects: Initializes and sets up an array of the dwarf entries for all compile units
*/
void initialize_compile_unit_array(unsigned long num_entries)
{
  comp_unit_info = VG_(calloc)("typedata.c: initialize_compile_unit_info", num_entries, sizeof *comp_unit_info);
} 


/*
Requires: dwarf_entry_array is initialized
Modifies: dwarf_entry_array (free and set to 0)
Returns:
Effects: Destroys dwarf_entry_array and all entry_ptr fields of all entries
*/
// (comment added 2005)  
// TODO: This doesn't free up all of the strings (char*) allocated
//       by strdup within all of the individual entries.
//       We need to implement "destructors" to free those strings.
//       Also, free() probably isn't smart enough to figure out exactly
//       how many bytes to free since dwarf_entry_array[i].entry_ptr is
//       of type void*.
void destroy_dwarf_entry_array()
{
  // Traverse the array and free the entry_ptr of all entries within array

  unsigned long i;
  for (i = 0; i < dwarf_entry_array_size; i++)
    {
      VG_(free)(dwarf_entry_array[i].entry_ptr);
    }

  // Free the array itself
  VG_(free)(dwarf_entry_array);

  dwarf_entry_array = 0;
  dwarf_entry_array_size = 0;
}

// Print without machine/runtime-specific address information
// in order to provide consistent results for diffs
// (Doesn't appear to be used - markro)
void simple_print_dwarf_entry_array()
{
  print_dwarf_entry_array_helper(1);
}

void print_dwarf_entry_array()
{
  print_dwarf_entry_array_helper(0);
}

void print_dwarf_entry_array_helper(char simplified)
{
  UInt i;
  FJALAR_DPRINTF("--- BEGIN DWARF ENTRY ARRAY - size: %lu\n", dwarf_entry_array_size);
  for (i = 0; i < dwarf_entry_array_size; i++)
    {

      FJALAR_DPRINTF("array[%u] (0x%x): ", i,
             (simplified ? i : ((UInt)(ptrdiff_t)dwarf_entry_array + (UInt)i)));
      print_dwarf_entry(&dwarf_entry_array[i], simplified);
    }
  FJALAR_DPRINTF("--- END DWARF ENTRY ARRAY\n");
}

/*
Requires: e is initialized and has a e->tag_name
Modifies: e->entry_ptr (initializes and set to 0)
Returns:
Effects: Initialize the value of e->entry_ptr to the appropriate sub-type
         based on the value of tag_name
         If tag_name is 0, then don't do anything
*/
void initialize_dwarf_entry_ptr(dwarf_entry* e)
{
  if (e->tag_name)
    {
      if (tag_is_base_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.1", 1, sizeof(base_type));
        }
      else if (tag_is_modifier_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.2", 1, sizeof(modifier_type));
        }
      else if (tag_is_collection_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.3", 1, sizeof(collection_type));
        }
      else if (tag_is_member(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.4", 1, sizeof(member));
        }
      else if (tag_is_enumerator(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.5", 1, sizeof(enumerator));
        }
      else if (tag_is_function(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.6", 1, sizeof(function));
        }
      else if (tag_is_formal_parameter(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.7", 1, sizeof(formal_parameter));
        }
      else if (tag_is_compile_unit(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.8", 1, sizeof(compile_unit));
        }
      else if (tag_is_function_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.9", 1, sizeof(function_type));
        }
      else if (tag_is_array_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.10", 1, sizeof(array_type));
        }
      else if (tag_is_array_subrange_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.11", 1, sizeof(array_subrange_type));
        }
      else if (tag_is_typedef(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.12", 1, sizeof(typedef_type));
        }
      else if (tag_is_variable(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.13", 1, sizeof(variable));
        }
      else if (tag_is_inheritance(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.14", 1, sizeof(inheritance_type));
        }
      else if (tag_is_namespace(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)("typedata.c: initialize_dwarf_entry_ptr.15", 1, sizeof(namespace_type));
        }
      else {
        tl_assert(0); // Error
      }
    }
}

/*
Requires: dwarf_entry_array is initialized
Modifies: dwarf_entry_array
Returns:
Effects: Links all of the entries within dwarf_entry_array
         with their respective members in a coherent manner
*/
void finish_dwarf_entry_array_init(void)
{
  // These must be done in this order or else things will go screwy!!!

  // typedef names optimization:
  initialize_typedef_names_map();


  link_array_entries_to_members();
  init_specification_and_abstract_stuff();
  initialize_function_filenames();
  link_entries_to_type_entries();
}

// Finds the first compile_unit entry to the LEFT of the given entry e
// and grab its filename:
char* findFilenameForEntry(dwarf_entry* e)
{
  int idx;
  dwarf_entry* cur_entry = 0;
  unsigned long entry_index;

  char success = binary_search_dwarf_entry_array(e->ID, &entry_index);

  if (!success)
    return 0;

  // Traverse backwards (to the LEFT) in dwarf_entry_array
  // until you hit the first compile_unit entry and return its filename
  for (idx = entry_index; idx >= 0; idx--)
    {
      cur_entry = &dwarf_entry_array[idx];

      if (tag_is_compile_unit(cur_entry->tag_name))
        return ((compile_unit*)cur_entry->entry_ptr)->filename;
    }
  return 0;
}

// Returns a struct entry that matches the following two criteria:
// 1. It's a collection_type
// 2. .is_declaration == 0
// 3. .name == name
dwarf_entry* find_struct_entry_with_name(char* name) {
  unsigned long idx;
  //  unsigned int totalNumTypedefs = 0;
  dwarf_entry* cur_entry = 0;

  for (idx = 0; idx < dwarf_entry_array_size; idx++) {
    cur_entry = &dwarf_entry_array[idx];

    if (tag_is_collection_type(cur_entry->tag_name)) {
      collection_type* collectionPtr = (collection_type*)cur_entry->entry_ptr;
      if (!(collectionPtr->is_declaration) &&
          VG_STREQ(collectionPtr->name, name)) {
        return cur_entry;
      }
    }
  }

  return 0;
}

// Finds the first namespace_type entry to the LEFT of the given entry
// e with a level lower than e's level and return it:
namespace_type* findNamespaceForVariableEntry(dwarf_entry* e) {
  int idx;
  dwarf_entry* cur_entry = 0;
  unsigned long entry_index;

  // (comment added 2005)  
  // TODO: We can avoid this and get entry_index directly if we assume
  // that 'e' is within dwarf_entry_array, which it should be:
  char success = binary_search_dwarf_entry_array(e->ID, &entry_index);

  if (!success)
    return 0;

  // Traverse backwards (to the LEFT) in dwarf_entry_array
  for (idx = entry_index; idx >= 0; idx--)
    {
      cur_entry = &dwarf_entry_array[idx];

      if(cur_entry->level < e->level) {
        if (tag_is_namespace(cur_entry->tag_name)) {
          return (namespace_type*)(cur_entry->entry_ptr);
        } else {
          return 0;
        }
      }
    }
  return 0;
}

// Finds the first function entry to the LEFT of the given entry e
// with a level lower than e's level and grabs its startPC
unsigned long findFunctionStartPCForVariableEntry(dwarf_entry* e)
{
  int idx;
  dwarf_entry* cur_entry = 0;
  unsigned long entry_index;

  // (comment added 2005)  
  // TODO: We can avoid this and get entry_index directly if we assume
  // that 'e' is within dwarf_entry_array, which it should be:
  char success = binary_search_dwarf_entry_array(e->ID, &entry_index);

  if (!success)
    return 0;

  // Traverse backwards (to the LEFT) in dwarf_entry_array
  for (idx = entry_index; idx >= 0; idx--)
    {
      cur_entry = &dwarf_entry_array[idx];

      if ((tag_is_function(cur_entry->tag_name)) &&
          (cur_entry->level < e->level)) {
        return ((function*)cur_entry->entry_ptr)->start_pc;
      }
    }
  return 0;
}

char harvest_frame_base(dwarf_entry *e, enum dwarf_location_atom a, long offset) {
  unsigned long tag;
  // FJALAR_DPRINTF("Attempting to harvest the frame_base\n");

  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;


  if (tag_is_function(tag))
    {
      ((function*)e->entry_ptr)->frame_base_offset = offset;
      ((function*)e->entry_ptr)->frame_base_expression = a;

      return 1;
    }
  return 0;
}

char harvest_debug_frame_entry(debug_frame *df){

  tl_assert(df);
  FJALAR_DPRINTF("Attaching debug_frame [%lx...%lx] to the debug_frame list\n", df->begin, df->end);

  if(!debug_frame_TAIL) {
    debug_frame_HEAD = df;
    debug_frame_TAIL = df;
    df->next = NULL;
  } else {
    debug_frame_TAIL->next = df;
    debug_frame_TAIL = df;
  }
  return 1;
}


char harvest_location_list_entry(location_list* ll, unsigned long offset){
  location_list *cur_loc = NULL;
  tl_assert(loc_list_map && "Location list map uninitialized");
  ll->next = NULL;

  FJALAR_DPRINTF("Adding the following location to the location list at offset: %lx\noffset\tbegin\tend\texpr\n%lx %lx %lx\t(%u + %llx)\n\n",
                 ll->offset, ll->offset, ll->begin, ll->end, ll->atom, (long long unsigned int) ll->atom_offset);

  if(gencontains(loc_list_map, (void *)offset)) {
    tl_assert((cur_loc = gengettable(loc_list_map, (void *)offset)));

    while(cur_loc->next != NULL) {
      cur_loc = cur_loc->next;
    }

    cur_loc->next = ll;

  } else {
    FJALAR_DPRINTF("\nCreating location list for offset %lx\n", offset);
    genputtable(loc_list_map, (void*)offset, ll);
    cur_loc = ll;
  }

  return 1;
}

// Initialize FunctionSymbolTable and VariableSymbolTable:
void initialize_typedata_structures() {

  loc_list_map = genallocatehashtable(0, (int (*)(void *,void *)) &equivalentIDs);

  FunctionSymbolTable = genallocatehashtable((unsigned int (*)(void *)) & hashString,
                                             (int (*)(void *,void *)) &equivalentStrings);
  ReverseFunctionSymbolTable = genallocatehashtable(0,
                                                    (int (*)(void *,void *)) &equivalentIDs);
  VariableSymbolTable = genallocatehashtable((unsigned int (*)(void *)) & hashString,
                                             (int (*)(void *,void *)) &equivalentStrings);

  next_line_addr =
    genallocatehashtable(0, (int (*)(void *,void *))&equivalentIDs);
}

Addr getFunctionStartAddr(char* name) {
  return (Addr)gengettable(FunctionSymbolTable, (void*)name);
}

// This queries ReverseFunctionSymbolTable:
// (Returns regular name for C and mangled name for C++)
char* getFunctionName(Addr startAddr) {
  return (char*)gengettable(ReverseFunctionSymbolTable, (void*)startAddr);
}

// This queries VariableSymbolTable:
// (Accepts regular name for C and mangled name for C++)
Addr getGlobalVarAddr(char* name) {
  return (Addr)gengettable(VariableSymbolTable, (void*)name);
}
