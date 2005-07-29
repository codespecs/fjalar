/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* typedata.c:
   This file contains functions that serve to complement readelf.c
   and arrange the DWARF2 debugging information in an orderly
   format within dwarf_entry_array
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "typedata.h"
#include "elf/dwarf2.h"

//#include "tool_asm.h" //#include "vg_constants_skin.h"
#include "tool.h"


// Forward declarations so that the compiler won't warn me:
//extern void  VG_(free)           ( void* p );
//extern void* VG_(calloc)         ( int n, int nbytes );

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
dwarf_entry* dwarf_entry_array = 0;

// The size of this array
unsigned long dwarf_entry_array_size = 0;


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
                     _array_type, _subrange_type, _typedef, _variable},
                     0 otherwise
Effects: Used to determine which entries to record into a dwarf_entry structure;
         All relevant entries should be included here
*/
char tag_is_relevant_entry(unsigned long tag)
{
  switch (tag)
    {
    case DW_TAG_enumeration_type:
    case DW_TAG_formal_parameter:
    case DW_TAG_member:
    case DW_TAG_pointer_type:
    case DW_TAG_reference_type:
    case DW_TAG_structure_type:
    case DW_TAG_union_type:
    case DW_TAG_base_type:
    case DW_TAG_const_type:
    case DW_TAG_enumerator:
    case DW_TAG_subprogram:
    case DW_TAG_volatile_type:
    case DW_TAG_compile_unit:
    case DW_TAG_subroutine_type:
    case DW_TAG_array_type:
    case DW_TAG_subrange_type:
    case DW_TAG_typedef:
    case DW_TAG_variable:
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
    case DW_TAG_pointer_type:
    case DW_TAG_reference_type:
    case DW_TAG_const_type:
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

/*------------------
 Attribute listeners
 ------------------*/

// Each type stored in dwarf_entry.entry_ptr listens for particular
// attributes.  e.g. collection_type listens for DW_AT_name and DW_AT_byte_size

// List of attributes and the types which listen for them:

// DW_AT_location: formal_parameter, variable
// DW_AT_data_member_location: member
// DW_AT_name: collection_type, member, enumerator, function, formal_parameter, compile_unit, variable, typedef
// DW_AT_byte_size: base_type, collection_type, member
// DW_AT_bit_offset: base_type, member
// DW_AT_bit_size: base_type, member
// DW_AT_const_value: enumerator
// DW_AT_type: modifier, member, function, formal_parameter, array_type, subrange_type, variable, typedef
// DW_AT_encoding: base_type
// DW_AT_comp_dir: compile_unit
// DW_AT_external: function, variable
// DW_AT_low_pc: function
// DW_AT_high_pc: function
// DW_AT_upper_bound: subrange_type
// DW_AT_sibling: collection_type, array_type, function_type, function, enumerator
// DW_AT_MIPS_linkage_name: function, variable
// DW_AT_specification: function, variable
// DW_AT_declaration: function, variable
// DW_AT_artificial: variable
// DW_AT_accessibility: function

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
      return tag_is_member(tag);
    case DW_AT_name:
      return (tag_is_collection_type(tag) ||
              tag_is_member(tag) ||
              tag_is_enumerator(tag) ||
              tag_is_function(tag) ||
              tag_is_formal_parameter(tag) ||
              tag_is_compile_unit(tag) ||
              tag_is_typedef(tag) ||
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
      return tag_is_enumerator(tag);
    case DW_AT_type:
      return (tag_is_modifier_type(tag) ||
              tag_is_member(tag) ||
              tag_is_function(tag) ||
              tag_is_formal_parameter(tag) ||
              tag_is_function_type(tag) ||
              tag_is_array_type(tag) ||
              tag_is_typedef(tag) ||
              tag_is_variable(tag));
    case DW_AT_encoding:
      return tag_is_base_type(tag);
    case DW_AT_comp_dir:
      return tag_is_compile_unit(tag);
    case DW_AT_external:
      return (tag_is_function(tag) ||
	      tag_is_variable(tag));
    case DW_AT_low_pc:
    case DW_AT_high_pc:
      return tag_is_function(tag);
    case DW_AT_upper_bound:
      return tag_is_array_subrange_type(tag);
    case DW_AT_MIPS_linkage_name:
      return (tag_is_function(tag) ||
              tag_is_variable(tag));
    case DW_AT_specification:
      return (tag_is_function(tag) ||
              tag_is_variable(tag));
    case DW_AT_declaration:
      return (tag_is_function(tag) ||
              tag_is_variable(tag));
    case DW_AT_artificial:
      return tag_is_variable(tag);
    case DW_AT_accessibility:
      return tag_is_function(tag);
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

char harvest_sibling(dwarf_entry* e, unsigned long value)
{
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
        DW_AT_upper_bound : -1	(location list)
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
    //    VG_(printf)("harvest_function_specification_value %x\n", value);
    return 1;
  }
  else if (value && (tag_is_variable(tag))) {
    ((variable*)e->entry_ptr)->specification_ID = value;
    return 1;
  }
  else
    return 0;
}

char harvest_function_accessibility(dwarf_entry* e, char a) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag)) {
    ((function*)e->entry_ptr)->accessibility = a;
    //    VG_(printf)("harvest_function_accessibility %d\n", a);
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

char harvest_const_value(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_enumerator(tag))
    {
      ((enumerator*)e->entry_ptr)->const_value = value;
      return 1;
    }
  else
    return 0;
}

// REMEMBER to use VG_(strdup) to make a COPY of the string
// or else you will run into SERIOUS memory corruption
// problems when readelf.c frees those strings from memory!!!
char harvest_name(dwarf_entry* e, const char* str)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_enumerator(tag))
    {
      ((enumerator*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_collection_type(tag))
    {
      ((collection_type*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_member(tag))
    {
      ((member*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_function(tag))
    {
      ((function*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_formal_parameter(tag))
    {
      ((formal_parameter*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_compile_unit(tag))
    {
      ((compile_unit*)e->entry_ptr)->filename = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_typedef(tag))
    {
      ((typedef_type*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->name = VG_(strdup)(str);
      return 1;
    }
  else
    return 0;
}

// REMEMBER to use VG_(strdup) to make a COPY of the string
// or else you will run into SERIOUS memory corruption
// problems when readelf.c frees those strings from memory!!!
char harvest_mangled_name(dwarf_entry* e, const char* str)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag))
    {
      ((function*)e->entry_ptr)->mangled_name = VG_(strdup)(str);
      return 1;
    }
  else if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->mangled_name = VG_(strdup)(str);
      return 1;
    }
  else
    return 0;
}

char harvest_comp_dir(dwarf_entry* e, const char* str)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_compile_unit(tag))
    {
      ((compile_unit*)e->entry_ptr)->comp_dir = VG_(strdup)(str);
      return 1;
    }
  else
    return 0;
}

// The strange thing is that variable offsets should be NEGATIVE
// but DW_OP_fbreg returns an unsigned value
char harvest_local_var_offset(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_variable(tag))
    {
      ((variable*)e->entry_ptr)->offset = (int)value;
      return 1;
    }
  else
    return 0;
}

char harvest_formal_param_location(dwarf_entry* e, unsigned long value)
{
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_formal_parameter(tag))
    {
      ((formal_parameter*)e->entry_ptr)->location = value;
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
  else
    return 0;
}

char harvest_string(dwarf_entry* e, unsigned long attr, const char* str)
{
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  if (attr == DW_AT_name)
    return harvest_name(e, str);
  else if (attr == DW_AT_comp_dir)
    return harvest_comp_dir(e, str);
  else if (attr == DW_AT_MIPS_linkage_name)
    return harvest_mangled_name(e, str);
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
  else
    return 0;
}

char harvest_address_value(dwarf_entry* e, unsigned long attr,
                           unsigned long value) {
  unsigned long tag;
  if ((e == 0) || (e->entry_ptr == 0))
    return 0;

  tag = e->tag_name;

  if (tag_is_function(tag) && attr == DW_AT_low_pc)
    {
      ((function*)e->entry_ptr)->start_pc = value;
      return 1;
    }
  else if (tag_is_function(tag) && attr == DW_AT_high_pc)
    {
      ((function*)e->entry_ptr)->end_pc = value;
      return 1;
    }
  else
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

  //  printf("--target_ID: 0x%x, index_ptr: 0x%x, upper.ID: 0x%x, lower.ID: 0x%x\n",
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

      //      printf("**lower: %d, mid: %d, upper: %d, target_ID: 0x%x, cur_ID: 0x%x\n",
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
static void link_entries_to_type_entries()
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
          unsigned long target_ID = modifier_ptr->target_ID;

          // Use a binary search to try to find the index of the entry in the
          // array with the corresponding target_ID
          success = binary_search_dwarf_entry_array(target_ID, &target_index);
          if (success)
            {
              modifier_ptr->target_ptr=&dwarf_entry_array[target_index];
            }
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
    array_ptr->subrange_entries = (dwarf_entry**)VG_(calloc)(member_count, sizeof(dwarf_entry*));

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
// with their member variables (both static and instance) and functions
// Precondition: In dwarf_entry_array, all members and member functions
// are listed after the collection's entry with its "level" as 1
// greater than the "level" of the collection's dwarf_entry 'e',
// 'e' if of type {collection}
// Postcondition: num_member_vars, member_vars, num_member_funcs, member_funcs
// num_static_member_vars, static_member_vars are all properly initialized
void link_collection_to_members(dwarf_entry* e, unsigned long dist_to_end)
{
  unsigned long member_var_count = 0;
  unsigned long static_member_var_count = 0;
  unsigned long member_func_count = 0;

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

  cur_entry++; // Move to the next entry - safe since dist_to_end > 0 by this point

  // structs/classes/unions expect DW_TAG_member as member variables
  // enumerations expect DW_TAG_enumerator as member "variables"
  // structs/classes expect DW_TAG_variable as static member variables
  // and DW_TAG_subprogram as member functions

  // Make one pass from the collection entry all the way to
  // to get the numbers of member variables
  // Iteration conditions:
  // 1. Make sure we don't walk off the end of dwarf_entry_array (local_dist_to_end)
  // 2. Make sure that all the entries are at least 1 level above the function entry's level
  //    so that we are not traversing its siblings
  while ((local_dist_to_end > 0) &&
	 (cur_entry->level > collection_entry_level)) {

    if (cur_entry->level == (collection_entry_level + 1)) {
      if (isEnumType) {
        if (tag_is_enumerator(cur_entry->tag_name)) {
          member_var_count++;
        }
      }
      else {
        if (tag_is_member(cur_entry->tag_name)) {
          member_var_count++;
        }
        else if (tag_is_variable(cur_entry->tag_name)) {
          static_member_var_count++;
        }
        else if (tag_is_function(cur_entry->tag_name)) {
          member_func_count++;
          // Set the is_member_func flag here:
          ((function*)(cur_entry->entry_ptr))->is_member_func = 1;
        }
      }
    }

    cur_entry++; // Move to the next entry in dwarf_entry_array
    local_dist_to_end--;
  }

  collection_ptr->num_member_vars = member_var_count;
  collection_ptr->num_static_member_vars = static_member_var_count;
  collection_ptr->num_member_funcs = member_func_count;

  // Make a second pass (actually three second passes)
  // to actually populate the newly-created arrays with entries
  if (member_var_count > 0) {
    int member_var_index = 0;
    collection_ptr->member_vars = (dwarf_entry**)VG_(calloc)(member_var_count, sizeof(dwarf_entry*));

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
          if (tag_is_member(cur_entry->tag_name)) {
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
      (dwarf_entry**)VG_(calloc)(static_member_var_count, sizeof(dwarf_entry*));

    cur_entry = (e + 1);
    local_dist_to_end = dist_to_end;

    while ((local_dist_to_end > 0) &&
	   (cur_entry->level > collection_entry_level)) {
      if (cur_entry->level == (collection_entry_level + 1)) {
        if (tag_is_variable(cur_entry->tag_name)) {
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
    collection_ptr->member_funcs = (dwarf_entry**)VG_(calloc)(member_func_count, sizeof(dwarf_entry*));

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
}

// Same as above except linking functions with formal parameters and local variables
// Precondition: In dwarf_entry_array, all formal parameter and local variable
//               entries are listed after the function entry with its "level" as
//               1 greater than the "level" of the function's dwarf_entry 'e',
//               'e' is of type {function}
// Postcondition: num_formal_params, params, num_local_vars, and local_vars
//                are properly initialized for the given dwarf_entry e which
//                is of type {function}

// This also attempts to do the following:
//  For every function entry e with a non-null specification_ID, attempt to
//  look up the entry X with the ID given by specification_ID and copy the
//  start_pc from e to X while copying (aliasing) the name,
//  mangled_name, return_type_ID, and accessibility from X to e
void link_function_to_params_and_local_vars(dwarf_entry* e, unsigned long dist_to_end)
{
  unsigned long param_count = 0;
  unsigned long var_count = 0;

  int function_entry_level = e->level;
  int local_dist_to_end = dist_to_end;
  //  unsigned long sibling_entry_ID = e->sibling_ID;
  char success = 0;

  dwarf_entry* cur_entry = e;
  unsigned long aliased_index = 0;
  function* function_ptr = (function*)(e->entry_ptr);

  if (function_ptr->specification_ID) {
    success = binary_search_dwarf_entry_array(function_ptr->specification_ID, &aliased_index);
    if (success) {
      dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
      if (tag_is_function(aliased_entry->tag_name)) {
        function* aliased_func_ptr = (function*)(aliased_entry->entry_ptr);

        aliased_func_ptr->start_pc = function_ptr->start_pc;

        function_ptr->name = aliased_func_ptr->name;
        function_ptr->mangled_name = aliased_func_ptr->mangled_name;
        function_ptr->return_type_ID = aliased_func_ptr->return_type_ID;
        function_ptr->accessibility = aliased_func_ptr->accessibility;

        // However, aliased_func_ptr will still have is_declaration == 1
        // so it will NOT be added to DaikonFunctionInfoTable - instead,
        // function_ptr will be added so that when we do a lookup for
        // findFunctionInfoByStartAddr(aliased_func_ptr->start_pc),
        // we will get the function_ptr entry.
        // This is CRUCIAL because the function_ptr entry has the REAL names and offsets
        // of the parameters whereas the aliased_func_ptr is only an empty shell
      }
    }
  }

  // If you are at the end of the array, you're screwed anyways
  if(dist_to_end == 0)
    return;

  // First pick off the formal parameters ...

  cur_entry++; // Move to the next entry - safe since dist_to_end > 0 by this point
  // functions expect DW_TAG_formal_parameter as parameters

  //  printf("\nlink_params: %s:\n", function_ptr->name);

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

    //    print_dwarf_entry(cur_entry, 0);

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

  //  printf("param_count: %d, var_count: %d\n", param_count, var_count);


  // Make a second pass (actually two second passes)
  // to actually populate the newly-created arrays with entries
  if (param_count > 0) {
    int param_index = 0;
    function_ptr->params = (dwarf_entry**)VG_(calloc)(param_count, sizeof(dwarf_entry*));

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
    function_ptr->local_vars = (dwarf_entry**)VG_(calloc)(var_count, sizeof(dwarf_entry*));

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
Requires: e non-null
Modifies: name
Returns: none
Effects: *name will contain the name of the FIRST typedef_type entry
         in dwarf_entry_array whose target_type_ID matches e->ID.
         If none found, name is unmodified
*/
void determineTypedefNameForEntry(char** name, dwarf_entry* e)
{
  int i;
  dwarf_entry* cur_entry = 0;
  for (i = 0; i < dwarf_entry_array_size; i++) {
    cur_entry = &dwarf_entry_array[i];
    if (tag_is_typedef(cur_entry->tag_name)) {
      typedef_type* cur_typedef = (typedef_type*)(cur_entry->entry_ptr);
      if ((cur_typedef->target_type_ID == e->ID) &&
          cur_typedef->name) {
        *name = cur_typedef->name;
      }
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
static void initialize_function_filenames()
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
static void link_array_entries_to_members()
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
	    determineTypedefNameForEntry(&(collectionPtr->name), cur_entry);
	  }
        link_collection_to_members(cur_entry, dwarf_entry_array_size - idx - 1);
      }

      if (tag_is_array_type(cur_entry->tag_name))
	link_array_type_to_members(cur_entry, dwarf_entry_array_size - idx - 1);
      else if (tag_is_function(cur_entry->tag_name))
        link_function_to_params_and_local_vars(cur_entry, dwarf_entry_array_size - idx - 1);

      // Link C++ static member variables
      // Copy all the information into the version of the variable "declaration" one
      // which is INSIDE the appropriate class/struct DWARF entry
      else if (tag_is_variable(cur_entry->tag_name)) {
        variable* variablePtr = (variable*)cur_entry->entry_ptr;
        if (variablePtr->specification_ID && variablePtr->globalVarAddr) {
          unsigned long aliased_index = 0;
          char success = 0;
          success =
            binary_search_dwarf_entry_array(variablePtr->specification_ID, &aliased_index);
          if (success) {
            dwarf_entry* aliased_entry = &dwarf_entry_array[aliased_index];
            if (tag_is_variable(aliased_entry->tag_name)) {
              variable* aliased_var_ptr = (variable*)(aliased_entry->entry_ptr);
              aliased_var_ptr->globalVarAddr = variablePtr->globalVarAddr;
              aliased_var_ptr->couldBeGlobalVar = 0;
              aliased_var_ptr->isStaticMemberVar = 1;
              aliased_var_ptr->is_declaration_or_artificial = 0;

              //              VG_(printf)("mangled_name: %s - ID: %x - globalVarAddr: 0x%x\n",
              //                          aliased_var_ptr->mangled_name,
              //                          aliased_entry->ID,
              //                          aliased_var_ptr->globalVarAddr);
            }
          }
        }
      }
    }
}

// Prints the contents of the entry depending on its type
void print_dwarf_entry(dwarf_entry* e, char simplified)
{
  if (e == 0)
    {
      printf("ERROR! Pointer e is null in print_dwarf_entry\n");
      return;
    }

  printf("ID:0x%lx, LVL:%d, SIB_ID:0x%lx, TAG:%s \n", e->ID, e->level, e->sibling_ID, get_TAG_name(e->tag_name));

  switch(e->tag_name)
    {
    case DW_TAG_subprogram:
      {
        function* function_ptr = (function*)(e->entry_ptr);
        printf("  Name: %s, Filename: %s, Return Type ID (addr): 0x%lx (0x%lx), is_ext: %d, low_pc: 0x%lx\n",
               function_ptr->name,
               function_ptr->filename,
               function_ptr->return_type_ID,
               ((simplified && function_ptr->return_type) ?
                function_ptr->return_type - dwarf_entry_array :
                (unsigned long)(function_ptr->return_type)),
	       function_ptr->is_external,
	       function_ptr->start_pc);
        break;
      }
    case DW_TAG_formal_parameter:
      {
        formal_parameter* formal_param_ptr = (formal_parameter*)(e->entry_ptr);
        printf("  Name: %s, Type ID (addr): 0x%lx (0x%lx), Location: %ld\n",
               formal_param_ptr->name,
               formal_param_ptr->type_ID,
               ((simplified && formal_param_ptr->type_ptr) ?
                formal_param_ptr->type_ptr - dwarf_entry_array :
                (unsigned long)(formal_param_ptr->type_ptr)),
               formal_param_ptr->location);
        break;
      }
    case DW_TAG_member:
      {
        member* member_ptr = (member*)(e->entry_ptr);
        printf("  Name: %s, Type ID (addr): 0x%lx (0x%lx), Data member location: %ld, Byte size: %ld, Bit offset: %ld, Bit size: %ld\n",
               member_ptr->name,
               member_ptr->type_ID,
               ((simplified && member_ptr->type_ptr) ?
                member_ptr->type_ptr - dwarf_entry_array :
                (unsigned long)(member_ptr->type_ptr)),
               member_ptr->data_member_location,
               member_ptr->internal_byte_size,
               member_ptr->internal_bit_offset,
               member_ptr->internal_bit_size);
        break;
      }
    case DW_TAG_enumerator:
      {
        enumerator* enumerator_ptr = (enumerator*)(e->entry_ptr);
        printf("  Name: %s, Const value: %ld\n",
               enumerator_ptr->name,
               enumerator_ptr->const_value);
        break;
      }

    case DW_TAG_structure_type:
    case DW_TAG_union_type:
    case DW_TAG_enumeration_type:
      {
	collection_type* collection_ptr = (collection_type*)(e->entry_ptr);
        printf("  Name: %s, Byte size: %ld\n",
               collection_ptr->name,
               collection_ptr->byte_size);

/*         printf("  Name: %s, Byte size: %ld, Num. members: %ld, 1st member addr: 0x%lx\n", */
/*                collection_ptr->name, */
/*                collection_ptr->byte_size, */
/* 	       collection_ptr->num_members, */
/* 	       ((simplified && collection_ptr->members) ? */
/* 		collection_ptr->members - dwarf_entry_array : */
/* 		(unsigned long)(collection_ptr->members))); */

        break;
      }

    case DW_TAG_base_type:
      {
        base_type* base_ptr = (base_type*)(e->entry_ptr);
        printf("  Byte size: %ld, Encoding: %ld ",
               base_ptr->byte_size,
               base_ptr->encoding);

        // More detailed encoding information
        switch (base_ptr->encoding)
          {
          case DW_ATE_void:             printf ("(void)"); break;
          case DW_ATE_address:		printf ("(machine address)"); break;
          case DW_ATE_boolean:		printf ("(boolean)"); break;
          case DW_ATE_complex_float:	printf ("(complex float)"); break;
          case DW_ATE_float:		printf ("(float)"); break;
          case DW_ATE_signed:		printf ("(signed)"); break;
          case DW_ATE_signed_char:	printf ("(signed char)"); break;
          case DW_ATE_unsigned:		printf ("(unsigned)"); break;
          case DW_ATE_unsigned_char:	printf ("(unsigned char)"); break;
            /* DWARF 2.1 value.  */
          case DW_ATE_imaginary_float:	printf ("(imaginary float)"); break;
          default:
            if (base_ptr->encoding >= DW_ATE_lo_user
                && base_ptr->encoding <= DW_ATE_hi_user)
              {
                printf ("(user defined type)");
              }
            else
              {
                printf ("(unknown type)");
              }
            break;
          }

        printf(", Bit size: %ld, Bit offset: %ld\n",
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
        printf("  Target ID (addr): 0x%lx (0x%lx)\n",
               modifier_ptr->target_ID,
               ((simplified && modifier_ptr->target_ptr) ?
                modifier_ptr->target_ptr - dwarf_entry_array :
                (unsigned long)(modifier_ptr->target_ptr)));
        break;
      }
    case DW_TAG_array_type:
      {
        array_type* array_ptr = (array_type*)(e->entry_ptr);
        printf("  Type ID (addr): 0x%lx (0x%lx), Num. subrange entries: %ld\n",
               array_ptr->type_ID,
               ((simplified && array_ptr->type_ptr) ?
                (array_ptr->type_ptr - dwarf_entry_array) :
                (unsigned long)(array_ptr->type_ptr)),
               array_ptr->num_subrange_entries);
        break;
      }
    case DW_TAG_subrange_type:
      {
        array_subrange_type* array_subrange_ptr = (array_subrange_type*)(e->entry_ptr);
        printf("  Upper bound: %lu\n",
               array_subrange_ptr->upperBound);
        break;
      }
    case DW_TAG_typedef:
      {
        typedef_type* typedef_ptr = (typedef_type*)(e->entry_ptr);
        printf("  Name: %s, Target type ID (addr): 0x%lx (0x%lx)\n",
               typedef_ptr->name,
               typedef_ptr->target_type_ID,
               ((simplified && typedef_ptr->target_type_ptr) ?
                (typedef_ptr->target_type_ptr - dwarf_entry_array) :
                (unsigned long)(typedef_ptr->target_type_ptr)));
        break;
      }
    case DW_TAG_variable:
      {
        variable* variable_ptr = (variable*)(e->entry_ptr);
        printf("  Name: %s, Target type ID (addr): 0x%lx (0x%lx), is_ext: %d, couldBeGlobalVar: %d, globalVarAddr: 0x%lx, localOffset: %d\n",
               variable_ptr->name,
               variable_ptr->type_ID,
               ((simplified && variable_ptr->type_ptr) ?
                (variable_ptr->type_ptr - dwarf_entry_array) :
                (unsigned long)(variable_ptr->type_ptr)),
	       variable_ptr->is_external,
               variable_ptr->couldBeGlobalVar,
               variable_ptr->globalVarAddr,
               variable_ptr->offset);
        break;
      }
    case DW_TAG_compile_unit:
      {
        compile_unit* compile_ptr = (compile_unit*)(e->entry_ptr);
        printf("  Filename: %s, Compile dir: %s\n",
               compile_ptr->filename,
               compile_ptr->comp_dir);
        break;
      }

    case DW_TAG_subroutine_type:
      {
        printf(  "DW_TAG_subroutine_type not yet supported\n");
        // TODO: Don't print anything out for this yet - it's still
        //       uninitialized
        //        function_type * func_type = (function_type *)(e->entry_ptr);
        //        printf("  Return type ID (addr): 0x%lx (%p)\n",
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
  dwarf_entry_array = VG_(calloc)(num_entries, sizeof *dwarf_entry_array);
}

/*
Requires: dwarf_entry_array is initialized
Modifies: dwarf_entry_array (free and set to 0)
Returns:
Effects: Destroys dwarf_entry_array and all entry_ptr fields of all entries
*/
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
  unsigned long i;
  printf("--- BEGIN DWARF ENTRY ARRAY - size: %ld\n", dwarf_entry_array_size);
  for (i = 0; i < dwarf_entry_array_size; i++)
    {

      printf("array[%ld] (0x%lx): ", i,
             (simplified ? i : (int)(dwarf_entry_array + i)));
      print_dwarf_entry(&dwarf_entry_array[i], simplified);
    }
  printf("--- END DWARF ENTRY ARRAY\n");
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
          e->entry_ptr = VG_(calloc)(1, sizeof(base_type));
        }
      else if (tag_is_modifier_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(modifier_type));
        }
      else if (tag_is_collection_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(collection_type));
        }
      else if (tag_is_member(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(member));
        }
      else if (tag_is_enumerator(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(enumerator));
        }
      else if (tag_is_function(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(function));
        }
      else if (tag_is_formal_parameter(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(formal_parameter));
        }
      else if (tag_is_compile_unit(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(compile_unit));
        }
      else if (tag_is_function_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(function_type));
        }
      else if (tag_is_array_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(array_type));
        }
      else if (tag_is_array_subrange_type(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(array_subrange_type));
        }
      else if (tag_is_typedef(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(typedef_type));
        }
      else if (tag_is_variable(e->tag_name))
        {
          e->entry_ptr = VG_(calloc)(1, sizeof(variable));
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

  link_array_entries_to_members();
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

// Finds the first function entry to the LEFT of the given entry e
// with a level lower than e's level and grabs its startPC
unsigned long findFunctionStartPCForVariableEntry(dwarf_entry* e)
{
  int idx;
  dwarf_entry* cur_entry = 0;
  unsigned long entry_index;

  char success = binary_search_dwarf_entry_array(e->ID, &entry_index);

  if (!success)
    return 0;

  // Traverse backwards (to the LEFT) in dwarf_entry_array
  for (idx = entry_index; idx >= 0; idx--)
    {
      cur_entry = &dwarf_entry_array[idx];

      if ((tag_is_function(cur_entry->tag_name)) &&
	  (cur_entry->level < e->level))
        return ((function*)cur_entry->entry_ptr)->start_pc;
    }
  return 0;
}
