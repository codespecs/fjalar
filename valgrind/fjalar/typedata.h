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

/* typedata.h:
   Everything here attempts to extract the information directly
   from the DWARF2 debugging information embedded within an ELF
   executable, piggy-backing off of readelf.c code. These data
   structures mimic the types of DWARF2 entries that we are interested
   in tracking.

   This should NOT be visible to tools.
*/

#ifndef TYPEDATA_H
#define TYPEDATA_H

#include "GenericHashtable.h"
#include "fjalar_dwarf.h"
#include "pub_tool_basics.h"
#include "pub_tool_xarray.h"

// compile_unit - used to figure out filename and compilation directory
// We assume that every function belongs to the file specified
// by the nearest compile_unit entry (to its left) in dwarf_entry_array
// as well as the file variables were declared in.
typedef struct
{
  char* filename;
  char* comp_dir;
  XArray* file_name_table;
  unsigned long stmt_list; // Loction of the compile unit's
                           // line information as an offset
                           // from the start of .debug_line
} compile_unit;

// Contains one entry that holds data for one of many possible types
// depending on tag_name
typedef struct
{
  unsigned long ID; // Unique ID for each entry
  unsigned long tag_name; // DW_TAG_____ for the type of this entry
  int level; // The level of this entry (useful for nested structs and function local vars.)
  unsigned long sibling_ID; // for DW_AT_sibling
  compile_unit* comp_unit; // The compilation unit this entry belongs.
                           // compile_unit entries belong to themselves
                           // this entry_ptr == comp_unit for comp_units
  void* entry_ptr; // Cast this pointer depending on value of tag_name, which specifies
                   // the "type" of this dwarf_entry
} dwarf_entry;

// Entries for individual types

// Struct representing the location list.
// Representned as a linked list.
typedef struct _location_list
{
  unsigned long offset;
  unsigned long begin;
  unsigned long end;
  enum dwarf_location_atom atom; //Location Expression.
  long long atom_offset;
  struct _location_list *next;
} location_list;

// Struct representing a debug_frame block.
// Represented as a linked list.
typedef struct _debug_frame
{
  unsigned long begin;
  unsigned long end;
  struct _debug_frame *next;
} debug_frame;


typedef struct
{
  unsigned long byte_size; // DW_AT_byte_size
  unsigned long encoding;

  // (comment added 2005)
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

// For C++ inheritance:
typedef struct
{
  unsigned long superclass_type_ID; // the ID of the superclass
  unsigned long accessibility;      // the type of inheritance (public, protected, private)
  unsigned long member_var_offset;  // the offset of member variables inherited from this class
} inheritance_type;

// For C++ namespaces
typedef struct
{
  char* namespace_name; // "::" is the name for the default namespace
} namespace_type;


// collection_type corresponds to the following DWARF2 types:
// DW_TAG{_structure_type, _union_type, _enumeration_type, _class_type}
typedef struct
{
  char* name;          // For unnamed structs/unions/enums, we should just munge the
                       // name from the ID field so that we have something
                       // to use to identify this struct
                       // We will name it "unnamed_0x$ID" where $ID
                       // is the ID field in hex.

  char is_declaration; // If this is non-null, then this entry is simply
                       // an empty declaration with no real members,
                       // so we should ignore it

  // While the DWARF definition indicates that DW_AT_specification may
  // be used with collections, it appears that gcc does not do so. (markro)
  unsigned long specification_ID; // Relevant for C++: See comment on Specification ID 
                                  // in the function str

  unsigned long byte_size;

  // Make these small and smash them together to save space:
  unsigned short num_member_vars;
  unsigned short num_member_funcs; // C++ only - for member functions
  unsigned short num_static_member_vars; // C++ only - for static member variables
  unsigned short num_superclasses; // C++ only - for superclasses

  dwarf_entry** member_vars; // Array of size num_member_vars; Each element is a
                            // POINTER to a dwarf_entry of type = {member, enumerator}

  dwarf_entry** member_funcs; // Array of size num_member_funcs; Each element is a
                              // POINTER to a dwarf_entry of type = {function}
                              // but these functions are only "declarations" and we need
                              // to look elsewhere in DWARF to find their true definitions
                              // (This is only true if function definitions and declarations
                              //  are made in separate .h and .cpp files in typical C++ fashion)

  dwarf_entry** static_member_vars; // Array of size num_static_member_vars; Each element is a
                                    // POINTER to a dwarf_entry of type = {variable}

  // The superclasses of this class (C++ only) - gotten from DW_TAG_inheritance
  dwarf_entry** superclasses; // Array of size num_superclasses; each entry is a POINTER
                              // to a dwarf_entry of type {inheritance_type}
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

  unsigned long accessibility;  // accessibility of this member variable (public, protected, or private)
  char is_external;         // is_external when applied to a member variable implies it's static

  // (comment added 2005)
  // TODO: support for bit fields not yet implemented
  //  char is_bit_field; // 1 = bit field
  // Only relevant for bit fields
  unsigned long internal_byte_size;
  unsigned long internal_bit_offset;
  unsigned long internal_bit_size;


  // The value of this variable (if it's constant)
  char is_const;
  long const_value; 

  // The file this variable is declared in
  unsigned long decl_file;
} member;

// enumeration member
typedef struct
{
  char* name;
  char is_const;
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

  // Make these small and smash them together to save space:
  unsigned short num_formal_params;
  unsigned short num_local_vars;

  // This array is NO LONGER inlined within dwarf_entry_array
  dwarf_entry** params; // Array of size num_formal_params, type = {formal_parameter}
                        // Each entry of this array is a POINTER to a dwarf_entry
                        // of type {formal_parameter}

  // This array is NO LONGER inlined within dwarf_entry_array
  dwarf_entry** local_vars; // Array of size num_local_vars, type = {variable}
                            // Each entry of this array is a POINTER to a dwarf_entry
                            // of type {variable}

  char is_external; /* Is it extern? If so, probably want to skip it */
  char is_member_func; /* 1 if it's a member function (within a class or struct) */
  char is_declaration; // Relevant for C++: 1 if this function is an empty
  // declaration - all of the important info. about this function comes from
  // the matching entry whose specification_ID field is the ID of this entry
  // Do NOT add an entry with is_declaration == 1 to
  // FunctionTable because it's an empty shell ...
  // instead add its analogue whose specification_ID points to this entry
  char accessibility; // 0 if none - ASSUMED TO BE PUBLIC!!!
                      // 1 (DW_ACCESS_public) if public,
                      // 2 (DW_ACCESS_protected) if protected,
                      // 3 (DW_ACCESS_private) if private

  unsigned long specification_ID; // Relevant for C++: This is a valid ID
  // of a dwarf_entry (of type function) if this function entry represents
  // the actual data for the entry with ID equal to specification_ID

  unsigned long abstract_origin_ID; // Relevant for C++ member functions
  // that are declared within a class definition.  For these cases,
  // there will be a function dwarf_entry with the proper start_pc and
  // end_pc and the abstract_origin_ID that points to another function
  // dwarf_entry.  That dwarf_entry will have a specification_ID that
  // points to the REAL function entry with the name.  Example:
  /*

 <1><180a1>: Abbrev Number: 136 (DW_TAG_subprogram)
     DW_AT_sibling     : <180d1>
     DW_AT_abstract_origin: <18069>
     DW_AT_low_pc      : 0x8048c16
     DW_AT_high_pc     : 0x8048c5d
     DW_AT_frame_base  : 1 byte block: 55 	(DW_OP_reg5)

 <1><18069>: Abbrev Number: 132 (DW_TAG_subprogram)
     DW_AT_sibling     : <1809c>
     DW_AT_specification: <17e25>
     DW_AT_inline      : 2	(declared as inline but ignored)

 <2><17e25>: Abbrev Number: 56 (DW_TAG_subprogram)
     DW_AT_sibling     : <17e51>
     DW_AT_external    : 1
     DW_AT_name        : push
     DW_AT_decl_file   : 53
     DW_AT_decl_line   : 27
     DW_AT_MIPS_linkage_name: _ZN5Stack4pushEPc
     DW_AT_declaration : 1

  */

  unsigned long frame_pc;
  unsigned long comp_pc;  /* Top of the current compilation unit */
  unsigned long start_pc; /* Location of the function in memory */
  unsigned long end_pc;   /* Location of the highest address of an
                             instruction in the function */


  enum dwarf_location_atom frame_base_expression; /* Location of the framebase.
						     Is likely to be a register expression
						     or the location list */
  long frame_base_offset; /* Offset from Frame_base_expression that correspods to the frame_base
			   */

} function;

// (comment added 2005)
// TODO: support for function pointer parameters not yet implemented
/* This is for abstract function types, as might be used in declaring
   a parameter as taking a function pointer. At least for the moment, we
   won't bother about the parameters. */
typedef struct {
  unsigned long return_type_ID;
  dwarf_entry* return_type;
} function_type;

enum location_type {
  LT_NONE = 0,
  LT_FP_OFFSET,
  LT_REGISTER
};

// function formal parameter
typedef struct
{
  char* name;
  unsigned long type_ID;
  dwarf_entry* type_ptr;
  enum location_type location_type;

  enum dwarf_location_atom loc_atom; //Location Expression.

  dwarf_location dwarf_stack[MAX_DWARF_OPS];
  unsigned int dwarf_stack_size;

  long location; // Offset from location

                 // This is stored as: (DW_OP_fbreg: x),
                 // where x is location offset
                 // (comment added 2005)
                 // TODO: DW_OP_fbreg: seems unreliable - gives flaky
                 //       values sometimes - look into finding a better
                 //       way to get the parameter location
  unsigned int valid_loc;

  unsigned long abstract_origin_ID; // See comment in the function struct definition
                                    // for the uses of this.

} formal_parameter;

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

  unsigned long specification_ID; // Relevant for C++:
  // DO NOT add an entry with specification_ID non-null to any variable
  // lists because it's an empty shell

  // We should try to grab this from the symbol table if one is not
  // provided because g++ 4.0 doesn't provide global variable
  // addresses in the debug. info.
  unsigned long globalVarAddr; // only valid for global variables

  int offset;  // only valid for local variables
  int regBase; // not all locals are addressed from EBP

  // accessibility of this variable (public, protected, or private)
  // (only relevant if isStaticMemberVar)
  unsigned long accessibility;

  // The value of this variable (if it's constant)
  char is_const;
  long const_value; 

  // The file this variable is declared in
  unsigned long decl_file;
} variable;

// Globals

extern dwarf_entry* dwarf_entry_array;
extern compile_unit** comp_unit_info;
extern unsigned long dwarf_entry_array_size;
extern location_list *debug_loc_list;
extern Bool clang_producer;
extern Bool other_producer;

unsigned int hashString(const char* str);
int equivalentStrings(char* str1, char* str2);


// The following are extracted from the executable's symbol table by
// running readelf with the -s option:

void initialize_typedata_structures(void);

// Key: String that represents the (possibly mangled) name of a function
// Value: An int that represents the global start_PC address of that function
struct genhashtable* FunctionSymbolTable;

// (reverse of FunctionSymbolTable)
// Key: An int that represents the global start_PC address of that function
// Value: String that represents the (possibly mangled) name of a function
struct genhashtable* ReverseFunctionSymbolTable;

// Key: String that represents the (possibly mangled) name of a variable
// Value: An int that represents the global address of that variable
struct genhashtable* VariableSymbolTable;

static __inline__ void insertIntoFunctionSymbolTable(char* name, void* addr) {
  //  printf("FunctionSymbolTable insert: %p  %s\n", addr, name);
  // Insert into both the regular and reverse tables:

  genputtable(FunctionSymbolTable,
              (void*)name,
              (void*)addr);

  genputtable(ReverseFunctionSymbolTable,
              (void*)addr,
              (void*)name);
}

static __inline__ void insertIntoVariableSymbolTable(char* name, void* addr) {
  //  printf("VariableSymbolTable insert: %p  %s\n", addr, name);
  genputtable(VariableSymbolTable,
              (void*)name,
              (void*)addr);
}

// Initialized based on the .debug_lines DWARF section, this table
// records the code addresses for each statement; more specifically,
// it maps from an address representing the start of one statement to
// an address representing the start of the next. We use this
// information to skip function prologues.
struct genhashtable *next_line_addr;

// The addresses and sizes of the sections (.data, .bss, .rodata, and .data.rel.ro) that
// hold global variables (initialized in readelf.c):
unsigned int data_section_addr;
unsigned int data_section_size;
unsigned int bss_section_addr;
unsigned int bss_section_size;
unsigned int rodata_section_addr;
unsigned int rodata_section_size;
unsigned int relrodata_section_addr;
unsigned int relrodata_section_size;

// Function declarations

// From readelf.c
const char *get_TAG_name(unsigned long tag);
bool process_elf_binary_data(const HChar* filename);

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
char tag_is_inheritance(unsigned long tag);
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
char harvest_producer(dwarf_entry* e, const char* str);
char harvest_formal_param_location_offset(dwarf_entry* e, long value);
char harvest_formal_param_location_atom(dwarf_entry* e, enum dwarf_location_atom atom, long value);
char harvest_data_member_location(dwarf_entry* e, unsigned long value);
char harvest_string(dwarf_entry* e, unsigned long attr, const char* str);
char harvest_external_flag_value(dwarf_entry *e, unsigned long value);
char harvest_address_value(dwarf_entry* e, unsigned long attr, unsigned long value);
char harvest_variable_addr_value(dwarf_entry* e, unsigned long value);
char harvest_ordinary_unsigned_value(dwarf_entry* e, unsigned long attr, unsigned long value);
char harvest_local_var_offset(dwarf_entry* e, unsigned long value, int regNum);
char harvest_sibling(dwarf_entry* e, unsigned long value);
char harvest_declaration_value(dwarf_entry* e, unsigned long value);
char harvest_artificial_value(dwarf_entry* e, unsigned long value);
char harvest_specification_value(dwarf_entry* e, unsigned long value);
char harvest_abstract_origin_value(dwarf_entry* e, unsigned long value);
char harvest_accessibility(dwarf_entry* e, char a);
char harvest_location_list_entry(location_list* ll, unsigned long offset);
char harvest_debug_frame_entry(debug_frame* df);
char harvest_frame_base(dwarf_entry* e, enum dwarf_location_atom a, long offset);
char harvest_decl_file(dwarf_entry* e, unsigned long value);
char harvest_stmt_list(dwarf_entry* e, unsigned long value);

char harvest_file_name_table(unsigned long debug_line_offset, XArray* table);


char binary_search_dwarf_entry_array(unsigned long target_ID, unsigned long* index_ptr);

void init_specification_and_abstract_stuff(void);
void process_abstract_origin_items(void);
void process_specification_items(void);

void link_array_type_to_members(dwarf_entry* e, unsigned long dist_to_end);
void link_collection_to_members(dwarf_entry* e, unsigned long dist_to_end);
void link_function_to_params_and_local_vars(dwarf_entry* e, unsigned long dist_to_end);
void print_dwarf_entry(dwarf_entry* e, char simplified);

void initialize_dwarf_entry_array(unsigned long num_entries);
void initialize_compile_unit_array(unsigned long num_entries);
void destroy_dwarf_entry_array(void);
void simple_print_dwarf_entry_array(void);
void print_dwarf_entry_array(void);
void print_dwarf_entry_array_helper(char simplified);
void initialize_dwarf_entry_ptr(dwarf_entry* e);
void finish_dwarf_entry_array_init(void);

void add_comp_unit(compile_unit* unit);

char tag_is_array_type(unsigned long tag);
char tag_is_array_subrange_type(unsigned long tag);
char tag_is_typedef(unsigned long tag);
char tag_is_variable(unsigned long tag);

char* findFilenameForEntry(dwarf_entry* e);
unsigned long findFunctionStartPCForVariableEntry(dwarf_entry* e);
namespace_type* findNamespaceForVariableEntry(dwarf_entry* e);
dwarf_entry* find_struct_entry_with_name(char* name);

#endif
