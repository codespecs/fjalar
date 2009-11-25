/* readelf.c -- display contents of an ELF format file
   Copyright 1998, 1999, 2000, 2001, 2002, 2003 Free Software Foundation, Inc.

   Originally developed by Eric Youngdale <eric@andante.jic.com>
   Modifications by Nick Clifton <nickc@redhat.com>

   This file is part of GNU Binutils.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.  */

/* readelf.c

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This file was modified by Philip Guo, MIT CSAIL Program Analysis Group,
   to perform recording of function return types and parameter types
   for Fjalar, a Valgrind tool that is a C/C++ dynamic analysis framework

   2005-04-28:
   Ported over to Valgrind 3 and integrated with the DynComp dynamic
   comparability analysis tool for C/C++.

   This file interprets the DWARF2 debugging information within
   the ELF binary and then calls functions in typedata.c

   My changes are denoted by // PG marks
*/

#include "my_libc.h"

#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"

// For debugging
extern Bool fjalar_debug;

#define FJALAR_DPRINTF(...) do { if (fjalar_debug) \
      VG_(printf)(__VA_ARGS__); } while (0)


#if __GNUC__ >= 2
/* Define BFD64 here, even if our default architecture is 32 bit ELF
   as this will allow us to read in and parse 64bit and 32bit ELF files.
   Only do this if we believe that the compiler can support a 64 bit
   data type.  For now we only rely on GCC being able to do this.  */
#define BFD64
#endif

#include "bfd.h"

#include "elf/common.h"
#include "elf/external.h"
#include "elf/internal.h"
#include "elf/dwarf2.h"

#include "typedata.h" // PG

/* The following headers use the elf/reloc-macros.h file to
   automatically generate relocation recognition functions
   such as elf_mips_reloc_type()  */

#define RELOC_MACROS_GEN_FUNC

#include "elf/i386.h"

#include "bucomm.h"
//#include "libiberty.h"

char *program_name = "readelf";
unsigned long dynamic_addr;
bfd_size_type dynamic_size;
char *dynamic_strings;
char *string_table;
unsigned long string_table_length;
unsigned long num_dynamic_syms;
Elf_Internal_Sym *dynamic_symbols;
Elf_Internal_Syminfo *dynamic_syminfo;
unsigned long dynamic_syminfo_offset;
unsigned int dynamic_syminfo_nent;
char program_interpreter[64];
long dynamic_info[DT_JMPREL + 1];
long version_info[16];
long loadaddr = 0;
Elf_Internal_Ehdr elf_header;
Elf_Internal_Shdr *section_headers;
Elf_Internal_Dyn *dynamic_segment;
Elf_Internal_Shdr *symtab_shndx_hdr;
int show_name;
int do_dynamic;
int do_syms;
int do_reloc;
int do_sections;
int do_segments;
int do_unwind;
int do_using_dynamic;
int do_header;
int do_dump;
int do_version;
int do_wide;
int do_histogram;
int do_debugging;
int do_debug_info;
int do_debug_abbrevs;
int do_debug_lines;
int do_debug_pubnames;
int do_debug_aranges;
int do_debug_frames;
int do_debug_frames_interp;
int do_debug_macinfo;
int do_debug_str;
int do_debug_loc;
int do_arch;
int do_notes;
int is_32bit_elf;

// PG set this equal to 1 to print out results
int print_results = 1;

// PG declarations
/*
char tag_is_relevant_entry(unsigned long tag);
void initialize_dwarf_entry_array(unsigned long num_entries);
void destroy_dwarf_entry_array(void);

char tag_is_modifier_type(unsigned long tag);
char tag_is_collection_type(unsigned long tag);
char tag_is_base_type(unsigned long tag);
char tag_is_member(unsigned long tag);
char tag_is_enumerator(unsigned long tag);
char tag_is_function(unsigned long tag);
char tag_is_formal_parameter(unsigned long tag);
*/

/* A dynamic array of flags indicating which sections require dumping.  */
char *dump_sects = NULL;
unsigned int num_dump_sects = 0;

#define HEX_DUMP	(1 << 0)
#define DISASS_DUMP	(1 << 1)
#define DEBUG_DUMP	(1 << 2)

/* How to rpint a vma value.  */
typedef enum print_mode
{
  HEX,
  DEC,
  DEC_5,
  UNSIGNED,
  PREFIX_HEX,
  FULL_HEX,
  LONG_HEX
}
print_mode;

/* Forward declarations for dumb compilers.  */
static void print_vma
  PARAMS ((bfd_vma, print_mode));
static void print_symbol
  PARAMS ((int, const char *));
static bfd_vma (*byte_get)
  PARAMS ((unsigned char *, int));
static bfd_vma byte_get_little_endian
  PARAMS ((unsigned char *, int));
static bfd_vma byte_get_big_endian
  PARAMS ((unsigned char *, int));
static void (*byte_put)
  PARAMS ((unsigned char *, bfd_vma, int));
static void byte_put_little_endian
  PARAMS ((unsigned char *, bfd_vma, int));
static void byte_put_big_endian
  PARAMS ((unsigned char *, bfd_vma, int));
static const char *get_mips_dynamic_type
  PARAMS ((unsigned long));
static const char *get_sparc64_dynamic_type
  PARAMS ((unsigned long));
static const char *get_ppc64_dynamic_type
  PARAMS ((unsigned long));
static const char *get_parisc_dynamic_type
  PARAMS ((unsigned long));
static const char *get_ia64_dynamic_type
  PARAMS ((unsigned long));
static const char *get_dynamic_type
  PARAMS ((unsigned long));
static int slurp_rela_relocs
  PARAMS ((FILE *, unsigned long, unsigned long, Elf_Internal_Rela **,
	   unsigned long *));
static int slurp_rel_relocs
  PARAMS ((FILE *, unsigned long, unsigned long, Elf_Internal_Rela **,
	   unsigned long *));
static int dump_relocations
  PARAMS ((FILE *, unsigned long, unsigned long, Elf_Internal_Sym *,
	   unsigned long, char *, int));
static char *get_file_type
  PARAMS ((unsigned));
static char *get_machine_name
  PARAMS ((unsigned));
static char *get_machine_flags
  PARAMS ((unsigned, unsigned));
static const char *get_mips_segment_type
  PARAMS ((unsigned long));
static const char *get_parisc_segment_type
  PARAMS ((unsigned long));
static const char *get_ia64_segment_type
  PARAMS ((unsigned long));
static const char *get_segment_type
  PARAMS ((unsigned long));
static const char *get_mips_section_type_name
  PARAMS ((unsigned int));
static const char *get_parisc_section_type_name
  PARAMS ((unsigned int));
static const char *get_ia64_section_type_name
  PARAMS ((unsigned int));
static const char *get_section_type_name
  PARAMS ((unsigned int));
static const char *get_dynamic_flags
  PARAMS ((bfd_vma));
static int process_file_header
  PARAMS ((void));
static int process_program_headers
  PARAMS ((FILE *));
static int process_section_headers
  PARAMS ((FILE *));
static int process_unwind
  PARAMS ((FILE *));
static void dynamic_segment_mips_val
  PARAMS ((Elf_Internal_Dyn *));
static void dynamic_segment_parisc_val
  PARAMS ((Elf_Internal_Dyn *));
static void dynamic_segment_ia64_val
  PARAMS ((Elf_Internal_Dyn *));
static int process_dynamic_segment
  PARAMS ((FILE *));
static int process_symbol_table
  PARAMS ((FILE *));
static int process_syminfo
  PARAMS ((FILE *));
static int process_section_contents
  PARAMS ((FILE *));
static int process_mips_specific
  PARAMS ((FILE *));
static int process_file
  PARAMS ((char *));
static int process_relocs
  PARAMS ((FILE *));
static int process_version_sections
  PARAMS ((FILE *));
static char *get_ver_flags
  PARAMS ((unsigned int));
static int get_32bit_section_headers
  PARAMS ((FILE *, unsigned int));
static int get_64bit_section_headers
  PARAMS ((FILE *, unsigned int));
static int get_32bit_program_headers
  PARAMS ((FILE *, Elf_Internal_Phdr *));
static int get_64bit_program_headers
  PARAMS ((FILE *, Elf_Internal_Phdr *));
static int get_file_header
  PARAMS ((FILE *));
static Elf_Internal_Sym *get_32bit_elf_symbols
  PARAMS ((FILE *, Elf_Internal_Shdr *));
static Elf_Internal_Sym *get_64bit_elf_symbols
  PARAMS ((FILE *, Elf_Internal_Shdr *));
static const char *get_elf_section_flags
  PARAMS ((bfd_vma));
static int *get_dynamic_data
  PARAMS ((FILE *, unsigned int));
static int get_32bit_dynamic_segment
  PARAMS ((FILE *));
static int get_64bit_dynamic_segment
  PARAMS ((FILE *));
#ifdef SUPPORT_DISASSEMBLY
static int disassemble_section
  PARAMS ((Elf_Internal_Shdr *, FILE *));
#endif
static int dump_section
  PARAMS ((Elf_Internal_Shdr *, FILE *));
static int display_debug_section
  PARAMS ((Elf_Internal_Shdr *, FILE *));
static int display_debug_info
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_not_supported
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int prescan_debug_info
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_lines
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_pubnames
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_abbrev
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_aranges
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_frames
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_macinfo
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_str
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static int display_debug_loc
  PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
static unsigned char *process_abbrev_section
  PARAMS ((unsigned char *, unsigned char *));
static void load_debug_str
  PARAMS ((FILE *));
static void free_debug_str
  PARAMS ((void));
static const char *fetch_indirect_string
  PARAMS ((unsigned long));
static void load_debug_loc
  PARAMS ((FILE *));
static void free_debug_loc
  PARAMS ((void));
static unsigned long read_leb128
  PARAMS ((unsigned char *, int *, int));
static int process_extended_line_op
  PARAMS ((unsigned char *, int, int));
static void reset_state_machine
  PARAMS ((int));
//char *get_TAG_name
//  PARAMS ((unsigned long)); // PG don't make this static since typedata.c needs it - put it in typedata.h instead
static char *get_AT_name
  PARAMS ((unsigned long));
static char *get_FORM_name
  PARAMS ((unsigned long));
static void free_abbrevs
  PARAMS ((void));
static void add_abbrev
  PARAMS ((unsigned long, unsigned long, int));
static void add_abbrev_attr
  PARAMS ((unsigned long, unsigned long));
static unsigned char *read_and_display_attr
  PARAMS ((unsigned long, unsigned long, unsigned char *, unsigned long,
	   unsigned long, unsigned long, int, dwarf_entry*, char));
static unsigned char *read_and_display_attr_value
  PARAMS ((unsigned long, unsigned long, unsigned char *, unsigned long,
	   unsigned long, unsigned long, int, dwarf_entry*, char));
static unsigned char *display_block
  PARAMS ((unsigned char *, unsigned long, char));
static void decode_location_expression
  PARAMS ((unsigned char *, unsigned int, unsigned long, char, dwarf_entry*, location_list* ll));
static void request_dump
  PARAMS ((unsigned int, int));
static const char *get_elf_class
  PARAMS ((unsigned int));
static const char *get_data_encoding
  PARAMS ((unsigned int));
static const char *get_osabi_name
  PARAMS ((unsigned int));
static int guess_is_rela
  PARAMS ((unsigned long));
static const char *get_note_type
  PARAMS ((unsigned int));
static const char *get_netbsd_elfcore_note_type
  PARAMS ((unsigned int));
static int process_note
  PARAMS ((Elf_Internal_Note *));
static int process_corefile_note_segment
  PARAMS ((FILE *, bfd_vma, bfd_vma));
static int process_corefile_note_segments
  PARAMS ((FILE *));
static int process_corefile_contents
  PARAMS ((FILE *));
static int process_arch_specific
  PARAMS ((FILE *));
static int process_gnu_liblist
  PARAMS ((FILE *));


typedef int Elf32_Word;

#define UNKNOWN -1

#define SECTION_NAME(X)	((X) == NULL ? "<none>" : \
				 ((X)->sh_name >= string_table_length \
				  ? "<corrupt>" : string_table + (X)->sh_name))

/* Given st_shndx I, map to section_headers index.  */
#define SECTION_HEADER_INDEX(I)				\
  ((I) < SHN_LORESERVE					\
   ? (I)						\
   : ((I) <= SHN_HIRESERVE				\
      ? 0						\
      : (I) - (SHN_HIRESERVE + 1 - SHN_LORESERVE)))

/* Reverse of the above.  */
#define SECTION_HEADER_NUM(N)				\
  ((N) < SHN_LORESERVE					\
   ? (N)						\
   : (N) + (SHN_HIRESERVE + 1 - SHN_LORESERVE))

#define SECTION_HEADER(I) (section_headers + SECTION_HEADER_INDEX (I))

#define DT_VERSIONTAGIDX(tag)	(DT_VERNEEDNUM - (tag))	/* Reverse order!  */

#define BYTE_GET(field)	byte_get (field, sizeof (field))

/* If we can support a 64 bit data type then BFD64 should be defined
   and sizeof (bfd_vma) == 8.  In this case when translating from an
   external 8 byte field to an internal field, we can assume that the
   internal field is also 8 bytes wide and so we can extract all the data.
   If, however, BFD64 is not defined, then we must assume that the
   internal data structure only has 4 byte wide fields that are the
   equivalent of the 8 byte wide external counterparts, and so we must
   truncate the data.  */
#ifdef  BFD64
#define BYTE_GET8(field)	byte_get (field, -8)
#else
#define BYTE_GET8(field)	byte_get (field, 8)
#endif

#define NUM_ELEM(array) 	(sizeof (array) / sizeof ((array)[0]))

#define GET_ELF_SYMBOLS(file, section)			\
  (is_32bit_elf ? get_32bit_elf_symbols (file, section)	\
   : get_64bit_elf_symbols (file, section))

// PG - begin custom libiberty.a functions

PTR xmalloc (size_t size)
{
  return VG_(malloc)("readelf.c: xmalloc", size);
}

PTR xrealloc (PTR oldmem, size_t size)
{
  return VG_(realloc)("readelf.c: xrealloc", oldmem, size);
}

#define ARRAY_SIZE(a) (sizeof (a) / sizeof ((a)[0]))

// PG - end

static void
error VPARAMS ((const char *message, ...))
{
  VA_OPEN (args, message);
  VA_FIXEDARG (args, const char *, message);

  fprintf (stderr, _("%s: Error: "), program_name);
  vfprintf (stderr, message, args);
  VA_CLOSE (args);
}

static void
warn VPARAMS ((const char *message, ...))
{
  VA_OPEN (args, message);
  VA_FIXEDARG (args, const char *, message);

  fprintf (stderr, _("%s: Warning: "), program_name);
  vfprintf (stderr, message, args);
  VA_CLOSE (args);
}

static PTR get_data PARAMS ((PTR, FILE *, long, size_t, const char *));

static PTR
get_data (var, file, offset, size, reason)
     PTR var;
     FILE *file;
     long offset;
     size_t size;
     const char *reason;
{
  PTR mvar;

  if (size == 0)
    return NULL;

  if (fseek (file, offset, SEEK_SET))
    {
      error (_("Unable to seek to %x for %s\n"), offset, reason);
      return NULL;
    }

  mvar = var;
  if (mvar == NULL)
    {
      mvar = (PTR) VG_(malloc) ("readelf.c: get_data", size);

      if (mvar == NULL)
	{
	  error (_("Out of memory allocating %d bytes for %s\n"),
		 size, reason);
	  return NULL;
	}
    }

  if (fread (mvar, size, 1, file) != 1)
    {
      error (_("Unable to read in %d bytes of %s\n"), size, reason);
      if (mvar != var)
	VG_(free) (mvar);
      return NULL;
    }

  return mvar;
}

static bfd_vma
byte_get_little_endian (field, size)
     unsigned char *field;
     int size;
{
  switch (size)
    {
    case 1:
      return *field;

    case 2:
      return  ((unsigned int) (field[0]))
	|    (((unsigned int) (field[1])) << 8);

#ifndef BFD64
    case 8:
      /* We want to extract data from an 8 byte wide field and
	 place it into a 4 byte wide field.  Since this is a little
	 endian source we can just use the 4 byte extraction code.  */
      /* Fall through.  */
#endif
    case 4:
      return  ((unsigned long) (field[0]))
	|    (((unsigned long) (field[1])) << 8)
	|    (((unsigned long) (field[2])) << 16)
	|    (((unsigned long) (field[3])) << 24);

#ifdef BFD64
    case 8:
    case -8:
      /* This is a special case, generated by the BYTE_GET8 macro.
	 It means that we are loading an 8 byte value from a field
	 in an external structure into an 8 byte value in a field
	 in an internal strcuture.  */
      return  ((bfd_vma) (field[0]))
	|    (((bfd_vma) (field[1])) << 8)
	|    (((bfd_vma) (field[2])) << 16)
	|    (((bfd_vma) (field[3])) << 24)
	|    (((bfd_vma) (field[4])) << 32)
	|    (((bfd_vma) (field[5])) << 40)
	|    (((bfd_vma) (field[6])) << 48)
	|    (((bfd_vma) (field[7])) << 56);
#endif
    default:
      error (_("Unhandled data length: %d\n"), size);
      abort ();
    }
}

static void
byte_put_little_endian (field, value, size)
     unsigned char * field;
     bfd_vma	     value;
     int             size;
{
  switch (size)
    {
    case 8:
      field[7] = (((value >> 24) >> 24) >> 8) & 0xff;
      field[6] = ((value >> 24) >> 24) & 0xff;
      field[5] = ((value >> 24) >> 16) & 0xff;
      field[4] = ((value >> 24) >> 8) & 0xff;
      /* Fall through.  */
    case 4:
      field[3] = (value >> 24) & 0xff;
      field[2] = (value >> 16) & 0xff;
      /* Fall through.  */
    case 2:
      field[1] = (value >> 8) & 0xff;
      /* Fall through.  */
    case 1:
      field[0] = value & 0xff;
      break;

    default:
      error (_("Unhandled data length: %d\n"), size);
      abort ();
    }
}

/* Print a VMA value.  */
static void
print_vma (vma, mode)
     bfd_vma vma;
     print_mode mode;
{
#ifdef BFD64
  if (is_32bit_elf)
#endif
    {
      switch (mode)
	{
	case FULL_HEX: FJALAR_DPRINTF ("0x"); /* drop through */
	case LONG_HEX: FJALAR_DPRINTF ("%8.8lx", (unsigned long) vma); break;
	case PREFIX_HEX: FJALAR_DPRINTF ("0x"); /* drop through */
	case HEX: FJALAR_DPRINTF ("%lx", (unsigned long) vma); break;
	case DEC: FJALAR_DPRINTF ("%ld", (unsigned long) vma); break;
	case DEC_5: FJALAR_DPRINTF ("%5ld", (long) vma); break;
	case UNSIGNED: FJALAR_DPRINTF ("%lu", (unsigned long) vma); break;
	}
    }
#ifdef BFD64
  else
    {
      switch (mode)
	{
	case FULL_HEX:
	  FJALAR_DPRINTF ("0x");
	  /* drop through */

	case LONG_HEX:
	  printf_vma (vma);
	  break;

	case PREFIX_HEX:
	  FJALAR_DPRINTF ("0x");
	  /* drop through */

	case HEX:
#if BFD_HOST_64BIT_LONG
	  FJALAR_DPRINTF ("%lx", vma);
#else
	  if (_bfd_int64_high (vma))
	    FJALAR_DPRINTF ("%lx%8.8lx", _bfd_int64_high (vma), _bfd_int64_low (vma));
	  else
	    FJALAR_DPRINTF ("%lx", _bfd_int64_low (vma));
#endif
	  break;

	case DEC:
#if BFD_HOST_64BIT_LONG
	  FJALAR_DPRINTF ("%ld", vma);
#else
	  if (_bfd_int64_high (vma))
	    /* ugg */
	    FJALAR_DPRINTF ("++%ld", _bfd_int64_low (vma));
	  else
	    FJALAR_DPRINTF ("%ld", _bfd_int64_low (vma));
#endif
	  break;

	case DEC_5:
#if BFD_HOST_64BIT_LONG
	  FJALAR_DPRINTF ("%5ld", vma);
#else
	  if (_bfd_int64_high (vma))
	    /* ugg */
	    FJALAR_DPRINTF ("++%ld", _bfd_int64_low (vma));
	  else
	    FJALAR_DPRINTF ("%5ld", _bfd_int64_low (vma));
#endif
	  break;

	case UNSIGNED:
#if BFD_HOST_64BIT_LONG
	  FJALAR_DPRINTF ("%lu", vma);
#else
	  if (_bfd_int64_high (vma))
	    /* ugg */
	    FJALAR_DPRINTF ("++%lu", _bfd_int64_low (vma));
	  else
	    FJALAR_DPRINTF ("%lu", _bfd_int64_low (vma));
#endif
	  break;
	}
    }
#endif
}

/* Display a symbol on stdout.  If do_wide is not true then
   format the symbol to be at most WIDTH characters,
   truncating as necessary.  If WIDTH is negative then
   format the string to be exactly - WIDTH characters,
   truncating or padding as necessary.  */

static void
print_symbol (width, symbol)
     int width;
     const char *symbol;
{
  if (do_wide)
    FJALAR_DPRINTF ("%s", symbol);
  else if (width < 0)
    FJALAR_DPRINTF ("%-*.*s", width, width, symbol);
  else
    FJALAR_DPRINTF ("%-.*s", width, symbol);
}

static bfd_vma
byte_get_big_endian (field, size)
     unsigned char *field;
     int size;
{
  switch (size)
    {
    case 1:
      return *field;

    case 2:
      return ((unsigned int) (field[1])) | (((int) (field[0])) << 8);

    case 4:
      return ((unsigned long) (field[3]))
	|   (((unsigned long) (field[2])) << 8)
	|   (((unsigned long) (field[1])) << 16)
	|   (((unsigned long) (field[0])) << 24);

#ifndef BFD64
    case 8:
      /* Although we are extracing data from an 8 byte wide field, we
	 are returning only 4 bytes of data.  */
      return ((unsigned long) (field[7]))
	|   (((unsigned long) (field[6])) << 8)
	|   (((unsigned long) (field[5])) << 16)
	|   (((unsigned long) (field[4])) << 24);
#else
    case 8:
    case -8:
      /* This is a special case, generated by the BYTE_GET8 macro.
	 It means that we are loading an 8 byte value from a field
	 in an external structure into an 8 byte value in a field
	 in an internal strcuture.  */
      return ((bfd_vma) (field[7]))
	|   (((bfd_vma) (field[6])) << 8)
	|   (((bfd_vma) (field[5])) << 16)
	|   (((bfd_vma) (field[4])) << 24)
	|   (((bfd_vma) (field[3])) << 32)
	|   (((bfd_vma) (field[2])) << 40)
	|   (((bfd_vma) (field[1])) << 48)
	|   (((bfd_vma) (field[0])) << 56);
#endif

    default:
      error (_("Unhandled data length: %d\n"), size);
      abort ();
    }
}

static void
byte_put_big_endian (field, value, size)
     unsigned char * field;
     bfd_vma	     value;
     int             size;
{
  switch (size)
    {
    case 8:
      field[7] = value & 0xff;
      field[6] = (value >> 8) & 0xff;
      field[5] = (value >> 16) & 0xff;
      field[4] = (value >> 24) & 0xff;
      value >>= 16;
      value >>= 16;
      /* Fall through.  */
    case 4:
      field[3] = value & 0xff;
      field[2] = (value >> 8) & 0xff;
      value >>= 16;
      /* Fall through.  */
    case 2:
      field[1] = value & 0xff;
      value >>= 8;
      /* Fall through.  */
    case 1:
      field[0] = value & 0xff;
      break;

    default:
      error (_("Unhandled data length: %d\n"), size);
      abort ();
    }
}

/* Guess the relocation size commonly used by the specific machines.  */

static int
guess_is_rela (e_machine)
     unsigned long e_machine;
{
  switch (e_machine)
    {
      /* Targets that use REL relocations.  */
    case EM_ARM:
    case EM_386:
    case EM_486:
    case EM_960:
    case EM_DLX:
    case EM_OPENRISC:
    case EM_OR32:
    case EM_M32R:
    case EM_CYGNUS_M32R:
    case EM_D10V:
    case EM_CYGNUS_D10V:
    case EM_MIPS:
    case EM_MIPS_RS3_LE:
      return FALSE;

      /* Targets that use RELA relocations.  */
    case EM_68K:
    case EM_H8_300:
    case EM_H8_300H:
    case EM_H8S:
    case EM_SPARC32PLUS:
    case EM_SPARCV9:
    case EM_SPARC:
    case EM_PPC:
    case EM_PPC64:
    case EM_V850:
    case EM_CYGNUS_V850:
    case EM_D30V:
    case EM_CYGNUS_D30V:
    case EM_MN10200:
    case EM_CYGNUS_MN10200:
    case EM_MN10300:
    case EM_CYGNUS_MN10300:
    case EM_FR30:
    case EM_CYGNUS_FR30:
    case EM_CYGNUS_FRV:
    case EM_SH:
    case EM_ALPHA:
    case EM_MCORE:
    case EM_IA_64:
    case EM_AVR:
    case EM_AVR_OLD:
    case EM_CRIS:
    case EM_860:
    case EM_X86_64:
    case EM_S390:
    case EM_S390_OLD:
    case EM_MMIX:
    case EM_MSP430:
    case EM_MSP430_OLD:
    case EM_XSTORMY16:
    case EM_VAX:
    case EM_IP2K:
    case EM_IP2K_OLD:
    case EM_IQ2000:
    case EM_XTENSA:
    case EM_XTENSA_OLD:
      return TRUE;

    case EM_MMA:
    case EM_PCP:
    case EM_NCPU:
    case EM_NDR1:
    case EM_STARCORE:
    case EM_ME16:
    case EM_ST100:
    case EM_TINYJ:
    case EM_FX66:
    case EM_ST9PLUS:
    case EM_ST7:
    case EM_68HC16:
    case EM_68HC11:
    case EM_68HC08:
    case EM_68HC05:
    case EM_SVX:
    case EM_ST19:
    default:
      warn (_("Don't know about relocations on this machine architecture\n"));
      return FALSE;
    }
}

static int
slurp_rela_relocs (file, rel_offset, rel_size, relasp, nrelasp)
     FILE *file;
     unsigned long rel_offset;
     unsigned long rel_size;
     Elf_Internal_Rela **relasp;
     unsigned long *nrelasp;
{
  Elf_Internal_Rela *relas;
  unsigned long nrelas;
  unsigned int i;

  if (is_32bit_elf)
    {
      Elf32_External_Rela *erelas;

      erelas = (Elf32_External_Rela *) get_data (NULL, file, rel_offset,
						 rel_size, _("relocs"));
      if (!erelas)
	return 0;

      nrelas = rel_size / sizeof (Elf32_External_Rela);

      relas = (Elf_Internal_Rela *)
	VG_(malloc) ("readelf.c: slurp_rela_relocs", nrelas * sizeof (Elf_Internal_Rela));

      if (relas == NULL)
	{
	  error(_("out of memory parsing relocs"));
	  return 0;
	}

      for (i = 0; i < nrelas; i++)
	{
	  relas[i].r_offset = BYTE_GET (erelas[i].r_offset);
	  relas[i].r_info   = BYTE_GET (erelas[i].r_info);
	  relas[i].r_addend = BYTE_GET (erelas[i].r_addend);
	}

      VG_(free) (erelas);
    }
  else
    {
      Elf64_External_Rela *erelas;

      erelas = (Elf64_External_Rela *) get_data (NULL, file, rel_offset,
						 rel_size, _("relocs"));
      if (!erelas)
	return 0;

      nrelas = rel_size / sizeof (Elf64_External_Rela);

      relas = (Elf_Internal_Rela *)
	VG_(malloc) ("readelf.c: slurp_rela_relocs.2", nrelas * sizeof (Elf_Internal_Rela));

      if (relas == NULL)
	{
	  error(_("out of memory parsing relocs"));
	  return 0;
	}

      for (i = 0; i < nrelas; i++)
	{
	  relas[i].r_offset = BYTE_GET8 (erelas[i].r_offset);
	  relas[i].r_info   = BYTE_GET8 (erelas[i].r_info);
	  relas[i].r_addend = BYTE_GET8 (erelas[i].r_addend);
	}

      VG_(free) (erelas);
    }
  *relasp = relas;
  *nrelasp = nrelas;
  return 1;
}

static int
slurp_rel_relocs (file, rel_offset, rel_size, relsp, nrelsp)
     FILE *file;
     unsigned long rel_offset;
     unsigned long rel_size;
     Elf_Internal_Rela **relsp;
     unsigned long *nrelsp;
{
  Elf_Internal_Rela *rels;
  unsigned long nrels;
  unsigned int i;

  if (is_32bit_elf)
    {
      Elf32_External_Rel *erels;

      erels = (Elf32_External_Rel *) get_data (NULL, file, rel_offset,
					       rel_size, _("relocs"));
      if (!erels)
	return 0;

      nrels = rel_size / sizeof (Elf32_External_Rel);

      rels = (Elf_Internal_Rela *) VG_(malloc) ("readelf.c: slurp_rel_relocs", nrels * sizeof (Elf_Internal_Rela));

      if (rels == NULL)
	{
	  error(_("out of memory parsing relocs"));
	  return 0;
	}

      for (i = 0; i < nrels; i++)
	{
	  rels[i].r_offset = BYTE_GET (erels[i].r_offset);
	  rels[i].r_info   = BYTE_GET (erels[i].r_info);
	  rels[i].r_addend = 0;
	}

      VG_(free) (erels);
    }
  else
    {
      Elf64_External_Rel *erels;

      erels = (Elf64_External_Rel *) get_data (NULL, file, rel_offset,
					       rel_size, _("relocs"));
      if (!erels)
	return 0;

      nrels = rel_size / sizeof (Elf64_External_Rel);

      rels = (Elf_Internal_Rela *) VG_(malloc) ("readelf.c: slurp_rel_relocs.2", nrels * sizeof (Elf_Internal_Rela));

      if (rels == NULL)
	{
	  error(_("out of memory parsing relocs"));
	  return 0;
	}

      for (i = 0; i < nrels; i++)
	{
	  rels[i].r_offset = BYTE_GET8 (erels[i].r_offset);
	  rels[i].r_info   = BYTE_GET8 (erels[i].r_info);
	  rels[i].r_addend = 0;
	}

      VG_(free) (erels);
    }
  *relsp = rels;
  *nrelsp = nrels;
  return 1;
}

/* Display the contents of the relocation data found at the specified offset.  */

static int
dump_relocations (file, rel_offset, rel_size, symtab, nsyms, strtab, is_rela)
     FILE *file;
     unsigned long rel_offset;
     unsigned long rel_size;
     Elf_Internal_Sym *symtab;
     unsigned long nsyms;
     char *strtab;
     int is_rela;
{
  unsigned int i;
  Elf_Internal_Rela *rels;


  if (is_rela == UNKNOWN)
    is_rela = guess_is_rela (elf_header.e_machine);

  if (is_rela)
    {
      if (!slurp_rela_relocs (file, rel_offset, rel_size, &rels, &rel_size))
	return 0;
    }
  else
    {
      if (!slurp_rel_relocs (file, rel_offset, rel_size, &rels, &rel_size))
	return 0;
    }

  if (is_32bit_elf)
    {
      if (is_rela)
	{
	  if (do_wide)
	    FJALAR_DPRINTF (_(" Offset     Info    Type                Sym. Value  Symbol's Name + Addend\n"));
	  else
	    FJALAR_DPRINTF (_(" Offset     Info    Type            Sym.Value  Sym. Name + Addend\n"));
	}
      else
	{
	  if (do_wide)
	    FJALAR_DPRINTF (_(" Offset     Info    Type                Sym. Value  Symbol's Name\n"));
	  else
	    FJALAR_DPRINTF (_(" Offset     Info    Type            Sym.Value  Sym. Name\n"));
	}
    }
  else
    {
      if (is_rela)
	{
	  if (do_wide)
	    FJALAR_DPRINTF (_("    Offset             Info             Type               Symbol's Value  Symbol's Name + Addend\n"));
	  else
	    FJALAR_DPRINTF (_("  Offset          Info           Type           Sym. Value    Sym. Name + Addend\n"));
	}
      else
	{
	  if (do_wide)
	    FJALAR_DPRINTF (_("    Offset             Info             Type               Symbol's Value  Symbol's Name\n"));
	  else
	    FJALAR_DPRINTF (_("  Offset          Info           Type           Sym. Value    Sym. Name\n"));
	}
    }

  for (i = 0; i < rel_size; i++)
    {
      const char *rtype;
      bfd_vma offset;
      bfd_vma info;
      bfd_vma symtab_index;
      bfd_vma type;

      offset = rels[i].r_offset;
      info   = rels[i].r_info;

      if (is_32bit_elf)
	{
	  type         = ELF32_R_TYPE (info);
	  symtab_index = ELF32_R_SYM  (info);
	}
      else
	{
	  /* The #ifdef BFD64 below is to prevent a compile time warning.
	     We know that if we do not have a 64 bit data type that we
	     will never execute this code anyway.  */
#ifdef BFD64
          type = ELF64_R_TYPE (info);

	  symtab_index = ELF64_R_SYM  (info);
#endif
	}

      if (is_32bit_elf)
	{
#ifdef _bfd_int64_low
	  FJALAR_DPRINTF ("%8.8lx  %8.8lx ", _bfd_int64_low (offset), _bfd_int64_low (info));
#else
	  FJALAR_DPRINTF ("%8.8lx  %8.8lx ", offset, info);
#endif
	}
      else
	{
#ifdef _bfd_int64_low
	  FJALAR_DPRINTF (do_wide
		  ? "%8.8lx%8.8lx  %8.8lx%8.8lx "
		  : "%4.4lx%8.8lx  %4.4lx%8.8lx ",
		  _bfd_int64_high (offset),
		  _bfd_int64_low (offset),
		  _bfd_int64_high (info),
		  _bfd_int64_low (info));
#else
	  FJALAR_DPRINTF (do_wide
		  ? "%16.16lx  %16.16lx "
		  : "%12.12lx  %12.12lx ",
		  offset, info);
#endif
	}

      switch (elf_header.e_machine)
	{
	default:
	  rtype = NULL;
	  break;

	case EM_386:
	case EM_486:
	  rtype = elf_i386_reloc_type (type);
	  break;

	}

      if (rtype == NULL)
#ifdef _bfd_int64_low
 FJALAR_DPRINTF (_("unrecognized: %-7lx"), _bfd_int64_low (type));
#else
 FJALAR_DPRINTF (_("unrecognized: %-7lx"), type);
#endif
      else
 FJALAR_DPRINTF (do_wide ? "%-22.22s" : "%-17.17s", rtype);

      if (symtab_index)
	{
	  if (symtab == NULL || symtab_index >= nsyms)
	    FJALAR_DPRINTF (" bad symbol index: %08lx", (unsigned long) symtab_index);
	  else
	    {
	      Elf_Internal_Sym *psym;

	      psym = symtab + symtab_index;

	      FJALAR_DPRINTF (" ");
	      print_vma (psym->st_value, LONG_HEX);
	      FJALAR_DPRINTF (is_32bit_elf ? "   " : " ");

	      if (psym->st_name == 0)
		{
		  const char *sec_name = "<null>";
		  char name_buf[40];

		  if (ELF_ST_TYPE (psym->st_info) == STT_SECTION)
		    {
		      bfd_vma sec_index = (bfd_vma) -1;

		      if (psym->st_shndx < SHN_LORESERVE)
			sec_index = psym->st_shndx;
		      else if (psym->st_shndx > SHN_LORESERVE)
			sec_index = psym->st_shndx - (SHN_HIRESERVE + 1
						      - SHN_LORESERVE);

		      if (sec_index != (bfd_vma) -1)
			sec_name = SECTION_NAME (section_headers + sec_index);
		      else if (psym->st_shndx == SHN_ABS)
			sec_name = "ABS";
		      else if (psym->st_shndx == SHN_COMMON)
			sec_name = "COMMON";
		      else
			{
			  sprintf (name_buf, "<section 0x%x>",
				   (unsigned int) psym->st_shndx);
			  sec_name = name_buf;
			}
		    }
		  print_symbol (22, sec_name);
		}
	      else if (strtab == NULL)
	 FJALAR_DPRINTF (_("<string table index %3ld>"), psym->st_name);
	      else
		print_symbol (22, strtab + psym->st_name);

	      if (is_rela)
	 FJALAR_DPRINTF (" + %lx", (unsigned long) rels[i].r_addend);
	    }
	}
      else if (is_rela)
	{
	  FJALAR_DPRINTF ("%*c", is_32bit_elf ? (do_wide ? 34 : 28) : (do_wide ? 26 : 20), ' ');
	  print_vma (rels[i].r_addend, LONG_HEX);
	}

      putchar ('\n');

    }

  VG_(free) (rels);

  return 1;
}

static const char *
get_mips_dynamic_type (type)
     unsigned long type;
{
  switch (type)
    {
    default:
      return NULL;
    }
}

static const char *
get_sparc64_dynamic_type (type)
     unsigned long type;
{
  switch (type)
    {
    default:
      return NULL;
    }
}

static const char *
get_ppc64_dynamic_type (type)
     unsigned long type;
{
  switch (type)
    {
    default:
      return NULL;
    }
}

static const char *
get_parisc_dynamic_type (type)
     unsigned long type;
{
  switch (type)
    {
    default:
      return NULL;
    }
}

static const char *
get_ia64_dynamic_type (type)
     unsigned long type;
{
  switch (type)
    {
    default:
      return NULL;
    }
}

static const char *
get_dynamic_type (type)
     unsigned long type;
{
  static char buff[32];

  switch (type)
    {
    case DT_NULL:	return "NULL";
    case DT_NEEDED:	return "NEEDED";
    case DT_PLTRELSZ:	return "PLTRELSZ";
    case DT_PLTGOT:	return "PLTGOT";
    case DT_HASH:	return "HASH";
    case DT_STRTAB:	return "STRTAB";
    case DT_SYMTAB:	return "SYMTAB";
    case DT_RELA:	return "RELA";
    case DT_RELASZ:	return "RELASZ";
    case DT_RELAENT:	return "RELAENT";
    case DT_STRSZ:	return "STRSZ";
    case DT_SYMENT:	return "SYMENT";
    case DT_INIT:	return "INIT";
    case DT_FINI:	return "FINI";
    case DT_SONAME:	return "SONAME";
    case DT_RPATH:	return "RPATH";
    case DT_SYMBOLIC:	return "SYMBOLIC";
    case DT_REL:	return "REL";
    case DT_RELSZ:	return "RELSZ";
    case DT_RELENT:	return "RELENT";
    case DT_PLTREL:	return "PLTREL";
    case DT_DEBUG:	return "DEBUG";
    case DT_TEXTREL:	return "TEXTREL";
    case DT_JMPREL:	return "JMPREL";
    case DT_BIND_NOW:   return "BIND_NOW";
    case DT_INIT_ARRAY: return "INIT_ARRAY";
    case DT_FINI_ARRAY: return "FINI_ARRAY";
    case DT_INIT_ARRAYSZ: return "INIT_ARRAYSZ";
    case DT_FINI_ARRAYSZ: return "FINI_ARRAYSZ";
    case DT_RUNPATH:    return "RUNPATH";
    case DT_FLAGS:      return "FLAGS";

    case DT_PREINIT_ARRAY: return "PREINIT_ARRAY";
    case DT_PREINIT_ARRAYSZ: return "PREINIT_ARRAYSZ";

    case DT_CHECKSUM:	return "CHECKSUM";
    case DT_PLTPADSZ:	return "PLTPADSZ";
    case DT_MOVEENT:	return "MOVEENT";
    case DT_MOVESZ:	return "MOVESZ";
    case DT_FEATURE:	return "FEATURE";
    case DT_POSFLAG_1:	return "POSFLAG_1";
    case DT_SYMINSZ:	return "SYMINSZ";
    case DT_SYMINENT:	return "SYMINENT"; /* aka VALRNGHI */

    case DT_ADDRRNGLO:  return "ADDRRNGLO";
    case DT_CONFIG:	return "CONFIG";
    case DT_DEPAUDIT:	return "DEPAUDIT";
    case DT_AUDIT:	return "AUDIT";
    case DT_PLTPAD:	return "PLTPAD";
    case DT_MOVETAB:	return "MOVETAB";
    case DT_SYMINFO:	return "SYMINFO"; /* aka ADDRRNGHI */

    case DT_VERSYM:	return "VERSYM";

    case DT_RELACOUNT:	return "RELACOUNT";
    case DT_RELCOUNT:	return "RELCOUNT";
    case DT_FLAGS_1:	return "FLAGS_1";
    case DT_VERDEF:	return "VERDEF";
    case DT_VERDEFNUM:	return "VERDEFNUM";
    case DT_VERNEED:	return "VERNEED";
    case DT_VERNEEDNUM:	return "VERNEEDNUM";

    case DT_AUXILIARY:	return "AUXILIARY";
    case DT_USED:	return "USED";
    case DT_FILTER:	return "FILTER";

    case DT_GNU_PRELINKED: return "GNU_PRELINKED";
    case DT_GNU_CONFLICT: return "GNU_CONFLICT";
    case DT_GNU_CONFLICTSZ: return "GNU_CONFLICTSZ";
    case DT_GNU_LIBLIST: return "GNU_LIBLIST";
    case DT_GNU_LIBLISTSZ: return "GNU_LIBLISTSZ";

    default:
      if ((type >= DT_LOPROC) && (type <= DT_HIPROC))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    case EM_MIPS:
	    case EM_MIPS_RS3_LE:
	      result = get_mips_dynamic_type (type);
	      break;
	    case EM_SPARCV9:
	      result = get_sparc64_dynamic_type (type);
	      break;
	    case EM_PPC64:
	      result = get_ppc64_dynamic_type (type);
	      break;
	    case EM_IA_64:
	      result = get_ia64_dynamic_type (type);
	      break;
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  sprintf (buff, _("Processor Specific: %lx"), type);
	}
      else if ((type >= DT_LOOS) && (type <= DT_HIOS))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    case EM_PARISC:
	      result = get_parisc_dynamic_type (type);
	      break;
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  sprintf (buff, _("Operating System specific: %lx"), type);
	}
      else
	sprintf (buff, _("<unknown>: %lx"), type);

      return buff;
    }
}

static char *
get_file_type (e_type)
     unsigned e_type;
{
  static char buff[32];

  switch (e_type)
    {
    case ET_NONE:	return _("NONE (None)");
    case ET_REL:	return _("REL (Relocatable file)");
    case ET_EXEC:       return _("EXEC (Executable file)");
    case ET_DYN:        return _("DYN (Shared object file)");
    case ET_CORE:       return _("CORE (Core file)");

    default:
      if ((e_type >= ET_LOPROC) && (e_type <= ET_HIPROC))
	sprintf (buff, _("Processor Specific: (%x)"), e_type);
      else if ((e_type >= ET_LOOS) && (e_type <= ET_HIOS))
	sprintf (buff, _("OS Specific: (%x)"), e_type);
      else
	sprintf (buff, _("<unknown>: %x"), e_type);
      return buff;
    }
}

static char *
get_machine_name (e_machine)
     unsigned e_machine;
{
  static char buff[64]; /* XXX */

  switch (e_machine)
    {
    case EM_NONE:		return _("None");
    case EM_M32:		return "WE32100";
    case EM_SPARC:		return "Sparc";
    case EM_386:		return "Intel 80386";
    case EM_68K:		return "MC68000";
    case EM_88K:		return "MC88000";
    case EM_486:		return "Intel 80486";
    case EM_860:		return "Intel 80860";
    case EM_MIPS:		return "MIPS R3000";
    case EM_S370:		return "IBM System/370";
    case EM_MIPS_RS3_LE:	return "MIPS R4000 big-endian";
    case EM_OLD_SPARCV9:	return "Sparc v9 (old)";
    case EM_PARISC:		return "HPPA";
    case EM_PPC_OLD:		return "Power PC (old)";
    case EM_SPARC32PLUS:	return "Sparc v8+" ;
    case EM_960:		return "Intel 90860";
    case EM_PPC:		return "PowerPC";
    case EM_PPC64:		return "PowerPC64";
    case EM_V800:		return "NEC V800";
    case EM_FR20:		return "Fujitsu FR20";
    case EM_RH32:		return "TRW RH32";
    case EM_MCORE:		return "MCORE";
    case EM_ARM:		return "ARM";
    case EM_OLD_ALPHA:		return "Digital Alpha (old)";
    case EM_SH:			return "Renesas / SuperH SH";
    case EM_SPARCV9:		return "Sparc v9";
    case EM_TRICORE:		return "Siemens Tricore";
    case EM_ARC:		return "ARC";
    case EM_H8_300:		return "Renesas H8/300";
    case EM_H8_300H:		return "Renesas H8/300H";
    case EM_H8S:		return "Renesas H8S";
    case EM_H8_500:		return "Renesas H8/500";
    case EM_IA_64:		return "Intel IA-64";
    case EM_MIPS_X:		return "Stanford MIPS-X";
    case EM_COLDFIRE:		return "Motorola Coldfire";
    case EM_68HC12:		return "Motorola M68HC12";
    case EM_ALPHA:		return "Alpha";
    case EM_CYGNUS_D10V:
    case EM_D10V:		return "d10v";
    case EM_CYGNUS_D30V:
    case EM_D30V:		return "d30v";
    case EM_CYGNUS_M32R:
    case EM_M32R:		return "Renesas M32R (formerly Mitsubishi M32r)";
    case EM_CYGNUS_V850:
    case EM_V850:		return "NEC v850";
    case EM_CYGNUS_MN10300:
    case EM_MN10300:		return "mn10300";
    case EM_CYGNUS_MN10200:
    case EM_MN10200:		return "mn10200";
    case EM_CYGNUS_FR30:
    case EM_FR30:		return "Fujitsu FR30";
    case EM_CYGNUS_FRV:		return "Fujitsu FR-V";
    case EM_PJ_OLD:
    case EM_PJ:			return "picoJava";
    case EM_MMA:		return "Fujitsu Multimedia Accelerator";
    case EM_PCP:		return "Siemens PCP";
    case EM_NCPU:		return "Sony nCPU embedded RISC processor";
    case EM_NDR1:		return "Denso NDR1 microprocesspr";
    case EM_STARCORE:		return "Motorola Star*Core processor";
    case EM_ME16:		return "Toyota ME16 processor";
    case EM_ST100:		return "STMicroelectronics ST100 processor";
    case EM_TINYJ:		return "Advanced Logic Corp. TinyJ embedded processor";
    case EM_FX66:		return "Siemens FX66 microcontroller";
    case EM_ST9PLUS:		return "STMicroelectronics ST9+ 8/16 bit microcontroller";
    case EM_ST7:		return "STMicroelectronics ST7 8-bit microcontroller";
    case EM_68HC16:		return "Motorola MC68HC16 Microcontroller";
    case EM_68HC11:		return "Motorola MC68HC11 Microcontroller";
    case EM_68HC08:		return "Motorola MC68HC08 Microcontroller";
    case EM_68HC05:		return "Motorola MC68HC05 Microcontroller";
    case EM_SVX:		return "Silicon Graphics SVx";
    case EM_ST19:		return "STMicroelectronics ST19 8-bit microcontroller";
    case EM_VAX:		return "Digital VAX";
    case EM_AVR_OLD:
    case EM_AVR:		return "Atmel AVR 8-bit microcontroller";
    case EM_CRIS:		return "Axis Communications 32-bit embedded processor";
    case EM_JAVELIN:		return "Infineon Technologies 32-bit embedded cpu";
    case EM_FIREPATH:		return "Element 14 64-bit DSP processor";
    case EM_ZSP:		return "LSI Logic's 16-bit DSP processor";
    case EM_MMIX:		return "Donald Knuth's educational 64-bit processor";
    case EM_HUANY:		return "Harvard Universitys's machine-independent object format";
    case EM_PRISM:		return "Vitesse Prism";
    case EM_X86_64:		return "Advanced Micro Devices X86-64";
    case EM_S390_OLD:
    case EM_S390:		return "IBM S/390";
    case EM_XSTORMY16:		return "Sanyo Xstormy16 CPU core";
    case EM_OPENRISC:
    case EM_OR32:		return "OpenRISC";
    case EM_DLX:		return "OpenDLX";
    case EM_IP2K_OLD:
    case EM_IP2K:		return "Ubicom IP2xxx 8-bit microcontrollers";
    case EM_IQ2000:       	return "Vitesse IQ2000";
    case EM_XTENSA_OLD:
    case EM_XTENSA:		return "Tensilica Xtensa Processor";
    default:
      sprintf (buff, _("<unknown>: %x"), e_machine);
      return buff;
    }
}

static char *
get_machine_flags (e_flags, e_machine)
     unsigned e_flags;
     unsigned e_machine;
{
  static char buf[1024];

  (void)e_flags; (void)e_machine; /* Quiet unused variable warning */
  buf[0] = '\0';
  return buf;
}

static const char *
get_mips_segment_type (type)
     unsigned long type;
{
  (void)type; /* Quiet unused variable warning */
  return NULL;
}

static const char *
get_parisc_segment_type (type)
     unsigned long type;
{
  (void)type; /* Quiet unused variable warning */
  return NULL;
}

static const char *
get_ia64_segment_type (type)
     unsigned long type;
{
  (void)type; /* Quiet unused variable warning */
  return NULL;
}

static const char *
get_segment_type (p_type)
     unsigned long p_type;
{
  static char buff[32];

  switch (p_type)
    {
    case PT_NULL:	return "NULL";
    case PT_LOAD:	return "LOAD";
    case PT_DYNAMIC:	return "DYNAMIC";
    case PT_INTERP:	return "INTERP";
    case PT_NOTE:	return "NOTE";
    case PT_SHLIB:	return "SHLIB";
    case PT_PHDR:	return "PHDR";
    case PT_TLS:	return "TLS";

    case PT_GNU_EH_FRAME:
			return "GNU_EH_FRAME";

    default:
      if ((p_type >= PT_LOPROC) && (p_type <= PT_HIPROC))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    case EM_MIPS:
	    case EM_MIPS_RS3_LE:
	      result = get_mips_segment_type (p_type);
	      break;
	    case EM_PARISC:
	      result = get_parisc_segment_type (p_type);
	      break;
	    case EM_IA_64:
	      result = get_ia64_segment_type (p_type);
	      break;
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  sprintf (buff, "LOPROC+%lx", p_type - PT_LOPROC);
	}
      else if ((p_type >= PT_LOOS) && (p_type <= PT_HIOS))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    case EM_PARISC:
	      result = get_parisc_segment_type (p_type);
	      break;
	    case EM_IA_64:
	      result = get_ia64_segment_type (p_type);
	      break;
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  sprintf (buff, "LOOS+%lx", p_type - PT_LOOS);
	}
      else
	sprintf (buff, _("<unknown>: %lx"), p_type);

      return buff;
    }
}

static const char *
get_mips_section_type_name (sh_type)
     unsigned int sh_type;
{
  (void)sh_type; /* Quiet unused variable warning */
  return NULL;
}

static const char *
get_parisc_section_type_name (sh_type)
     unsigned int sh_type;
{
  (void)sh_type; /* Quiet unused variable warning */
  return NULL;
}

static const char *
get_ia64_section_type_name (sh_type)
     unsigned int sh_type;
{
  (void)sh_type; /* Quiet unused variable warning */
  return NULL;
}

static const char *
get_section_type_name (sh_type)
     unsigned int sh_type;
{
  static char buff[32];

  switch (sh_type)
    {
    case SHT_NULL:		return "NULL";
    case SHT_PROGBITS:		return "PROGBITS";
    case SHT_SYMTAB:		return "SYMTAB";
    case SHT_STRTAB:		return "STRTAB";
    case SHT_RELA:		return "RELA";
    case SHT_HASH:		return "HASH";
    case SHT_DYNAMIC:		return "DYNAMIC";
    case SHT_NOTE:		return "NOTE";
    case SHT_NOBITS:		return "NOBITS";
    case SHT_REL:		return "REL";
    case SHT_SHLIB:		return "SHLIB";
    case SHT_DYNSYM:		return "DYNSYM";
    case SHT_INIT_ARRAY:	return "INIT_ARRAY";
    case SHT_FINI_ARRAY:	return "FINI_ARRAY";
    case SHT_PREINIT_ARRAY:	return "PREINIT_ARRAY";
    case SHT_GROUP:		return "GROUP";
    case SHT_SYMTAB_SHNDX:	return "SYMTAB SECTION INDICIES";
    case SHT_GNU_verdef:	return "VERDEF";
    case SHT_GNU_verneed:	return "VERNEED";
    case SHT_GNU_versym:	return "VERSYM";
    case 0x6ffffff0:		return "VERSYM";
    case 0x6ffffffc:		return "VERDEF";
    case 0x7ffffffd:		return "AUXILIARY";
    case 0x7fffffff:		return "FILTER";
    case SHT_GNU_LIBLIST:	return "GNU_LIBLIST";

    default:
      if ((sh_type >= SHT_LOPROC) && (sh_type <= SHT_HIPROC))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    case EM_MIPS:
	    case EM_MIPS_RS3_LE:
	      result = get_mips_section_type_name (sh_type);
	      break;
	    case EM_PARISC:
	      result = get_parisc_section_type_name (sh_type);
	      break;
	    case EM_IA_64:
	      result = get_ia64_section_type_name (sh_type);
	      break;
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  sprintf (buff, "LOPROC+%x", sh_type - SHT_LOPROC);
	}
      else if ((sh_type >= SHT_LOOS) && (sh_type <= SHT_HIOS))
	sprintf (buff, "LOOS+%x", sh_type - SHT_LOOS);
      else if ((sh_type >= SHT_LOUSER) && (sh_type <= SHT_HIUSER))
	sprintf (buff, "LOUSER+%x", sh_type - SHT_LOUSER);
      else
	sprintf (buff, _("<unknown>: %x"), sh_type);

      return buff;
    }
}

#define OPTION_DEBUG_DUMP	512

static void
request_dump (section, type)
     unsigned int section;
     int type;
{
  if (section >= num_dump_sects)
    {
      char *new_dump_sects;

      new_dump_sects = (char *) VG_(calloc) ("readelf.c: request_dump", section + 1, 1);

      if (new_dump_sects == NULL)
	error (_("Out of memory allocating dump request table."));
      else
	{
	  /* Copy current flag settings.  */
	  VG_(memcpy) (new_dump_sects, dump_sects, num_dump_sects);

	  VG_(free) (dump_sects);

	  dump_sects = new_dump_sects;
	  num_dump_sects = section + 1;
	}
    }

  if (dump_sects)
    dump_sects[section] |= type;

  return;
}

static const char *
get_elf_class (elf_class)
     unsigned int elf_class;
{
  static char buff[32];

  switch (elf_class)
    {
    case ELFCLASSNONE: return _("none");
    case ELFCLASS32:   return "ELF32";
    case ELFCLASS64:   return "ELF64";
    default:
      sprintf (buff, _("<unknown: %x>"), elf_class);
      return buff;
    }
}

static const char *
get_data_encoding (encoding)
     unsigned int encoding;
{
  static char buff[32];

  switch (encoding)
    {
    case ELFDATANONE: return _("none");
    case ELFDATA2LSB: return _("2's complement, little endian");
    case ELFDATA2MSB: return _("2's complement, big endian");
    default:
      sprintf (buff, _("<unknown: %x>"), encoding);
      return buff;
    }
}

static const char *
get_osabi_name (osabi)
     unsigned int osabi;
{
  static char buff[32];

  switch (osabi)
    {
    case ELFOSABI_NONE:		return "UNIX - System V";
    case ELFOSABI_HPUX:		return "UNIX - HP-UX";
    case ELFOSABI_NETBSD:	return "UNIX - NetBSD";
    case ELFOSABI_LINUX:	return "UNIX - Linux";
    case ELFOSABI_HURD:		return "GNU/Hurd";
    case ELFOSABI_SOLARIS:	return "UNIX - Solaris";
    case ELFOSABI_AIX:		return "UNIX - AIX";
    case ELFOSABI_IRIX:		return "UNIX - IRIX";
    case ELFOSABI_FREEBSD:	return "UNIX - FreeBSD";
    case ELFOSABI_TRU64:	return "UNIX - TRU64";
    case ELFOSABI_MODESTO:	return "Novell - Modesto";
    case ELFOSABI_OPENBSD:	return "UNIX - OpenBSD";
    case ELFOSABI_OPENVMS:	return "VMS - OpenVMS";
    case ELFOSABI_NSK:		return "HP - Non-Stop Kernel";
    case ELFOSABI_AROS:		return "Amiga Research OS";
    case ELFOSABI_STANDALONE:	return _("Standalone App");
    case ELFOSABI_ARM:		return "ARM";
    default:
      sprintf (buff, _("<unknown: %x>"), osabi);
      return buff;
    }
}

/* Decode the data held in 'elf_header'.  */

static int
process_file_header ()
{
  if (   elf_header.e_ident[EI_MAG0] != ELFMAG0
      || elf_header.e_ident[EI_MAG1] != ELFMAG1
      || elf_header.e_ident[EI_MAG2] != ELFMAG2
      || elf_header.e_ident[EI_MAG3] != ELFMAG3)
    {
      error
	(_("Not an ELF file - it has the wrong magic bytes at the start\n"));
      return 0;
    }

  if (do_header)
    {
      int i;

      FJALAR_DPRINTF (_("ELF Header:\n"));
      FJALAR_DPRINTF (_("  Magic:   "));
      for (i = 0; i < EI_NIDENT; i++)
 FJALAR_DPRINTF ("%2.2x ", elf_header.e_ident[i]);
      FJALAR_DPRINTF ("\n");
      FJALAR_DPRINTF (_("  Class:                             %s\n"),
	      get_elf_class (elf_header.e_ident[EI_CLASS]));
      FJALAR_DPRINTF (_("  Data:                              %s\n"),
	      get_data_encoding (elf_header.e_ident[EI_DATA]));
      FJALAR_DPRINTF (_("  Version:                           %d %s\n"),
	      elf_header.e_ident[EI_VERSION],
	      (elf_header.e_ident[EI_VERSION] == EV_CURRENT
	       ? "(current)"
	       : (elf_header.e_ident[EI_VERSION] != EV_NONE
		  ? "<unknown: %lx>"
		  : "")));
      FJALAR_DPRINTF (_("  OS/ABI:                            %s\n"),
	      get_osabi_name (elf_header.e_ident[EI_OSABI]));
      FJALAR_DPRINTF (_("  ABI Version:                       %d\n"),
	      elf_header.e_ident[EI_ABIVERSION]);
      FJALAR_DPRINTF (_("  Type:                              %s\n"),
	      get_file_type (elf_header.e_type));
      FJALAR_DPRINTF (_("  Machine:                           %s\n"),
	      get_machine_name (elf_header.e_machine));
      FJALAR_DPRINTF (_("  Version:                           0x%lx\n"),
	      (unsigned long) elf_header.e_version);

      FJALAR_DPRINTF (_("  Entry point address:               "));
      print_vma ((bfd_vma) elf_header.e_entry, PREFIX_HEX);
      FJALAR_DPRINTF (_("\n  Start of program headers:          "));
      print_vma ((bfd_vma) elf_header.e_phoff, DEC);
      FJALAR_DPRINTF (_(" (bytes into file)\n  Start of section headers:          "));
      print_vma ((bfd_vma) elf_header.e_shoff, DEC);
      FJALAR_DPRINTF (_(" (bytes into file)\n"));

      FJALAR_DPRINTF (_("  Flags:                             0x%lx%s\n"),
	      (unsigned long) elf_header.e_flags,
	      get_machine_flags (elf_header.e_flags, elf_header.e_machine));
      FJALAR_DPRINTF (_("  Size of this header:               %ld (bytes)\n"),
	      (long) elf_header.e_ehsize);
      FJALAR_DPRINTF (_("  Size of program headers:           %ld (bytes)\n"),
	      (long) elf_header.e_phentsize);
      FJALAR_DPRINTF (_("  Number of program headers:         %ld\n"),
	      (long) elf_header.e_phnum);
      FJALAR_DPRINTF (_("  Size of section headers:           %ld (bytes)\n"),
	      (long) elf_header.e_shentsize);
      FJALAR_DPRINTF (_("  Number of section headers:         %ld"),
	      (long) elf_header.e_shnum);
      if (section_headers != NULL && elf_header.e_shnum == 0)
 FJALAR_DPRINTF (" (%ld)", (long) section_headers[0].sh_size);
      putc ('\n', stdout);
      FJALAR_DPRINTF (_("  Section header string table index: %ld"),
	      (long) elf_header.e_shstrndx);
      if (section_headers != NULL && elf_header.e_shstrndx == SHN_XINDEX)
 FJALAR_DPRINTF (" (%ld)", (long) section_headers[0].sh_link);
      putc ('\n', stdout);
    }

  if (section_headers != NULL)
    {
      if (elf_header.e_shnum == 0)
	elf_header.e_shnum = section_headers[0].sh_size;
      if (elf_header.e_shstrndx == SHN_XINDEX)
	elf_header.e_shstrndx = section_headers[0].sh_link;
      VG_(free) (section_headers);
      section_headers = NULL;
    }

  return 1;
}


static int
get_32bit_program_headers (file, program_headers)
     FILE *file;
     Elf_Internal_Phdr *program_headers;
{
  Elf32_External_Phdr *phdrs;
  Elf32_External_Phdr *external;
  Elf_Internal_Phdr *internal;
  unsigned int i;

  phdrs = ((Elf32_External_Phdr *)
	   get_data (NULL, file, elf_header.e_phoff,
		     elf_header.e_phentsize * elf_header.e_phnum,
		     _("program headers")));
  if (!phdrs)
    return 0;

  for (i = 0, internal = program_headers, external = phdrs;
       i < elf_header.e_phnum;
       i++, internal++, external++)
    {
      internal->p_type   = BYTE_GET (external->p_type);
      internal->p_offset = BYTE_GET (external->p_offset);
      internal->p_vaddr  = BYTE_GET (external->p_vaddr);
      internal->p_paddr  = BYTE_GET (external->p_paddr);
      internal->p_filesz = BYTE_GET (external->p_filesz);
      internal->p_memsz  = BYTE_GET (external->p_memsz);
      internal->p_flags  = BYTE_GET (external->p_flags);
      internal->p_align  = BYTE_GET (external->p_align);
    }

  VG_(free) (phdrs);

  return 1;
}

static int
get_64bit_program_headers (file, program_headers)
     FILE *file;
     Elf_Internal_Phdr *program_headers;
{
  Elf64_External_Phdr *phdrs;
  Elf64_External_Phdr *external;
  Elf_Internal_Phdr *internal;
  unsigned int i;

  phdrs = ((Elf64_External_Phdr *)
	   get_data (NULL, file, elf_header.e_phoff,
		     elf_header.e_phentsize * elf_header.e_phnum,
		     _("program headers")));
  if (!phdrs)
    return 0;

  for (i = 0, internal = program_headers, external = phdrs;
       i < elf_header.e_phnum;
       i++, internal++, external++)
    {
      internal->p_type   = BYTE_GET (external->p_type);
      internal->p_flags  = BYTE_GET (external->p_flags);
      internal->p_offset = BYTE_GET8 (external->p_offset);
      internal->p_vaddr  = BYTE_GET8 (external->p_vaddr);
      internal->p_paddr  = BYTE_GET8 (external->p_paddr);
      internal->p_filesz = BYTE_GET8 (external->p_filesz);
      internal->p_memsz  = BYTE_GET8 (external->p_memsz);
      internal->p_align  = BYTE_GET8 (external->p_align);
    }

  VG_(free) (phdrs);

  return 1;
}

/* Returns 1 if the program headers were loaded.  */

static int
process_program_headers (file)
     FILE *file;
{
  Elf_Internal_Phdr *program_headers;
  Elf_Internal_Phdr *segment;
  unsigned int i;

  if (elf_header.e_phnum == 0)
    {
      if (do_segments)
 FJALAR_DPRINTF (_("\nThere are no program headers in this file.\n"));
      return 0;
    }

  if (do_segments && !do_header)
    {
      FJALAR_DPRINTF (_("\nElf file type is %s\n"), get_file_type (elf_header.e_type));
      FJALAR_DPRINTF (_("Entry point "));
      print_vma ((bfd_vma) elf_header.e_entry, PREFIX_HEX);
      FJALAR_DPRINTF (_("\nThere are %d program headers, starting at offset "),
	      elf_header.e_phnum);
      print_vma ((bfd_vma) elf_header.e_phoff, DEC);
      FJALAR_DPRINTF ("\n");
    }

  program_headers = (Elf_Internal_Phdr *) VG_(malloc)
    ("readelf.c: process_program_headers", elf_header.e_phnum * sizeof (Elf_Internal_Phdr));

  if (program_headers == NULL)
    {
      error (_("Out of memory\n"));
      return 0;
    }

  if (is_32bit_elf)
    i = get_32bit_program_headers (file, program_headers);
  else
    i = get_64bit_program_headers (file, program_headers);

  if (i == 0)
    {
      VG_(free) (program_headers);
      return 0;
    }

  if (do_segments)
    {
      if (elf_header.e_phnum > 1)
 FJALAR_DPRINTF (_("\nProgram Headers:\n"));
      else
 FJALAR_DPRINTF (_("\nProgram Headers:\n"));

      if (is_32bit_elf)
 FJALAR_DPRINTF
	  (_("  Type           Offset   VirtAddr   PhysAddr   FileSiz MemSiz  Flg Align\n"));
      else if (do_wide)
 FJALAR_DPRINTF
	  (_("  Type           Offset   VirtAddr           PhysAddr           FileSiz  MemSiz   Flg Align\n"));
      else
	{
	  FJALAR_DPRINTF
	    (_("  Type           Offset             VirtAddr           PhysAddr\n"));
	  FJALAR_DPRINTF
	    (_("                 FileSiz            MemSiz              Flags  Align\n"));
	}
    }

  loadaddr = -1;
  dynamic_addr = 0;
  dynamic_size = 0;

  for (i = 0, segment = program_headers;
       i < elf_header.e_phnum;
       i++, segment++)
    {
      if (do_segments)
	{
	  FJALAR_DPRINTF ("  %-14.14s ", get_segment_type (segment->p_type));

	  if (is_32bit_elf)
	    {
	      FJALAR_DPRINTF ("0x%6.6lx ", (unsigned long) segment->p_offset);
	      FJALAR_DPRINTF ("0x%8.8lx ", (unsigned long) segment->p_vaddr);
	      FJALAR_DPRINTF ("0x%8.8lx ", (unsigned long) segment->p_paddr);
	      FJALAR_DPRINTF ("0x%5.5lx ", (unsigned long) segment->p_filesz);
	      FJALAR_DPRINTF ("0x%5.5lx ", (unsigned long) segment->p_memsz);
	      FJALAR_DPRINTF ("%c%c%c ",
		      (segment->p_flags & PF_R ? 'R' : ' '),
		      (segment->p_flags & PF_W ? 'W' : ' '),
		      (segment->p_flags & PF_X ? 'E' : ' '));
	      FJALAR_DPRINTF ("%#lx", (unsigned long) segment->p_align);
	    }
	  else if (do_wide)
	    {
	      if ((unsigned long) segment->p_offset == segment->p_offset)
	 FJALAR_DPRINTF ("0x%6.6lx ", (unsigned long) segment->p_offset);
	      else
		{
		  print_vma (segment->p_offset, FULL_HEX);
		  putchar (' ');
		}

	      print_vma (segment->p_vaddr, FULL_HEX);
	      putchar (' ');
	      print_vma (segment->p_paddr, FULL_HEX);
	      putchar (' ');

	      if ((unsigned long) segment->p_filesz == segment->p_filesz)
	 FJALAR_DPRINTF ("0x%6.6lx ", (unsigned long) segment->p_filesz);
	      else
		{
		  print_vma (segment->p_filesz, FULL_HEX);
		  putchar (' ');
		}

	      if ((unsigned long) segment->p_memsz == segment->p_memsz)
	 FJALAR_DPRINTF ("0x%6.6lx", (unsigned long) segment->p_memsz);
	      else
		{
		  print_vma (segment->p_offset, FULL_HEX);
		}

	      FJALAR_DPRINTF (" %c%c%c ",
		      (segment->p_flags & PF_R ? 'R' : ' '),
		      (segment->p_flags & PF_W ? 'W' : ' '),
		      (segment->p_flags & PF_X ? 'E' : ' '));

	      if ((unsigned long) segment->p_align == segment->p_align)
	 FJALAR_DPRINTF ("%#lx", (unsigned long) segment->p_align);
	      else
		{
		  print_vma (segment->p_align, PREFIX_HEX);
		}
	    }
	  else
	    {
	      print_vma (segment->p_offset, FULL_HEX);
	      putchar (' ');
	      print_vma (segment->p_vaddr, FULL_HEX);
	      putchar (' ');
	      print_vma (segment->p_paddr, FULL_HEX);
	      FJALAR_DPRINTF ("\n                 ");
	      print_vma (segment->p_filesz, FULL_HEX);
	      putchar (' ');
	      print_vma (segment->p_memsz, FULL_HEX);
	      FJALAR_DPRINTF ("  %c%c%c    ",
		      (segment->p_flags & PF_R ? 'R' : ' '),
		      (segment->p_flags & PF_W ? 'W' : ' '),
		      (segment->p_flags & PF_X ? 'E' : ' '));
	      print_vma (segment->p_align, HEX);
	    }
	}

      switch (segment->p_type)
	{
	case PT_LOAD:
	  if (loadaddr == -1)
	    {
	      unsigned long align_mask = -segment->p_align;

	      if (align_mask == 0)
		--align_mask;
	      loadaddr = ((segment->p_vaddr & align_mask)
			  - (segment->p_offset & align_mask));
	    }
	  break;

	case PT_DYNAMIC:
	  if (dynamic_addr)
	    error (_("more than one dynamic segment\n"));

	  dynamic_addr = segment->p_offset;
	  dynamic_size = segment->p_filesz;
	  break;

	case PT_INTERP:
	  if (fseek (file, (long) segment->p_offset, SEEK_SET))
	    error (_("Unable to find program interpreter name\n"));
	  else
	    {
	      program_interpreter[0] = 0;
	      /* fscanf (file, "%63s", program_interpreter);*/
	      fgets(program_interpreter, 62, file);

	      if (do_segments)
	 FJALAR_DPRINTF (_("\n      [Requesting program interpreter: %s]"),
		    program_interpreter);
	    }
	  break;
	}

      if (do_segments)
	putc ('\n', stdout);
    }

  if (loadaddr == -1)
    {
      /* Very strange.  */
      loadaddr = 0;
    }

  if (do_segments && section_headers != NULL)
    {
      FJALAR_DPRINTF (_("\n Section to Segment mapping:\n"));
      FJALAR_DPRINTF (_("  Segment Sections...\n"));

      tl_assert (string_table != NULL);

      for (i = 0; i < elf_header.e_phnum; i++)
	{
	  unsigned int j;
	  Elf_Internal_Shdr *section;

	  segment = program_headers + i;
	  section = section_headers;

	  FJALAR_DPRINTF ("   %2.2d     ", i);

	  for (j = 1; j < elf_header.e_shnum; j++, section++)
	    {
	      if (section->sh_size > 0
		  /* Compare allocated sections by VMA, unallocated
		     sections by file offset.  */
		  && (section->sh_flags & SHF_ALLOC
		      ? (section->sh_addr >= segment->p_vaddr
			 && section->sh_addr + section->sh_size
			 <= segment->p_vaddr + segment->p_memsz)
		      : ((bfd_vma) section->sh_offset >= segment->p_offset
			 && (section->sh_offset + section->sh_size
			     <= segment->p_offset + segment->p_filesz))))
	 FJALAR_DPRINTF ("%s ", SECTION_NAME (section));
	    }

	  putc ('\n',stdout);
	}
    }

  VG_(free) (program_headers);

  return 1;
}


static int
get_32bit_section_headers (file, num)
     FILE *file;
     unsigned int num;
{
  Elf32_External_Shdr *shdrs;
  Elf_Internal_Shdr *internal;
  unsigned int i;

  shdrs = ((Elf32_External_Shdr *)
	   get_data (NULL, file, elf_header.e_shoff,
		     elf_header.e_shentsize * num,
		     _("section headers")));
  if (!shdrs)
    return 0;

  section_headers = ((Elf_Internal_Shdr *)
		     VG_(malloc) ("readelf.c: get_32b_sh", num * sizeof (Elf_Internal_Shdr)));

  //  FJALAR_DPRINTF("Just allocated section_headers at 0x%x, size = %d * %d\n",
  //         section_headers, num, sizeof (Elf_Internal_Shdr)); // PG

  if (section_headers == NULL)
    {
      error (_("Out of memory\n"));
      return 0;
    }

  for (i = 0, internal = section_headers;
       i < num;
       i++, internal++)
    {
      internal->sh_name      = BYTE_GET (shdrs[i].sh_name);
      internal->sh_type      = BYTE_GET (shdrs[i].sh_type);
      internal->sh_flags     = BYTE_GET (shdrs[i].sh_flags);
      internal->sh_addr      = BYTE_GET (shdrs[i].sh_addr);
      internal->sh_offset    = BYTE_GET (shdrs[i].sh_offset);
      internal->sh_size      = BYTE_GET (shdrs[i].sh_size);
      internal->sh_link      = BYTE_GET (shdrs[i].sh_link);
      internal->sh_info      = BYTE_GET (shdrs[i].sh_info);
      internal->sh_addralign = BYTE_GET (shdrs[i].sh_addralign);
      internal->sh_entsize   = BYTE_GET (shdrs[i].sh_entsize);
    }

  VG_(free) (shdrs);

  return 1;
}

static int
get_64bit_section_headers (file, num)
     FILE *file;
     unsigned int num;
{
  Elf64_External_Shdr *shdrs;
  Elf_Internal_Shdr *internal;
  unsigned int i;

  shdrs = ((Elf64_External_Shdr *)
	   get_data (NULL, file, elf_header.e_shoff,
		     elf_header.e_shentsize * num,
		     _("section headers")));
  if (!shdrs)
    return 0;

  section_headers = ((Elf_Internal_Shdr *)
		     VG_(malloc) ("readelf.c: get_64b_sh", num * sizeof (Elf_Internal_Shdr)));

  if (section_headers == NULL)
    {
      error (_("Out of memory\n"));
      return 0;
    }

  for (i = 0, internal = section_headers;
       i < num;
       i++, internal++)
    {
      internal->sh_name      = BYTE_GET (shdrs[i].sh_name);
      internal->sh_type      = BYTE_GET (shdrs[i].sh_type);
      internal->sh_flags     = BYTE_GET8 (shdrs[i].sh_flags);
      internal->sh_addr      = BYTE_GET8 (shdrs[i].sh_addr);
      internal->sh_size      = BYTE_GET8 (shdrs[i].sh_size);
      internal->sh_entsize   = BYTE_GET8 (shdrs[i].sh_entsize);
      internal->sh_link      = BYTE_GET (shdrs[i].sh_link);
      internal->sh_info      = BYTE_GET (shdrs[i].sh_info);
      internal->sh_offset    = BYTE_GET (shdrs[i].sh_offset);
      internal->sh_addralign = BYTE_GET (shdrs[i].sh_addralign);
    }

  VG_(free) (shdrs);

  return 1;
}

static Elf_Internal_Sym *
get_32bit_elf_symbols (file, section)
     FILE *file;
     Elf_Internal_Shdr *section;
{
  unsigned long number;
  Elf32_External_Sym *esyms;
  Elf_External_Sym_Shndx *shndx;
  Elf_Internal_Sym *isyms;
  Elf_Internal_Sym *psym;
  unsigned int j;

  esyms = ((Elf32_External_Sym *)
	   get_data (NULL, file, section->sh_offset,
		     section->sh_size, _("symbols")));
  if (!esyms)
    return NULL;

  shndx = NULL;
  if (symtab_shndx_hdr != NULL
      && (symtab_shndx_hdr->sh_link
	  == (unsigned long) SECTION_HEADER_NUM (section - section_headers)))
    {
      shndx = ((Elf_External_Sym_Shndx *)
	       get_data (NULL, file, symtab_shndx_hdr->sh_offset,
			 symtab_shndx_hdr->sh_size, _("symtab shndx")));
      if (!shndx)
	{
	  VG_(free) (esyms);
	  return NULL;
	}
    }

  number = section->sh_size / section->sh_entsize;
  isyms = (Elf_Internal_Sym *) VG_(malloc) ("readelf.c: get_32b_elfsy", number * sizeof (Elf_Internal_Sym));

  if (isyms == NULL)
    {
      error (_("Out of memory\n"));
      if (shndx)
	VG_(free) (shndx);
      VG_(free) (esyms);
      return NULL;
    }

  for (j = 0, psym = isyms;
       j < number;
       j++, psym++)
    {
      psym->st_name  = BYTE_GET (esyms[j].st_name);
      psym->st_value = BYTE_GET (esyms[j].st_value);
      psym->st_size  = BYTE_GET (esyms[j].st_size);
      psym->st_shndx = BYTE_GET (esyms[j].st_shndx);
      if (psym->st_shndx == SHN_XINDEX && shndx != NULL)
	psym->st_shndx
	  = byte_get ((unsigned char *) &shndx[j], sizeof (shndx[j]));
      psym->st_info  = BYTE_GET (esyms[j].st_info);
      psym->st_other = BYTE_GET (esyms[j].st_other);
    }

  if (shndx)
    VG_(free) (shndx);
  VG_(free) (esyms);

  return isyms;
}

static Elf_Internal_Sym *
get_64bit_elf_symbols (file, section)
     FILE *file;
     Elf_Internal_Shdr *section;
{
  unsigned long number;
  Elf64_External_Sym *esyms;
  Elf_External_Sym_Shndx *shndx;
  Elf_Internal_Sym *isyms;
  Elf_Internal_Sym *psym;
  unsigned int j;

  esyms = ((Elf64_External_Sym *)
	   get_data (NULL, file, section->sh_offset,
		     section->sh_size, _("symbols")));
  if (!esyms)
    return NULL;

  shndx = NULL;
  if (symtab_shndx_hdr != NULL
      && (symtab_shndx_hdr->sh_link
	  == (unsigned long) SECTION_HEADER_NUM (section - section_headers)))
    {
      shndx = ((Elf_External_Sym_Shndx *)
	       get_data (NULL, file, symtab_shndx_hdr->sh_offset,
			 symtab_shndx_hdr->sh_size, _("symtab shndx")));
      if (!shndx)
	{
	  VG_(free) (esyms);
	  return NULL;
	}
    }

  number = section->sh_size / section->sh_entsize;
  isyms = (Elf_Internal_Sym *) VG_(malloc) ("readelf.c: get_64b_elfsym", number * sizeof (Elf_Internal_Sym));

  if (isyms == NULL)
    {
      error (_("Out of memory\n"));
      if (shndx)
	VG_(free) (shndx);
      VG_(free) (esyms);
      return NULL;
    }

  for (j = 0, psym = isyms;
       j < number;
       j++, psym++)
    {
      psym->st_name  = BYTE_GET (esyms[j].st_name);
      psym->st_info  = BYTE_GET (esyms[j].st_info);
      psym->st_other = BYTE_GET (esyms[j].st_other);
      psym->st_shndx = BYTE_GET (esyms[j].st_shndx);
      if (psym->st_shndx == SHN_XINDEX && shndx != NULL)
	psym->st_shndx
	  = byte_get ((unsigned char *) &shndx[j], sizeof (shndx[j]));
      psym->st_value = BYTE_GET8 (esyms[j].st_value);
      psym->st_size  = BYTE_GET8 (esyms[j].st_size);
    }

  if (shndx)
    VG_(free) (shndx);
  VG_(free) (esyms);

  return isyms;
}

static const char *
get_elf_section_flags (sh_flags)
     bfd_vma sh_flags;
{
  static char buff[32];

  *buff = 0;

  while (sh_flags)
    {
      bfd_vma flag;

      flag = sh_flags & - sh_flags;
      sh_flags &= ~ flag;

      switch (flag)
	{
	case SHF_WRITE:		   VG_(strcat) (buff, "W"); break;
	case SHF_ALLOC:		   VG_(strcat) (buff, "A"); break;
	case SHF_EXECINSTR:	   VG_(strcat) (buff, "X"); break;
	case SHF_MERGE:		   VG_(strcat) (buff, "M"); break;
	case SHF_STRINGS:	   VG_(strcat) (buff, "S"); break;
	case SHF_INFO_LINK:	   VG_(strcat) (buff, "I"); break;
	case SHF_LINK_ORDER:	   VG_(strcat) (buff, "L"); break;
	case SHF_OS_NONCONFORMING: VG_(strcat) (buff, "O"); break;
	case SHF_GROUP:		   VG_(strcat) (buff, "G"); break;
	case SHF_TLS:		   VG_(strcat) (buff, "T"); break;

	default:
	  if (flag & SHF_MASKOS)
	    {
	      VG_(strcat) (buff, "o");
	      sh_flags &= ~ SHF_MASKOS;
	    }
	  else if (flag & SHF_MASKPROC)
	    {
	      VG_(strcat) (buff, "p");
	      sh_flags &= ~ SHF_MASKPROC;
	    }
	  else
	    VG_(strcat) (buff, "x");
	  break;
	}
    }

  return buff;
}

static int
process_section_headers (file)
     FILE *file;
{
  Elf_Internal_Shdr *section;
  unsigned int i;

  section_headers = NULL;

  if (elf_header.e_shnum == 0)
    {
      if (do_sections)
 FJALAR_DPRINTF (_("\nThere are no sections in this file.\n"));

      return 1;
    }

  if (do_sections && !do_header)
    FJALAR_DPRINTF (_("There are %d section headers, starting at offset 0x%lx:\n"),
	    elf_header.e_shnum, (unsigned long) elf_header.e_shoff);

  if (is_32bit_elf)
    {
      if (! get_32bit_section_headers (file, elf_header.e_shnum))
	return 0;
    }
  else if (! get_64bit_section_headers (file, elf_header.e_shnum))
    return 0;

  /* Read in the string table, so that we have names to display.  */
  section = SECTION_HEADER (elf_header.e_shstrndx);

  if (section->sh_size != 0)
    {
      string_table = (char *) get_data (NULL, file, section->sh_offset,
					section->sh_size, _("string table"));

      string_table_length = section->sh_size;
    }

  /* Scan the sections for the dynamic symbol table
     and dynamic string table and debug sections.  */
  dynamic_symbols = NULL;
  dynamic_strings = NULL;
  dynamic_syminfo = NULL;
  symtab_shndx_hdr = NULL;

  for (i = 0, section = section_headers;
       i < elf_header.e_shnum;
       i++, section++)
    {
      char *name = SECTION_NAME (section);

      FJALAR_DPRINTF("At section: %p - %p\n", section, name);

      if (section->sh_type == SHT_DYNSYM)
	{
	  if (dynamic_symbols != NULL)
	    {
	      error (_("File contains multiple dynamic symbol tables\n"));
	      continue;
	    }

	  num_dynamic_syms = section->sh_size / section->sh_entsize;
	  dynamic_symbols = GET_ELF_SYMBOLS (file, section);
	}
      else if (section->sh_type == SHT_STRTAB
	       && VG_(strcmp) (name, ".dynstr") == 0)
	{
	  if (dynamic_strings != NULL)
	    {
	      error (_("File contains multiple dynamic string tables\n"));
	      continue;
	    }

	  dynamic_strings = (char *) get_data (NULL, file, section->sh_offset,
					       section->sh_size,
					       _("dynamic strings"));
	}
      else if (section->sh_type == SHT_SYMTAB_SHNDX)
	{
	  if (symtab_shndx_hdr != NULL)
	    {
	      error (_("File contains multiple symtab shndx tables\n"));
	      continue;
	    }
	  symtab_shndx_hdr = section;
	}
      else if ((do_debugging || do_debug_info || do_debug_abbrevs
		|| do_debug_lines || do_debug_pubnames || do_debug_aranges
		|| do_debug_frames || do_debug_macinfo || do_debug_str
		|| do_debug_loc)
	       && VG_(strncmp) (name, ".debug_", 7) == 0)
	{
	  name += 7;

	  if (do_debugging
	      || (do_debug_info     && (VG_(strcmp) (name, "info") == 0))
	      || (do_debug_abbrevs  && (VG_(strcmp) (name, "abbrev") == 0))
	      || (do_debug_lines    && (VG_(strcmp) (name, "line") == 0))
	      || (do_debug_pubnames && (VG_(strcmp) (name, "pubnames") == 0))
	      || (do_debug_aranges  && (VG_(strcmp) (name, "aranges") == 0))
	      || (do_debug_frames   && (VG_(strcmp) (name, "frame") == 0))
	      || (do_debug_macinfo  && (VG_(strcmp) (name, "macinfo") == 0))
	      || (do_debug_str      && (VG_(strcmp) (name, "str") == 0))
	      || (do_debug_loc      && (VG_(strcmp) (name, "loc") == 0))
	      )
	    request_dump (i, DEBUG_DUMP);
	}
      /* linkonce section to be combined with .debug_info at link time.  */
      else if ((do_debugging || do_debug_info)
	       && VG_(strncmp) (name, ".gnu.linkonce.wi.", 17) == 0)
	request_dump (i, DEBUG_DUMP);
      else if (do_debug_frames && VG_(strcmp) (name, ".eh_frame") == 0)
	request_dump (i, DEBUG_DUMP);
    }

  if (! do_sections)
    return 1;

  if (elf_header.e_shnum > 1)
    FJALAR_DPRINTF (_("\nSection Headers:\n"));
  else
    FJALAR_DPRINTF (_("\nSection Header:\n"));

  if (is_32bit_elf)
    FJALAR_DPRINTF
      (_("  [Nr] Name              Type            Addr     Off    Size   ES Flg Lk Inf Al\n"));
  else if (do_wide)
    FJALAR_DPRINTF
      (_("  [Nr] Name              Type            Address          Off    Size   ES Flg Lk Inf Al\n"));
  else
    {
      FJALAR_DPRINTF (_("  [Nr] Name              Type             Address           Offset\n"));
      FJALAR_DPRINTF (_("       Size              EntSize          Flags  Link  Info  Align\n"));
    }

  for (i = 0, section = section_headers;
       i < elf_header.e_shnum;
       i++, section++)
    {
      FJALAR_DPRINTF ("  [%2u] %-17.17s %-15.15s ",
	      SECTION_HEADER_NUM (i),
	      SECTION_NAME (section),
	      get_section_type_name (section->sh_type));

      if (is_32bit_elf)
	{
	  print_vma (section->sh_addr, LONG_HEX);

	  FJALAR_DPRINTF ( " %6.6lx %6.6lx %2.2lx",
		   (unsigned long) section->sh_offset,
		   (unsigned long) section->sh_size,
		   (unsigned long) section->sh_entsize);

	  FJALAR_DPRINTF (" %3s ", get_elf_section_flags (section->sh_flags));

	  FJALAR_DPRINTF ("%2ld %3lx %2ld\n",
		  (unsigned long) section->sh_link,
		  (unsigned long) section->sh_info,
		  (unsigned long) section->sh_addralign);
	}
      else if (do_wide)
	{
	  print_vma (section->sh_addr, LONG_HEX);

	  if ((long) section->sh_offset == section->sh_offset)
	    FJALAR_DPRINTF (" %6.6lx", (unsigned long) section->sh_offset);
	  else
	    {
	      putchar (' ');
	      print_vma (section->sh_offset, LONG_HEX);
	    }

	  if ((unsigned long) section->sh_size == section->sh_size)
	    FJALAR_DPRINTF (" %6.6lx", (unsigned long) section->sh_size);
	  else
	    {
	      putchar (' ');
	      print_vma (section->sh_size, LONG_HEX);
	    }

	  if ((unsigned long) section->sh_entsize == section->sh_entsize)
	    FJALAR_DPRINTF (" %2.2lx", (unsigned long) section->sh_entsize);
	  else
	    {
	      putchar (' ');
	      print_vma (section->sh_entsize, LONG_HEX);
	    }

	  FJALAR_DPRINTF (" %3s ", get_elf_section_flags (section->sh_flags));

	  FJALAR_DPRINTF ("%2ld %3lx ",
		  (unsigned long) section->sh_link,
		  (unsigned long) section->sh_info);

	  if ((unsigned long) section->sh_addralign == section->sh_addralign)
	    FJALAR_DPRINTF ("%2ld\n", (unsigned long) section->sh_addralign);
	  else
	    {
	      print_vma (section->sh_addralign, DEC);
	      putchar ('\n');
	    }
	}
      else
	{
	  putchar (' ');
	  print_vma (section->sh_addr, LONG_HEX);
	  if ((long) section->sh_offset == section->sh_offset)
	    FJALAR_DPRINTF ("  %8.8lx", (unsigned long) section->sh_offset);
	  else
	    {
	      FJALAR_DPRINTF ("  ");
	      print_vma (section->sh_offset, LONG_HEX);
	    }
	  FJALAR_DPRINTF ("\n       ");
	  print_vma (section->sh_size, LONG_HEX);
	  FJALAR_DPRINTF ("  ");
	  print_vma (section->sh_entsize, LONG_HEX);

	  FJALAR_DPRINTF (" %3s ", get_elf_section_flags (section->sh_flags));

	  FJALAR_DPRINTF ("     %2ld   %3lx     %ld\n",
		  (unsigned long) section->sh_link,
		  (unsigned long) section->sh_info,
		  (unsigned long) section->sh_addralign);
	}
    }

  FJALAR_DPRINTF (_("Key to Flags:\n\
  W (write), A (alloc), X (execute), M (merge), S (strings)\n\
  I (info), L (link order), G (group), x (unknown)\n\
  O (extra OS processing required) o (OS specific), p (processor specific)\n"));

  return 1;
}

struct
{
  const char *name;
  int reloc;
  int size;
  int rela;
} dynamic_relocations [] =
{
    { "REL", DT_REL, DT_RELSZ, FALSE },
    { "RELA", DT_RELA, DT_RELASZ, TRUE },
    { "PLT", DT_JMPREL, DT_PLTRELSZ, UNKNOWN }
};

/* Process the reloc section.  */
static int
process_relocs (file)
     FILE *file;
{
  unsigned long rel_size;
  unsigned long rel_offset;


  if (!do_reloc)
    return 1;

  if (do_using_dynamic)
    {
      int is_rela;
      const char *name;
      int has_dynamic_reloc;
      unsigned int i;

      has_dynamic_reloc = 0;

      for (i = 0; i < ARRAY_SIZE (dynamic_relocations); i++)
	{
	  is_rela = dynamic_relocations [i].rela;
	  name = dynamic_relocations [i].name;
	  rel_size = dynamic_info [dynamic_relocations [i].size];
	  rel_offset = dynamic_info [dynamic_relocations [i].reloc];

	  has_dynamic_reloc |= rel_size;

	  if (is_rela == UNKNOWN)
	    {
	      if (dynamic_relocations [i].reloc == DT_JMPREL)
		switch (dynamic_info[DT_PLTREL])
		  {
		  case DT_REL:
		    is_rela = FALSE;
		    break;
		  case DT_RELA:
		    is_rela = TRUE;
		    break;
		  }
	    }

	  if (rel_size)
	    {
	      FJALAR_DPRINTF
		(_("\n'%s' relocation section at offset 0x%lx contains %ld bytes:\n"),
		 name, rel_offset, rel_size);

	      dump_relocations (file, rel_offset - loadaddr, rel_size,
				dynamic_symbols, num_dynamic_syms,
				dynamic_strings, is_rela);
	    }
	}

      if (! has_dynamic_reloc)
 FJALAR_DPRINTF (_("\nThere are no dynamic relocations in this file.\n"));
    }
  else
    {
      Elf_Internal_Shdr *section;
      unsigned long i;
      int found = 0;

      for (i = 0, section = section_headers;
	   i < elf_header.e_shnum;
	   i++, section++)
	{
	  if (   section->sh_type != SHT_RELA
	      && section->sh_type != SHT_REL)
	    continue;

	  rel_offset = section->sh_offset;
	  rel_size   = section->sh_size;

	  if (rel_size)
	    {
	      Elf_Internal_Shdr *strsec;
	      Elf_Internal_Sym *symtab;
	      char *strtab;
	      int is_rela;
	      unsigned long nsyms;

	      FJALAR_DPRINTF (_("\nRelocation section "));

	      if (string_table == NULL)
	 FJALAR_DPRINTF ("%d", section->sh_name);
	      else
	 FJALAR_DPRINTF (_("'%s'"), SECTION_NAME (section));

	      FJALAR_DPRINTF (_(" at offset 0x%lx contains %lu entries:\n"),
		 rel_offset, (unsigned long) (rel_size / section->sh_entsize));

	      symtab = NULL;
	      strtab = NULL;
	      nsyms = 0;
	      if (section->sh_link)
		{
		  Elf_Internal_Shdr *symsec;

		  symsec = SECTION_HEADER (section->sh_link);
		  nsyms = symsec->sh_size / symsec->sh_entsize;
		  symtab = GET_ELF_SYMBOLS (file, symsec);

		  if (symtab == NULL)
		    continue;

		  strsec = SECTION_HEADER (symsec->sh_link);

		  strtab = (char *) get_data (NULL, file, strsec->sh_offset,
					      strsec->sh_size,
					      _("string table"));
		}
	      is_rela = section->sh_type == SHT_RELA;

	      dump_relocations (file, rel_offset, rel_size,
				symtab, nsyms, strtab, is_rela);

	      if (strtab)
		VG_(free) (strtab);
	      if (symtab)
		VG_(free) (symtab);

	      found = 1;
	    }
	}

      if (! found)
 FJALAR_DPRINTF (_("\nThere are no relocations in this file.\n"));
    }

  return 1;
}

//#include "unwind-ia64.h"
#include "elf/ia64.h"

/* An absolute address consists of a section and an offset.  If the
   section is NULL, the offset itself is the address, otherwise, the
   address equals to LOAD_ADDRESS(section) + offset.  */

struct absaddr
  {
    unsigned short section;
    bfd_vma offset;
  };

struct unw_aux_info
  {
    struct unw_table_entry
      {
	struct absaddr start;
	struct absaddr end;
	struct absaddr info;
      }
    *table;			/* Unwind table.  */
    unsigned long table_len;	/* Length of unwind table.  */
    unsigned char *info;	/* Unwind info.  */
    unsigned long info_size;	/* Size of unwind info.  */
    bfd_vma info_addr;		/* starting address of unwind info.  */
    bfd_vma seg_base;		/* Starting address of segment.  */
    Elf_Internal_Sym *symtab;	/* The symbol table.  */
    unsigned long nsyms;	/* Number of symbols.  */
    char *strtab;		/* The string table.  */
    unsigned long strtab_size;	/* Size of string table.  */
  };

//static void find_symbol_for_address
//  PARAMS ((struct unw_aux_info *, struct absaddr, const char **, bfd_vma *));
static void dump_ia64_unwind
  PARAMS ((struct unw_aux_info *));
static int slurp_ia64_unwind_table
  PARAMS ((FILE *, struct unw_aux_info *, Elf_Internal_Shdr *));

/* static void */
/* find_symbol_for_address (aux, addr, symname, offset) */
/*      struct unw_aux_info *aux; */
/*      struct absaddr addr; */
/*      const char **symname; */
/*      bfd_vma *offset; */
/* { */
/*   bfd_vma dist = (bfd_vma) 0x100000; */
/*   Elf_Internal_Sym *sym, *best = NULL; */
/*   unsigned long i; */

/*   for (i = 0, sym = aux->symtab; i < aux->nsyms; ++i, ++sym) */
/*     { */
/*       if (ELF_ST_TYPE (sym->st_info) == STT_FUNC */
/* 	  && sym->st_name != 0 */
/* 	  && (addr.section == SHN_UNDEF || addr.section == sym->st_shndx) */
/* 	  && addr.offset >= sym->st_value */
/* 	  && addr.offset - sym->st_value < dist) */
/* 	{ */
/* 	  best = sym; */
/* 	  dist = addr.offset - sym->st_value; */
/* 	  if (!dist) */
/* 	    break; */
/* 	} */
/*     } */
/*   if (best) */
/*     { */
/*       *symname = (best->st_name >= aux->strtab_size */
/* 		  ? "<corrupt>" : aux->strtab + best->st_name); */
/*       *offset = dist; */
/*       return; */
/*     } */
/*   *symname = NULL; */
/*   *offset = addr.offset; */
/* } */

static void
dump_ia64_unwind (aux)
     struct unw_aux_info *aux;
{
  (void)aux; /* Quiet unused variable warning */
}

static int
slurp_ia64_unwind_table (file, aux, sec)
     FILE *file;
     struct unw_aux_info *aux;
     Elf_Internal_Shdr *sec;
{
  unsigned long size, addr_size, nrelas, i;
  Elf_Internal_Phdr *prog_hdrs, *seg;
  struct unw_table_entry *tep;
  Elf_Internal_Shdr *relsec;
  Elf_Internal_Rela *rela, *rp;
  unsigned char *table, *tp;
  Elf_Internal_Sym *sym;
  const char *relname;
  int result;

  addr_size = is_32bit_elf ? 4 : 8;

  /* First, find the starting address of the segment that includes
     this section: */

  if (elf_header.e_phnum)
    {
      prog_hdrs = (Elf_Internal_Phdr *)
	xmalloc (elf_header.e_phnum * sizeof (Elf_Internal_Phdr));

      if (is_32bit_elf)
	result = get_32bit_program_headers (file, prog_hdrs);
      else
	result = get_64bit_program_headers (file, prog_hdrs);

      if (!result)
	{
	  VG_(free) (prog_hdrs);
	  return 0;
	}

      for (seg = prog_hdrs; seg < prog_hdrs + elf_header.e_phnum; ++seg)
	{
	  if (seg->p_type != PT_LOAD)
	    continue;

	  if (sec->sh_addr >= seg->p_vaddr
	      && (sec->sh_addr + sec->sh_size <= seg->p_vaddr + seg->p_memsz))
	    {
	      aux->seg_base = seg->p_vaddr;
	      break;
	    }
	}

      VG_(free) (prog_hdrs);
    }

  /* Second, build the unwind table from the contents of the unwind section:  */
  size = sec->sh_size;
  table = (char *) get_data (NULL, file, sec->sh_offset,
			     size, _("unwind table"));
  if (!table)
    return 0;

  tep = aux->table = xmalloc (size / (3 * addr_size) * sizeof (aux->table[0]));
  for (tp = table; tp < table + size; tp += 3 * addr_size, ++tep)
    {
      tep->start.section = SHN_UNDEF;
      tep->end.section   = SHN_UNDEF;
      tep->info.section  = SHN_UNDEF;
      if (is_32bit_elf)
	{
	  tep->start.offset = byte_get ((unsigned char *) tp + 0, 4);
	  tep->end.offset   = byte_get ((unsigned char *) tp + 4, 4);
	  tep->info.offset  = byte_get ((unsigned char *) tp + 8, 4);
	}
      else
	{
	  tep->start.offset = BYTE_GET8 ((unsigned char *) tp +  0);
	  tep->end.offset   = BYTE_GET8 ((unsigned char *) tp +  8);
	  tep->info.offset  = BYTE_GET8 ((unsigned char *) tp + 16);
	}
      tep->start.offset += aux->seg_base;
      tep->end.offset   += aux->seg_base;
      tep->info.offset  += aux->seg_base;
    }
  VG_(free) (table);

  /* Third, apply any relocations to the unwind table: */

  for (relsec = section_headers;
       relsec < section_headers + elf_header.e_shnum;
       ++relsec)
    {
      if (relsec->sh_type != SHT_RELA
	  || SECTION_HEADER (relsec->sh_info) != sec)
	continue;

      if (!slurp_rela_relocs (file, relsec->sh_offset, relsec->sh_size,
			      & rela, & nrelas))
	return 0;

      for (rp = rela; rp < rela + nrelas; ++rp)
	{
	  if (is_32bit_elf)
	    {
	      relname = elf_ia64_reloc_type (ELF32_R_TYPE (rp->r_info));
	      sym = aux->symtab + ELF32_R_SYM (rp->r_info);

	      if (ELF32_ST_TYPE (sym->st_info) != STT_SECTION)
		{
		  warn (_("Skipping unexpected symbol type %u\n"),
			ELF32_ST_TYPE (sym->st_info));
		  continue;
		}
	    }
	  else
	    {
	      relname = elf_ia64_reloc_type (ELF64_R_TYPE (rp->r_info));
	      sym = aux->symtab + ELF64_R_SYM (rp->r_info);

	      if (ELF64_ST_TYPE (sym->st_info) != STT_SECTION)
		{
		  warn (_("Skipping unexpected symbol type %u\n"),
			ELF64_ST_TYPE (sym->st_info));
		  continue;
		}
	    }

	  if (VG_(strncmp) (relname, "R_IA64_SEGREL", 13) != 0)
	    {
	      warn (_("Skipping unexpected relocation type %s\n"), relname);
	      continue;
	    }

	  i = rp->r_offset / (3 * addr_size);

	  switch (rp->r_offset/addr_size % 3)
	    {
	    case 0:
	      aux->table[i].start.section = sym->st_shndx;
	      aux->table[i].start.offset += rp->r_addend;
	      break;
	    case 1:
	      aux->table[i].end.section   = sym->st_shndx;
	      aux->table[i].end.offset   += rp->r_addend;
	      break;
	    case 2:
	      aux->table[i].info.section  = sym->st_shndx;
	      aux->table[i].info.offset  += rp->r_addend;
	      break;
	    default:
	      break;
	    }
	}

      VG_(free) (rela);
    }

  aux->table_len = size / (3 * addr_size);
  return 1;
}

static int
process_unwind (file)
     FILE *file;
{
  Elf_Internal_Shdr *sec, *unwsec = NULL, *strsec;
  unsigned long i, addr_size, unwcount = 0, unwstart = 0;
  struct unw_aux_info aux;

  if (!do_unwind)
    return 1;

  if (elf_header.e_machine != EM_IA_64)
    {
      FJALAR_DPRINTF (_("\nThere are no unwind sections in this file.\n"));
      return 1;
    }

  VG_(memset) (& aux, 0, sizeof (aux));

  addr_size = is_32bit_elf ? 4 : 8;

  for (i = 0, sec = section_headers; i < elf_header.e_shnum; ++i, ++sec)
    {
      if (sec->sh_type == SHT_SYMTAB)
	{
	  aux.nsyms = sec->sh_size / sec->sh_entsize;
	  aux.symtab = GET_ELF_SYMBOLS (file, sec);

	  strsec = SECTION_HEADER (sec->sh_link);
	  aux.strtab_size = strsec->sh_size;
	  aux.strtab = (char *) get_data (NULL, file, strsec->sh_offset,
					  aux.strtab_size, _("string table"));
	}
      else if (sec->sh_type == SHT_IA_64_UNWIND)
	unwcount++;
    }

  if (!unwcount)
    FJALAR_DPRINTF (_("\nThere are no unwind sections in this file.\n"));

  while (unwcount-- > 0)
    {
      char *suffix;
      size_t len, len2;

      for (i = unwstart, sec = section_headers + unwstart;
	   i < elf_header.e_shnum; ++i, ++sec)
	if (sec->sh_type == SHT_IA_64_UNWIND)
	  {
	    unwsec = sec;
	    break;
	  }

      unwstart = i + 1;
      len = sizeof (ELF_STRING_ia64_unwind_once) - 1;

      if (VG_(strncmp) (SECTION_NAME (unwsec), ELF_STRING_ia64_unwind_once,
		   len) == 0)
	{
	  /* .gnu.linkonce.ia64unw.FOO -> .gnu.linkonce.ia64unwi.FOO */
	  len2 = sizeof (ELF_STRING_ia64_unwind_info_once) - 1;
	  suffix = SECTION_NAME (unwsec) + len;
	  for (i = 0, sec = section_headers; i < elf_header.e_shnum;
	       ++i, ++sec)
	    if (VG_(strncmp) (SECTION_NAME (sec),
			 ELF_STRING_ia64_unwind_info_once, len2) == 0
		&& VG_(strcmp) (SECTION_NAME (sec) + len2, suffix) == 0)
	      break;
	}
      else
	{
	  /* .IA_64.unwindFOO -> .IA_64.unwind_infoFOO
	     .IA_64.unwind or BAR -> .IA_64.unwind_info */
	  len = sizeof (ELF_STRING_ia64_unwind) - 1;
	  len2 = sizeof (ELF_STRING_ia64_unwind_info) - 1;
	  suffix = "";
	  if (VG_(strncmp) (SECTION_NAME (unwsec), ELF_STRING_ia64_unwind,
		       len) == 0)
	    suffix = SECTION_NAME (unwsec) + len;
	  for (i = 0, sec = section_headers; i < elf_header.e_shnum;
	       ++i, ++sec)
	    if (VG_(strncmp) (SECTION_NAME (sec),
			 ELF_STRING_ia64_unwind_info, len2) == 0
		&& VG_(strcmp) (SECTION_NAME (sec) + len2, suffix) == 0)
	      break;
	}

      if (i == elf_header.e_shnum)
	{
	  FJALAR_DPRINTF (_("\nCould not find unwind info section for "));

	  if (string_table == NULL)
	    FJALAR_DPRINTF ("%d", unwsec->sh_name);
	  else
	    FJALAR_DPRINTF (_("'%s'"), SECTION_NAME (unwsec));
	}
      else
	{
	  aux.info_size = sec->sh_size;
	  aux.info_addr = sec->sh_addr;
	  aux.info = (char *) get_data (NULL, file, sec->sh_offset,
					aux.info_size, _("unwind info"));

	  FJALAR_DPRINTF (_("\nUnwind section "));

	  if (string_table == NULL)
	    FJALAR_DPRINTF ("%d", unwsec->sh_name);
	  else
	    FJALAR_DPRINTF (_("'%s'"), SECTION_NAME (unwsec));

	  FJALAR_DPRINTF (_(" at offset 0x%lx contains %lu entries:\n"),
		  (unsigned long) unwsec->sh_offset,
		  (unsigned long) (unwsec->sh_size / (3 * addr_size)));

	  (void) slurp_ia64_unwind_table (file, & aux, unwsec);

	  if (aux.table_len > 0)
	    dump_ia64_unwind (& aux);

	  if (aux.table)
	    VG_(free) ((char *) aux.table);
	  if (aux.info)
	    VG_(free) ((char *) aux.info);
	  aux.table = NULL;
	  aux.info = NULL;
	}
    }

  if (aux.symtab)
    VG_(free) (aux.symtab);
  if (aux.strtab)
    VG_(free) ((char *) aux.strtab);

  return 1;
}

static void
dynamic_segment_mips_val (entry)
     Elf_Internal_Dyn *entry;
{
  switch (entry->d_tag)
    {
    default:
      FJALAR_DPRINTF ("%#lx\n", (long) entry->d_un.d_ptr);
    }
}


static void
dynamic_segment_parisc_val (entry)
     Elf_Internal_Dyn *entry;
{
  switch (entry->d_tag)
    {
    default:
      print_vma (entry->d_un.d_ptr, PREFIX_HEX);
      break;
    }
  putchar ('\n');
}

static void
dynamic_segment_ia64_val (entry)
     Elf_Internal_Dyn *entry;
{
  (void)entry; /* Quiet unused variable warning */
}

static int
get_32bit_dynamic_segment (file)
     FILE *file;
{
  Elf32_External_Dyn *edyn;
  Elf_Internal_Dyn *entry;
  bfd_size_type i;

  edyn = (Elf32_External_Dyn *) get_data (NULL, file, dynamic_addr,
					  dynamic_size, _("dynamic segment"));
  if (!edyn)
    return 0;

  /* SGI's ELF has more than one section in the DYNAMIC segment.  Determine
     how large this .dynamic is now.  We can do this even before the byte
     swapping since the DT_NULL tag is recognizable.  */
  dynamic_size = 0;
  while (*(Elf32_Word *) edyn[dynamic_size++].d_tag != DT_NULL)
    ;

  dynamic_segment = (Elf_Internal_Dyn *)
    VG_(malloc) ("readelf.c: get_32b_dynseg", dynamic_size * sizeof (Elf_Internal_Dyn));

  if (dynamic_segment == NULL)
    {
      error (_("Out of memory\n"));
      VG_(free) (edyn);
      return 0;
    }

  for (i = 0, entry = dynamic_segment;
       i < dynamic_size;
       i++, entry++)
    {
      entry->d_tag      = BYTE_GET (edyn[i].d_tag);
      entry->d_un.d_val = BYTE_GET (edyn[i].d_un.d_val);
    }

  VG_(free) (edyn);

  return 1;
}

static int
get_64bit_dynamic_segment (file)
     FILE *file;
{
  Elf64_External_Dyn *edyn;
  Elf_Internal_Dyn *entry;
  bfd_size_type i;

  edyn = (Elf64_External_Dyn *) get_data (NULL, file, dynamic_addr,
					  dynamic_size, _("dynamic segment"));
  if (!edyn)
    return 0;

  /* SGI's ELF has more than one section in the DYNAMIC segment.  Determine
     how large this .dynamic is now.  We can do this even before the byte
     swapping since the DT_NULL tag is recognizable.  */
  dynamic_size = 0;
  while (*(bfd_vma *) edyn[dynamic_size++].d_tag != DT_NULL)
    ;

  dynamic_segment = (Elf_Internal_Dyn *)
    VG_(malloc) ("readelf.c: get_64b_dynseg", dynamic_size * sizeof (Elf_Internal_Dyn));

  if (dynamic_segment == NULL)
    {
      error (_("Out of memory\n"));
      VG_(free) (edyn);
      return 0;
    }

  for (i = 0, entry = dynamic_segment;
       i < dynamic_size;
       i++, entry++)
    {
      entry->d_tag      = BYTE_GET8 (edyn[i].d_tag);
      entry->d_un.d_val = BYTE_GET8 (edyn[i].d_un.d_val);
    }

  VG_(free) (edyn);

  return 1;
}

static const char *
get_dynamic_flags (flags)
     bfd_vma flags;
{
  static char buff[128];
  char *p = buff;

  *p = '\0';
  while (flags)
    {
      bfd_vma flag;

      flag = flags & - flags;
      flags &= ~ flag;

      if (p != buff)
	*p++ = ' ';

      switch (flag)
	{
	case DF_ORIGIN:		VG_(strcpy) (p, "ORIGIN"); break;
	case DF_SYMBOLIC:	VG_(strcpy) (p, "SYMBOLIC"); break;
	case DF_TEXTREL:	VG_(strcpy) (p, "TEXTREL"); break;
	case DF_BIND_NOW:	VG_(strcpy) (p, "BIND_NOW"); break;
	case DF_STATIC_TLS:	VG_(strcpy) (p, "STATIC_TLS"); break;
	default:		VG_(strcpy) (p, "unknown"); break;
	}

      p = VG_(strchr) (p, '\0');
    }
  return buff;
}

/* Parse and display the contents of the dynamic segment.  */
static int
process_dynamic_segment (file)
     FILE *file;
{
  Elf_Internal_Dyn *entry;
  bfd_size_type i;

  if (dynamic_size == 0)
    {
      if (do_dynamic)
 FJALAR_DPRINTF (_("\nThere is no dynamic segment in this file.\n"));

      return 1;
    }

  if (is_32bit_elf)
    {
      if (! get_32bit_dynamic_segment (file))
	return 0;
    }
  else if (! get_64bit_dynamic_segment (file))
    return 0;

  /* Find the appropriate symbol table.  */
  if (dynamic_symbols == NULL)
    {
      for (i = 0, entry = dynamic_segment;
	   i < dynamic_size;
	   ++i, ++entry)
	{
	  Elf_Internal_Shdr section;

	  if (entry->d_tag != DT_SYMTAB)
	    continue;

	  dynamic_info[DT_SYMTAB] = entry->d_un.d_val;

	  /* Since we do not know how big the symbol table is,
	     we default to reading in the entire file (!) and
	     processing that.  This is overkill, I know, but it
	     should work.  */
	  section.sh_offset = entry->d_un.d_val - loadaddr;

	  if (fseek (file, 0, SEEK_END))
	    error (_("Unable to seek to end of file!"));

	  section.sh_size = ftell (file) - section.sh_offset;
	  if (is_32bit_elf)
	    section.sh_entsize = sizeof (Elf32_External_Sym);
	  else
	    section.sh_entsize = sizeof (Elf64_External_Sym);

	  num_dynamic_syms = section.sh_size / section.sh_entsize;
	  if (num_dynamic_syms < 1)
	    {
	      error (_("Unable to determine the number of symbols to load\n"));
	      continue;
	    }

	  dynamic_symbols = GET_ELF_SYMBOLS (file, &section);
	}
    }

  /* Similarly find a string table.  */
  if (dynamic_strings == NULL)
    {
      for (i = 0, entry = dynamic_segment;
	   i < dynamic_size;
	   ++i, ++entry)
	{
	  unsigned long offset;
	  long str_tab_len;

	  if (entry->d_tag != DT_STRTAB)
	    continue;

	  dynamic_info[DT_STRTAB] = entry->d_un.d_val;

	  /* Since we do not know how big the string table is,
	     we default to reading in the entire file (!) and
	     processing that.  This is overkill, I know, but it
	     should work.  */

	  offset = entry->d_un.d_val - loadaddr;
	  if (fseek (file, 0, SEEK_END))
	    error (_("Unable to seek to end of file\n"));
	  str_tab_len = ftell (file) - offset;

	  if (str_tab_len < 1)
	    {
	      error
		(_("Unable to determine the length of the dynamic string table\n"));
	      continue;
	    }

	  dynamic_strings = (char *) get_data (NULL, file, offset, str_tab_len,
					       _("dynamic string table"));
	  break;
	}
    }

  /* And find the syminfo section if available.  */
  if (dynamic_syminfo == NULL)
    {
      unsigned long syminsz = 0;

      for (i = 0, entry = dynamic_segment;
	   i < dynamic_size;
	   ++i, ++entry)
	{
	  if (entry->d_tag == DT_SYMINENT)
	    {
	      /* Note: these braces are necessary to avoid a syntax
		 error from the SunOS4 C compiler.  */
	      tl_assert (sizeof (Elf_External_Syminfo) == entry->d_un.d_val);
	    }
	  else if (entry->d_tag == DT_SYMINSZ)
	    syminsz = entry->d_un.d_val;
	  else if (entry->d_tag == DT_SYMINFO)
	    dynamic_syminfo_offset = entry->d_un.d_val - loadaddr;
	}

      if (dynamic_syminfo_offset != 0 && syminsz != 0)
	{
	  Elf_External_Syminfo *extsyminfo;
	  Elf_Internal_Syminfo *syminfo;

	  /* There is a syminfo section.  Read the data.  */
	  extsyminfo = ((Elf_External_Syminfo *)
			get_data (NULL, file, dynamic_syminfo_offset,
				  syminsz, _("symbol information")));
	  if (!extsyminfo)
	    return 0;

	  dynamic_syminfo = (Elf_Internal_Syminfo *) VG_(malloc) ("readelf.c: proc_dynseg", syminsz);
	  if (dynamic_syminfo == NULL)
	    {
	      error (_("Out of memory\n"));
	      return 0;
	    }

	  dynamic_syminfo_nent = syminsz / sizeof (Elf_External_Syminfo);
	  for (i = 0, syminfo = dynamic_syminfo; i < dynamic_syminfo_nent;
	       ++i, ++syminfo)
	    {
	      syminfo->si_boundto = BYTE_GET (extsyminfo[i].si_boundto);
	      syminfo->si_flags = BYTE_GET (extsyminfo[i].si_flags);
	    }

	  VG_(free) (extsyminfo);
	}
    }

  if (do_dynamic && dynamic_addr)
    FJALAR_DPRINTF (_("\nDynamic segment at offset 0x%lx contains %ld entries:\n"),
	    dynamic_addr, (long) dynamic_size);
  if (do_dynamic)
    FJALAR_DPRINTF (_("  Tag        Type                         Name/Value\n"));

  for (i = 0, entry = dynamic_segment;
       i < dynamic_size;
       i++, entry++)
    {
      if (do_dynamic)
	{
	  const char *dtype;

	  putchar (' ');
	  print_vma (entry->d_tag, FULL_HEX);
	  dtype = get_dynamic_type (entry->d_tag);
	  FJALAR_DPRINTF (" (%s)%*s", dtype,
		  ((is_32bit_elf ? 27 : 19)
		   - (int) VG_(strlen) (dtype)),
		  " ");
	}

      switch (entry->d_tag)
	{
	case DT_FLAGS:
	  if (do_dynamic)
	    puts (get_dynamic_flags (entry->d_un.d_val));
	  break;

	case DT_AUXILIARY:
	case DT_FILTER:
	case DT_CONFIG:
	case DT_DEPAUDIT:
	case DT_AUDIT:
	  if (do_dynamic)
	    {
	      switch (entry->d_tag)
		{
		case DT_AUXILIARY:
		  FJALAR_DPRINTF (_("Auxiliary library"));
		  break;

		case DT_FILTER:
		  FJALAR_DPRINTF (_("Filter library"));
		  break;

		case DT_CONFIG:
		  FJALAR_DPRINTF (_("Configuration file"));
		  break;

		case DT_DEPAUDIT:
		  FJALAR_DPRINTF (_("Dependency audit library"));
		  break;

		case DT_AUDIT:
		  FJALAR_DPRINTF (_("Audit library"));
		  break;
		}

	      if (dynamic_strings)
	 FJALAR_DPRINTF (": [%s]\n", dynamic_strings + entry->d_un.d_val);
	      else
		{
		  FJALAR_DPRINTF (": ");
		  print_vma (entry->d_un.d_val, PREFIX_HEX);
		  putchar ('\n');
		}
	    }
	  break;

	case DT_FEATURE:
	  if (do_dynamic)
	    {
	      FJALAR_DPRINTF (_("Flags:"));

	      if (entry->d_un.d_val == 0)
	 FJALAR_DPRINTF (_(" None\n"));
	      else
		{
		  unsigned long int val = entry->d_un.d_val;

		  if (val & DTF_1_PARINIT)
		    {
		      FJALAR_DPRINTF (" PARINIT");
		      val ^= DTF_1_PARINIT;
		    }
		  if (val & DTF_1_CONFEXP)
		    {
		      FJALAR_DPRINTF (" CONFEXP");
		      val ^= DTF_1_CONFEXP;
		    }
		  if (val != 0)
		    FJALAR_DPRINTF (" %lx", val);
		  puts ("");
		}
	    }
	  break;

	case DT_POSFLAG_1:
	  if (do_dynamic)
	    {
	      FJALAR_DPRINTF (_("Flags:"));

	      if (entry->d_un.d_val == 0)
	 FJALAR_DPRINTF (_(" None\n"));
	      else
		{
		  unsigned long int val = entry->d_un.d_val;

		  if (val & DF_P1_LAZYLOAD)
		    {
		      FJALAR_DPRINTF (" LAZYLOAD");
		      val ^= DF_P1_LAZYLOAD;
		    }
		  if (val & DF_P1_GROUPPERM)
		    {
		      FJALAR_DPRINTF (" GROUPPERM");
		      val ^= DF_P1_GROUPPERM;
		    }
		  if (val != 0)
		    FJALAR_DPRINTF (" %lx", val);
		  puts ("");
		}
	    }
	  break;

	case DT_FLAGS_1:
	  if (do_dynamic)
	    {
	      FJALAR_DPRINTF (_("Flags:"));
	      if (entry->d_un.d_val == 0)
	 FJALAR_DPRINTF (_(" None\n"));
	      else
		{
		  unsigned long int val = entry->d_un.d_val;

		  if (val & DF_1_NOW)
		    {
		      FJALAR_DPRINTF (" NOW");
		      val ^= DF_1_NOW;
		    }
		  if (val & DF_1_GLOBAL)
		    {
		      FJALAR_DPRINTF (" GLOBAL");
		      val ^= DF_1_GLOBAL;
		    }
		  if (val & DF_1_GROUP)
		    {
		      FJALAR_DPRINTF (" GROUP");
		      val ^= DF_1_GROUP;
		    }
		  if (val & DF_1_NODELETE)
		    {
		      FJALAR_DPRINTF (" NODELETE");
		      val ^= DF_1_NODELETE;
		    }
		  if (val & DF_1_LOADFLTR)
		    {
		      FJALAR_DPRINTF (" LOADFLTR");
		      val ^= DF_1_LOADFLTR;
		    }
		  if (val & DF_1_INITFIRST)
		    {
		      FJALAR_DPRINTF (" INITFIRST");
		      val ^= DF_1_INITFIRST;
		    }
		  if (val & DF_1_NOOPEN)
		    {
		      FJALAR_DPRINTF (" NOOPEN");
		      val ^= DF_1_NOOPEN;
		    }
		  if (val & DF_1_ORIGIN)
		    {
		      FJALAR_DPRINTF (" ORIGIN");
		      val ^= DF_1_ORIGIN;
		    }
		  if (val & DF_1_DIRECT)
		    {
		      FJALAR_DPRINTF (" DIRECT");
		      val ^= DF_1_DIRECT;
		    }
		  if (val & DF_1_TRANS)
		    {
		      FJALAR_DPRINTF (" TRANS");
		      val ^= DF_1_TRANS;
		    }
		  if (val & DF_1_INTERPOSE)
		    {
		      FJALAR_DPRINTF (" INTERPOSE");
		      val ^= DF_1_INTERPOSE;
		    }
		  if (val & DF_1_NODEFLIB)
		    {
		      FJALAR_DPRINTF (" NODEFLIB");
		      val ^= DF_1_NODEFLIB;
		    }
		  if (val & DF_1_NODUMP)
		    {
		      FJALAR_DPRINTF (" NODUMP");
		      val ^= DF_1_NODUMP;
		    }
		  if (val & DF_1_CONLFAT)
		    {
		      FJALAR_DPRINTF (" CONLFAT");
		      val ^= DF_1_CONLFAT;
		    }
		  if (val != 0)
		    FJALAR_DPRINTF (" %lx", val);
		  puts ("");
		}
	    }
	  break;

	case DT_PLTREL:
	  dynamic_info[entry->d_tag] = entry->d_un.d_val;
	  if (do_dynamic)
	    puts (get_dynamic_type (entry->d_un.d_val));
	  break;

	case DT_NULL	:
	case DT_NEEDED	:
	case DT_PLTGOT	:
	case DT_HASH	:
	case DT_STRTAB	:
	case DT_SYMTAB	:
	case DT_RELA	:
	case DT_INIT	:
	case DT_FINI	:
	case DT_SONAME	:
	case DT_RPATH	:
	case DT_SYMBOLIC:
	case DT_REL	:
	case DT_DEBUG	:
	case DT_TEXTREL	:
	case DT_JMPREL	:
	case DT_RUNPATH	:
	  dynamic_info[entry->d_tag] = entry->d_un.d_val;

	  if (do_dynamic)
	    {
	      char *name;

	      if (dynamic_strings == NULL)
		name = NULL;
	      else
		name = dynamic_strings + entry->d_un.d_val;

	      if (name)
		{
		  switch (entry->d_tag)
		    {
		    case DT_NEEDED:
		      FJALAR_DPRINTF (_("Shared library: [%s]"), name);

		      if (VG_(strcmp) (name, program_interpreter) == 0)
		 FJALAR_DPRINTF (_(" program interpreter"));
		      break;

		    case DT_SONAME:
		      FJALAR_DPRINTF (_("Library soname: [%s]"), name);
		      break;

		    case DT_RPATH:
		      FJALAR_DPRINTF (_("Library rpath: [%s]"), name);
		      break;

		    case DT_RUNPATH:
		      FJALAR_DPRINTF (_("Library runpath: [%s]"), name);
		      break;

		    default:
		      print_vma (entry->d_un.d_val, PREFIX_HEX);
		      break;
		    }
		}
	      else
		print_vma (entry->d_un.d_val, PREFIX_HEX);

	      putchar ('\n');
	    }
	  break;

	case DT_PLTRELSZ:
	case DT_RELASZ	:
	case DT_STRSZ	:
	case DT_RELSZ	:
	case DT_RELAENT	:
	case DT_SYMENT	:
	case DT_RELENT	:
	  dynamic_info[entry->d_tag] = entry->d_un.d_val;
	case DT_PLTPADSZ:
	case DT_MOVEENT	:
	case DT_MOVESZ	:
	case DT_INIT_ARRAYSZ:
	case DT_FINI_ARRAYSZ:
	case DT_GNU_CONFLICTSZ:
	case DT_GNU_LIBLISTSZ:
	  if (do_dynamic)
	    {
	      print_vma (entry->d_un.d_val, UNSIGNED);
	      FJALAR_DPRINTF (" (bytes)\n");
	    }
	  break;

	case DT_VERDEFNUM:
	case DT_VERNEEDNUM:
	case DT_RELACOUNT:
	case DT_RELCOUNT:
	  if (do_dynamic)
	    {
	      print_vma (entry->d_un.d_val, UNSIGNED);
	      putchar ('\n');
	    }
	  break;

	case DT_SYMINSZ:
	case DT_SYMINENT:
	case DT_SYMINFO:
	case DT_USED:
	case DT_INIT_ARRAY:
	case DT_FINI_ARRAY:
	  if (do_dynamic)
	    {
	      if (dynamic_strings != NULL && entry->d_tag == DT_USED)
		{
		  char *name;

		  name = dynamic_strings + entry->d_un.d_val;

		  if (*name)
		    {
		      FJALAR_DPRINTF (_("Not needed object: [%s]\n"), name);
		      break;
		    }
		}

	      print_vma (entry->d_un.d_val, PREFIX_HEX);
	      putchar ('\n');
	    }
	  break;

	case DT_BIND_NOW:
	  /* The value of this entry is ignored.  */
	  if (do_dynamic)
	    putchar ('\n');
	  break;

	case DT_GNU_PRELINKED:
	  break;

	default:
	  if ((entry->d_tag >= DT_VERSYM) && (entry->d_tag <= DT_VERNEEDNUM))
	    version_info[DT_VERSIONTAGIDX (entry->d_tag)] =
	      entry->d_un.d_val;

	  if (do_dynamic)
	    {
	      switch (elf_header.e_machine)
		{
		case EM_MIPS:
		case EM_MIPS_RS3_LE:
		  dynamic_segment_mips_val (entry);
		  break;
		case EM_PARISC:
		  dynamic_segment_parisc_val (entry);
		  break;
		case EM_IA_64:
		  dynamic_segment_ia64_val (entry);
		  break;
		default:
		  print_vma (entry->d_un.d_val, PREFIX_HEX);
		  putchar ('\n');
		}
	    }
	  break;
	}
    }

  return 1;
}

static char *
get_ver_flags (flags)
     unsigned int flags;
{
  static char buff[32];

  buff[0] = 0;

  if (flags == 0)
    return _("none");

  if (flags & VER_FLG_BASE)
    VG_(strcat) (buff, "BASE ");

  if (flags & VER_FLG_WEAK)
    {
      if (flags & VER_FLG_BASE)
	VG_(strcat) (buff, "| ");

      VG_(strcat) (buff, "WEAK ");
    }

  if (flags & ~(VER_FLG_BASE | VER_FLG_WEAK))
    VG_(strcat) (buff, "| <unknown>");

  return buff;
}

/* Display the contents of the version sections.  */
static int
process_version_sections (file)
     FILE *file;
{
  Elf_Internal_Shdr *section;
  unsigned i;
  int found = 0;

  if (! do_version)
    return 1;

  for (i = 0, section = section_headers;
       i < elf_header.e_shnum;
       i++, section++)
    {
      switch (section->sh_type)
	{
	case SHT_GNU_verdef:
	  {
	    Elf_External_Verdef *edefs;
	    unsigned int idx;
	    unsigned int cnt;

	    found = 1;

	    FJALAR_DPRINTF
	      (_("\nVersion definition section '%s' contains %ld entries:\n"),
	       SECTION_NAME (section), section->sh_info);

	    FJALAR_DPRINTF (_("  Addr: 0x"));
	    printf_vma (section->sh_addr);
	    FJALAR_DPRINTF (_("  Offset: %#08lx  Link: %lx (%s)\n"),
		    (unsigned long) section->sh_offset, section->sh_link,
		    SECTION_NAME (SECTION_HEADER (section->sh_link)));

	    edefs = ((Elf_External_Verdef *)
		     get_data (NULL, file, section->sh_offset,
			       section->sh_size,
			       _("version definition section")));
	    if (!edefs)
	      break;

	    for (idx = cnt = 0; cnt < section->sh_info; ++cnt)
	      {
		char *vstart;
		Elf_External_Verdef *edef;
		Elf_Internal_Verdef ent;
		Elf_External_Verdaux *eaux;
		Elf_Internal_Verdaux aux;
		int j;
		int isum;

		vstart = ((char *) edefs) + idx;

		edef = (Elf_External_Verdef *) vstart;

		ent.vd_version = BYTE_GET (edef->vd_version);
		ent.vd_flags   = BYTE_GET (edef->vd_flags);
		ent.vd_ndx     = BYTE_GET (edef->vd_ndx);
		ent.vd_cnt     = BYTE_GET (edef->vd_cnt);
		ent.vd_hash    = BYTE_GET (edef->vd_hash);
		ent.vd_aux     = BYTE_GET (edef->vd_aux);
		ent.vd_next    = BYTE_GET (edef->vd_next);

	 FJALAR_DPRINTF (_("  %#06x: Rev: %d  Flags: %s"),
			idx, ent.vd_version, get_ver_flags (ent.vd_flags));

	 FJALAR_DPRINTF (_("  Index: %d  Cnt: %d  "),
			ent.vd_ndx, ent.vd_cnt);

		vstart += ent.vd_aux;

		eaux = (Elf_External_Verdaux *) vstart;

		aux.vda_name = BYTE_GET (eaux->vda_name);
		aux.vda_next = BYTE_GET (eaux->vda_next);

		if (dynamic_strings)
		  FJALAR_DPRINTF (_("Name: %s\n"), dynamic_strings + aux.vda_name);
		else
		  FJALAR_DPRINTF (_("Name index: %ld\n"), aux.vda_name);

		isum = idx + ent.vd_aux;

		for (j = 1; j < ent.vd_cnt; j++)
		  {
		    isum   += aux.vda_next;
		    vstart += aux.vda_next;

		    eaux = (Elf_External_Verdaux *) vstart;

		    aux.vda_name = BYTE_GET (eaux->vda_name);
		    aux.vda_next = BYTE_GET (eaux->vda_next);

		    if (dynamic_strings)
		      FJALAR_DPRINTF (_("  %#06x: Parent %d: %s\n"),
			      isum, j, dynamic_strings + aux.vda_name);
		    else
		      FJALAR_DPRINTF (_("  %#06x: Parent %d, name index: %ld\n"),
			      isum, j, aux.vda_name);
		  }

		idx += ent.vd_next;
	      }

	    VG_(free) (edefs);
	  }
	  break;

	case SHT_GNU_verneed:
	  {
	    Elf_External_Verneed *eneed;
	    unsigned int idx;
	    unsigned int cnt;

	    found = 1;

	    FJALAR_DPRINTF (_("\nVersion needs section '%s' contains %ld entries:\n"),
		    SECTION_NAME (section), section->sh_info);

	    FJALAR_DPRINTF (_(" Addr: 0x"));
	    printf_vma (section->sh_addr);
	    FJALAR_DPRINTF (_("  Offset: %#08lx  Link to section: %ld (%s)\n"),
		    (unsigned long) section->sh_offset, section->sh_link,
		    SECTION_NAME (SECTION_HEADER (section->sh_link)));

	    eneed = ((Elf_External_Verneed *)
		     get_data (NULL, file, section->sh_offset,
			       section->sh_size, _("version need section")));
	    if (!eneed)
	      break;

	    for (idx = cnt = 0; cnt < section->sh_info; ++cnt)
	      {
		Elf_External_Verneed *entry;
		Elf_Internal_Verneed ent;
		int j;
		int isum;
		char *vstart;

		vstart = ((char *) eneed) + idx;

		entry = (Elf_External_Verneed *) vstart;

		ent.vn_version = BYTE_GET (entry->vn_version);
		ent.vn_cnt     = BYTE_GET (entry->vn_cnt);
		ent.vn_file    = BYTE_GET (entry->vn_file);
		ent.vn_aux     = BYTE_GET (entry->vn_aux);
		ent.vn_next    = BYTE_GET (entry->vn_next);

	 FJALAR_DPRINTF (_("  %#06x: Version: %d"), idx, ent.vn_version);

		if (dynamic_strings)
		  FJALAR_DPRINTF (_("  File: %s"), dynamic_strings + ent.vn_file);
		else
		  FJALAR_DPRINTF (_("  File: %lx"), ent.vn_file);

	 FJALAR_DPRINTF (_("  Cnt: %d\n"), ent.vn_cnt);

		vstart += ent.vn_aux;

		for (j = 0, isum = idx + ent.vn_aux; j < ent.vn_cnt; ++j)
		  {
		    Elf_External_Vernaux *eaux;
		    Elf_Internal_Vernaux aux;

		    eaux = (Elf_External_Vernaux *) vstart;

		    aux.vna_hash  = BYTE_GET (eaux->vna_hash);
		    aux.vna_flags = BYTE_GET (eaux->vna_flags);
		    aux.vna_other = BYTE_GET (eaux->vna_other);
		    aux.vna_name  = BYTE_GET (eaux->vna_name);
		    aux.vna_next  = BYTE_GET (eaux->vna_next);

		    if (dynamic_strings)
		      FJALAR_DPRINTF (_("  %#06x: Name: %s"),
			      isum, dynamic_strings + aux.vna_name);
		    else
		      FJALAR_DPRINTF (_("  %#06x: Name index: %lx"),
			      isum, aux.vna_name);

		    FJALAR_DPRINTF (_("  Flags: %s  Version: %d\n"),
			    get_ver_flags (aux.vna_flags), aux.vna_other);

		    isum   += aux.vna_next;
		    vstart += aux.vna_next;
		  }

		idx += ent.vn_next;
	      }

	    VG_(free) (eneed);
	  }
	  break;

	case SHT_GNU_versym:
	  {
	    Elf_Internal_Shdr *link_section;
	    int total;
	    int cnt;
	    unsigned char *edata;
	    unsigned short *data;
	    char *strtab;
	    Elf_Internal_Sym *symbols;
	    Elf_Internal_Shdr *string_sec;

	    link_section = SECTION_HEADER (section->sh_link);
	    total = section->sh_size / section->sh_entsize;

	    found = 1;

	    symbols = GET_ELF_SYMBOLS (file, link_section);

	    string_sec = SECTION_HEADER (link_section->sh_link);

	    strtab = (char *) get_data (NULL, file, string_sec->sh_offset,
					string_sec->sh_size,
					_("version string table"));
	    if (!strtab)
	      break;

	    FJALAR_DPRINTF (_("\nVersion symbols section '%s' contains %d entries:\n"),
		    SECTION_NAME (section), total);

	    FJALAR_DPRINTF (_(" Addr: "));
	    printf_vma (section->sh_addr);
	    FJALAR_DPRINTF (_("  Offset: %#08lx  Link: %lx (%s)\n"),
		    (unsigned long) section->sh_offset, section->sh_link,
		    SECTION_NAME (link_section));

	    edata =
	      ((unsigned char *)
	       get_data (NULL, file,
			 version_info[DT_VERSIONTAGIDX (DT_VERSYM)] - loadaddr,
			 total * sizeof (short), _("version symbol data")));
	    if (!edata)
	      {
		VG_(free) (strtab);
		break;
	      }

	    data = (unsigned short *) VG_(malloc) ("readelf.c: get_verflag", total * sizeof (short));

	    for (cnt = total; cnt --;)
	      data[cnt] = byte_get (edata + cnt * sizeof (short),
				    sizeof (short));

	    VG_(free) (edata);

	    for (cnt = 0; cnt < total; cnt += 4)
	      {
		int j, nn = 0;
		int check_def, check_need;
		char *name;

                FJALAR_DPRINTF ("  %03x:", cnt);

		for (j = 0; (j < 4) && (cnt + j) < total; ++j)
		  switch (data[cnt + j])
		    {
		    case 0:
		      fputs (_("   0 (*local*)    "), stdout);
		      break;

		    case 1:
		      fputs (_("   1 (*global*)   "), stdout);
		      break;

		    default:
		      if(fjalar_debug) {
			nn = printf ("4%x%c", data[cnt + j] & 0x7fff,
				     data[cnt + j] & 0x8000 ? 'h' : ' ');
		      }

		      check_def = 1;
		      check_need = 1;
		      if (SECTION_HEADER (symbols[cnt + j].st_shndx)->sh_type
			  != SHT_NOBITS)
			{
			  if (symbols[cnt + j].st_shndx == SHN_UNDEF)
			    check_def = 0;
			  else
			    check_need = 0;
			}

		      if (check_need
			  && version_info[DT_VERSIONTAGIDX (DT_VERNEED)])
			{
			  Elf_Internal_Verneed ivn;
			  unsigned long offset;

			  offset = version_info[DT_VERSIONTAGIDX (DT_VERNEED)]
			    - loadaddr;

			  do
			    {
			      Elf_Internal_Vernaux ivna;
			      Elf_External_Verneed evn;
			      Elf_External_Vernaux evna;
			      unsigned long a_off;

			      get_data (&evn, file, offset, sizeof (evn),
					_("version need"));

			      ivn.vn_aux  = BYTE_GET (evn.vn_aux);
			      ivn.vn_next = BYTE_GET (evn.vn_next);

			      a_off = offset + ivn.vn_aux;

			      do
				{
				  get_data (&evna, file, a_off, sizeof (evna),
					    _("version need aux (2)"));

				  ivna.vna_next  = BYTE_GET (evna.vna_next);
				  ivna.vna_other = BYTE_GET (evna.vna_other);

				  a_off += ivna.vna_next;
				}
			      while (ivna.vna_other != data[cnt + j]
				     && ivna.vna_next != 0);

			      if (ivna.vna_other == data[cnt + j])
				{
				  ivna.vna_name = BYTE_GET (evna.vna_name);

				  name = strtab + ivna.vna_name;
				  if(fjalar_debug) {
				    nn += printf ("(%s%-*s",
						  name,
						  12 - (int) VG_(strlen) (name),
						  ")");
				  }
				  check_def = 0;
				  break;
				}

			      offset += ivn.vn_next;
			    }
			  while (ivn.vn_next);
			}

		      if (check_def && data[cnt + j] != 0x8001
			  && version_info[DT_VERSIONTAGIDX (DT_VERDEF)])
			{
			  Elf_Internal_Verdef ivd;
			  Elf_External_Verdef evd;
			  unsigned long offset;

			  offset = (version_info[DT_VERSIONTAGIDX (DT_VERDEF)]
				    - loadaddr);

			  do
			    {
			      get_data (&evd, file, offset, sizeof (evd),
					_("version def"));

			      ivd.vd_next = BYTE_GET (evd.vd_next);
			      ivd.vd_ndx  = BYTE_GET (evd.vd_ndx);

			      offset += ivd.vd_next;
			    }
			  while (ivd.vd_ndx != (data[cnt + j] & 0x7fff)
				 && ivd.vd_next != 0);

			  if (ivd.vd_ndx == (data[cnt + j] & 0x7fff))
			    {
			      Elf_External_Verdaux evda;
			      Elf_Internal_Verdaux ivda;

			      ivd.vd_aux = BYTE_GET (evd.vd_aux);

			      get_data (&evda, file,
					offset - ivd.vd_next + ivd.vd_aux,
					sizeof (evda), _("version def aux"));

			      ivda.vda_name = BYTE_GET (evda.vda_name);

			      name = strtab + ivda.vda_name;
			      if(fjalar_debug) {
				nn += printf ("(%s%-*s",
					      name,
					      12 - (int) VG_(strlen) (name),
					      ")");
			      }
			    }
			}

		      if (nn < 18)
		 FJALAR_DPRINTF ("%*c", 18 - nn, ' ');
		    }

		putchar ('\n');
	      }

	    VG_(free) (data);
	    VG_(free) (strtab);
	    VG_(free) (symbols);
	  }
	  break;

	default:
	  break;
	}
    }

  if (! found)
    FJALAR_DPRINTF (_("\nNo version information found in this file.\n"));

  return 1;
}

static int *
get_dynamic_data (file, number)
     FILE *file;
     unsigned int number;
{
  unsigned char *e_data;
  int *i_data;

  e_data = (unsigned char *) VG_(malloc) ("readelf.c: get_dyndata", number * 4);

  if (e_data == NULL)
    {
      error (_("Out of memory\n"));
      return NULL;
    }

  if (fread (e_data, 4, number, file) != number)
    {
      error (_("Unable to read in dynamic data\n"));
      return NULL;
    }

  i_data = (int *) VG_(malloc) ("readelf.c: get_dyndata.2", number * sizeof (*i_data));

  if (i_data == NULL)
    {
      error (_("Out of memory\n"));
      VG_(free) (e_data);
      return NULL;
    }

  while (number--)
    i_data[number] = byte_get (e_data + number * 4, 4);

  VG_(free) (e_data);

  return i_data;
}

/* Dump the symbol table.  */
static int
process_symbol_table (file)
     FILE *file;
{
  Elf_Internal_Shdr *section;
  unsigned char nb[4];
  unsigned char nc[4];
  int nbuckets = 0;
  int nchains = 0;
  int *buckets = NULL;
  int *chains = NULL;

  //  VG_(printf)("\n\nprocess_symbol_table - do_syms: %d do_histogram: %d\n\n",
  //              do_syms, do_histogram);

  if (! do_syms && !do_histogram)
    return 1;

  if (dynamic_info[DT_HASH] && ((do_using_dynamic && dynamic_strings != NULL)
				|| do_histogram))
    {
      if (fseek (file, dynamic_info[DT_HASH] - loadaddr, SEEK_SET))
	{
	  error (_("Unable to seek to start of dynamic information"));
	  return 0;
	}

      if (fread (nb, sizeof (nb), 1, file) != 1)
	{
	  error (_("Failed to read in number of buckets\n"));
	  return 0;
	}

      if (fread (nc, sizeof (nc), 1, file) != 1)
	{
	  error (_("Failed to read in number of chains\n"));
	  return 0;
	}

      nbuckets = byte_get (nb, 4);
      nchains  = byte_get (nc, 4);

      buckets = get_dynamic_data (file, nbuckets);
      chains  = get_dynamic_data (file, nchains);

      if (buckets == NULL || chains == NULL)
	return 0;
    }

  if (do_syms
      && dynamic_info[DT_HASH] && do_using_dynamic && dynamic_strings != NULL)
    {
      //      int hn;
      //      int si;

      //      FJALAR_DPRINTF (_("\nSymbol table for image:\n"));
      //      if (is_32bit_elf)
      // FJALAR_DPRINTF (_("  Num Buc:    Value  Size   Type   Bind Vis      Ndx Name\n"));
      //      else
      // FJALAR_DPRINTF (_("  Num Buc:    Value          Size   Type   Bind Vis      Ndx Name\n"));

      //      for (hn = 0; hn < nbuckets; hn++)
      //	{
      //	  if (! buckets[hn])
      //	    continue;
      //
      //	  for (si = buckets[hn]; si < nchains && si > 0; si = chains[si])
      //	    {
      //	      Elf_Internal_Sym *psym;
      //
      //	      psym = dynamic_symbols + si;
      //
      //              //printf ("  %3d %3d: ", si, hn);
      //              print_vma (psym->st_value, LONG_HEX);
      //      putchar (' ' );
      //      print_vma (psym->st_size, DEC_5);
      //
      //      //printf ("  %6s", get_symbol_type (ELF_ST_TYPE (psym->st_info)));
      //      //printf (" %6s",  get_symbol_binding (ELF_ST_BIND (psym->st_info)));
      //      //printf (" %3s",  get_symbol_visibility (ELF_ST_VISIBILITY (psym->st_other)));
      //      //printf (" %3.3s ", get_symbol_index_type (psym->st_shndx));
      //      print_symbol (25, dynamic_strings + psym->st_name);
      //      putchar ('\n');
      //  }
      //}
    }
  else if (do_syms && !do_using_dynamic)
    {
      unsigned int i;

      for (i = 0, section = section_headers;
	   i < elf_header.e_shnum;
	   i++, section++)
	{
	  unsigned int si;
	  char *strtab;
	  Elf_Internal_Sym *symtab;
	  Elf_Internal_Sym *psym;

	  //	  VG_(printf) (_("'%s'\n"), SECTION_NAME (section));

          // PG - harvest address and size information for the .data,
          // .bss, and .rodata sections:
          if (0 == VG_(strcmp)(SECTION_NAME (section), ".data")) {
            data_section_addr = section->sh_addr;
            data_section_size = section->sh_size;
          }
          else if (0 == VG_(strcmp)(SECTION_NAME (section), ".bss")) {
            bss_section_addr = section->sh_addr;
            bss_section_size = section->sh_size;
          }
          else if (0 == VG_(strcmp)(SECTION_NAME (section), ".rodata")) {
            rodata_section_addr = section->sh_addr;
            rodata_section_size = section->sh_size;
          } else if (0 == VG_(strcmp)(SECTION_NAME (section), ".data.rel.ro")) {
	    // Rudd - There's another section known as .data.del.ro
	    // It's similar in semantics to the .data section, but is used for
	    // globals that need to appear constant at runtime but have to be
	    // relocated first.
	    relrodata_section_addr = section->sh_addr;
            relrodata_section_size = section->sh_size;
	  }
          // PG - only look for symbols in the regular symbol table
          // (.symtab), NOT the dynamic symbols (.dynsym), because
          // they seem to contain lots of library junk:
	  if (section->sh_type != SHT_SYMTAB) {
	    continue;
          }

          //	  if (   section->sh_type != SHT_SYMTAB
          //	      && section->sh_type != SHT_DYNSYM)
          //	    continue;

          //	  VG_(printf) (_("\nSymbol table '%s' contains %lu entries:\n"),
          //          		  SECTION_NAME (section),
          //          		  (unsigned long) (section->sh_size / section->sh_entsize));
          //          if (is_32bit_elf)
          //	    VG_(printf) (_("   Num:    Value  Size Type    Bind   Vis      Ndx Name\n"));
          //          else
          //	    VG_(printf) (_("   Num:    Value          Size Type    Bind   Vis      Ndx Name\n"));

	  symtab = GET_ELF_SYMBOLS (file, section);
	  if (symtab == NULL)
	    continue;

	  if (section->sh_link == elf_header.e_shstrndx)
	    strtab = string_table;
	  else
	    {
	      Elf_Internal_Shdr *string_sec;

	      string_sec = SECTION_HEADER (section->sh_link);

	      strtab = (char *) get_data (NULL, file, string_sec->sh_offset,
					  string_sec->sh_size,
					  _("string table"));
	    }

	  for (si = 0, psym = symtab;
	       si < section->sh_size / section->sh_entsize;
	       si++, psym++)
	    {
              // DEPRECATED!  We no longer do this!

              //              // Ignore all entries which aren't "FUNC" or have an address of 0:
              //              if ((VG_(strcmp)((get_symbol_type (ELF_ST_TYPE (psym->st_info))),
              //                               "FUNC")) ||
              //                  (!psym->st_value)){
              //                continue;
              //              }


              // PG - harvest object symbols so that we can get
              // addresses for global and C++ static class variables
              // and non-static function start addresses (we can get
              // this from DWARF info, but it's a good sanity check)
              // Don't harvest "HIDDEN" entries (just a heuristic) and
              // also don't harvest entries with a 0 value because
              // that's probably useless (yet another heuristic):
              if (((STT_OBJECT == ELF_ST_TYPE (psym->st_info)) ||
                   (STT_FUNC == ELF_ST_TYPE (psym->st_info))) &&
                  psym->st_value &&
                  (STV_HIDDEN != ELF_ST_VISIBILITY (psym->st_other))) {

                // PG - remember that this is strdup'ed!
                char* symbol_name = VG_(strdup)("readelf.c: proc_symtable", &strtab[psym->st_name]);

                if (STT_OBJECT == ELF_ST_TYPE (psym->st_info)) {
                  insertIntoVariableSymbolTable(symbol_name,
						(void *)(int)psym->st_value);
                }
                else if (STT_FUNC == ELF_ST_TYPE (psym->st_info)) {
                  insertIntoFunctionSymbolTable(symbol_name,
						(void *)(int)psym->st_value);
                }
              }

	      //printf ("%6d: ", si);
              //print_vma (psym->st_value, LONG_HEX);
              //putchar (' ');
	      //print_vma (psym->st_size, DEC_5);
	      //printf (" %-7s", get_symbol_type (ELF_ST_TYPE (psym->st_info)));
	      //printf (" %-6s", get_symbol_binding (ELF_ST_BIND (psym->st_info)));
	      //printf (" %-3s", get_symbol_visibility (ELF_ST_VISIBILITY (psym->st_other)));
	      //printf (" %4s ", get_symbol_index_type (psym->st_shndx));
	      //print_symbol (25, strtab + psym->st_name);

/* 	      if (section->sh_type == SHT_DYNSYM && */
/* 		  version_info[DT_VERSIONTAGIDX (DT_VERSYM)] != 0) */
/* 		{ */
/* 		  unsigned char data[2]; */
/* 		  unsigned short vers_data; */
/* 		  unsigned long offset; */
/* 		  int is_nobits; */
/* 		  int check_def; */

/* 		  offset = version_info[DT_VERSIONTAGIDX (DT_VERSYM)] */
/* 		    - loadaddr; */

/* 		  get_data (&data, file, offset + si * sizeof (vers_data), */
/* 			    sizeof (data), _("version data")); */

/* 		  vers_data = byte_get (data, 2); */

/* 		  is_nobits = (SECTION_HEADER (psym->st_shndx)->sh_type */
/* 			       == SHT_NOBITS); */

/* 		  check_def = (psym->st_shndx != SHN_UNDEF); */

/* 		  if ((vers_data & 0x8000) || vers_data > 1) */
/* 		    { */
/* 		      if (version_info[DT_VERSIONTAGIDX (DT_VERNEED)] */
/* 			  && (is_nobits || ! check_def)) */
/* 			{ */
/* 			  Elf_External_Verneed evn; */
/* 			  Elf_Internal_Verneed ivn; */
/* 			  Elf_Internal_Vernaux ivna; */

 			  /* We must test both.  */
/* 			  offset = (version_info[DT_VERSIONTAGIDX (DT_VERNEED)] */
/* 				    - loadaddr); */

/* 			  do */
/* 			    { */
/* 			      unsigned long vna_off; */

/* 			      get_data (&evn, file, offset, sizeof (evn), */
/* 					_("version need")); */

/* 			      ivn.vn_aux  = BYTE_GET (evn.vn_aux); */
/* 			      ivn.vn_next = BYTE_GET (evn.vn_next); */

/* 			      vna_off = offset + ivn.vn_aux; */

/* 			      do */
/* 				{ */
/* 				  Elf_External_Vernaux evna; */

/* 				  get_data (&evna, file, vna_off, */
/* 					    sizeof (evna), */
/* 					    _("version need aux (3)")); */

/* 				  ivna.vna_other = BYTE_GET (evna.vna_other); */
/* 				  ivna.vna_next  = BYTE_GET (evna.vna_next); */
/* 				  ivna.vna_name  = BYTE_GET (evna.vna_name); */

/* 				  vna_off += ivna.vna_next; */
/* 				} */
/* 			      while (ivna.vna_other != vers_data */
/* 				     && ivna.vna_next != 0); */

/* 			      if (ivna.vna_other == vers_data) */
/* 				break; */

/* 			      offset += ivn.vn_next; */
/* 			    } */
/* 			  while (ivn.vn_next != 0); */

/* 			  if (ivna.vna_other == vers_data) */
/* 			    { */
/*                               //printf ("@%s (%d)", */
/*                               //strtab + ivna.vna_name, ivna.vna_other); */
/* 			      check_def = 0; */
/* 			    } */
/* 			  else if (! is_nobits) */
/* 			    error (_("bad dynamic symbol")); */
/* 			  else */
/* 			    check_def = 1; */
/* 			} */

/* 		      if (check_def) */
/* 			{ */
/* 			  if (vers_data != 0x8001 */
/* 			      && version_info[DT_VERSIONTAGIDX (DT_VERDEF)]) */
/* 			    { */
/* 			      Elf_Internal_Verdef ivd; */
/* 			      Elf_Internal_Verdaux ivda; */
/* 			      Elf_External_Verdaux evda; */
/* 			      unsigned long off; */

/* 			      off */
/* 				= (version_info[DT_VERSIONTAGIDX (DT_VERDEF)] */
/* 				   - loadaddr); */

/* 			      do */
/* 				{ */
/* 				  Elf_External_Verdef evd; */

/* 				  get_data (&evd, file, off, sizeof (evd), */
/* 					    _("version def")); */

/* 				  ivd.vd_ndx = BYTE_GET (evd.vd_ndx); */
/* 				  ivd.vd_aux = BYTE_GET (evd.vd_aux); */
/* 				  ivd.vd_next = BYTE_GET (evd.vd_next); */

/* 				  off += ivd.vd_next; */
/* 				} */
/* 			      while (ivd.vd_ndx != (vers_data & 0x7fff) */
/* 				     && ivd.vd_next != 0); */

/* 			      off -= ivd.vd_next; */
/* 			      off += ivd.vd_aux; */

/* 			      get_data (&evda, file, off, sizeof (evda), */
/* 					_("version def aux")); */

/* 			      ivda.vda_name = BYTE_GET (evda.vda_name); */

/* 			      if (psym->st_name != ivda.vda_name) */
/* 			 FJALAR_DPRINTF ((vers_data & 0x8000) */
/* 					? "@%s" : "@@%s", */
/* 					strtab + ivda.vda_name); */
/* 			    } */
/* 			} */
/* 		    } */
/* 		} */

//	      putchar ('\n');
	    }

	  VG_(free) (symtab);
	  if (strtab != string_table)
	    VG_(free) (strtab);
	}
    }
  else if (do_syms)
    FJALAR_DPRINTF
      (_("\nDynamic symbol information is not available for displaying symbols.\n"));

  if (do_histogram && buckets != NULL)
    {
      int *lengths;
      int *counts;
      int hn;
      int si;
      int maxlength = 0;
      int nzero_counts = 0;
      int nsyms = 0;

      FJALAR_DPRINTF (_("\nHistogram for bucket list length (total of %d buckets):\n"),
	      nbuckets);
      FJALAR_DPRINTF (_(" Length  Number     %% of total  Coverage\n"));

      lengths = (int *) VG_(calloc) ("readelf.c: process_symbol_table.1",nbuckets, sizeof (int));
      if (lengths == NULL)
	{
	  error (_("Out of memory"));
	  return 0;
	}
      for (hn = 0; hn < nbuckets; ++hn)
	{
	  if (! buckets[hn])
	    continue;

	  for (si = buckets[hn]; si > 0 && si < nchains; si = chains[si])
	    {
	      ++nsyms;
	      if (maxlength < ++lengths[hn])
		++maxlength;
	    }
	}

      counts = (int *) VG_(calloc) ("readelf.c: process_symbol_table.2",maxlength + 1, sizeof (int));
      if (counts == NULL)
	{
	  error (_("Out of memory"));
	  return 0;
	}

      for (hn = 0; hn < nbuckets; ++hn)
	++counts[lengths[hn]];

      if (nbuckets > 0)
	{
	  FJALAR_DPRINTF ("      0  %-10d (%5.1f%%)\n",
		  counts[0], (counts[0] * 100.0) / nbuckets);
	  for (si = 1; si <= maxlength; ++si)
	    {
	      nzero_counts += counts[si] * si;
	      FJALAR_DPRINTF ("%7d  %-10d (%5.1f%%)    %5.1f%%\n",
		      si, counts[si], (counts[si] * 100.0) / nbuckets,
		      (nzero_counts * 100.0) / nsyms);
	    }
	}

      VG_(free) (counts);
      VG_(free) (lengths);
    }

  if (buckets != NULL)
    {
      VG_(free) (buckets);
      VG_(free) (chains);
    }

  return 1;
}

static int
process_syminfo (file)
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned int i;

  if (dynamic_syminfo == NULL
      || !do_dynamic)
    /* No syminfo, this is ok.  */
    return 1;

  /* There better should be a dynamic symbol section.  */
  if (dynamic_symbols == NULL || dynamic_strings == NULL)
    return 0;

  if (dynamic_addr)
    FJALAR_DPRINTF (_("\nDynamic info segment at offset 0x%lx contains %d entries:\n"),
	    dynamic_syminfo_offset, dynamic_syminfo_nent);

  FJALAR_DPRINTF (_(" Num: Name                           BoundTo     Flags\n"));
  for (i = 0; i < dynamic_syminfo_nent; ++i)
    {
      unsigned short int flags = dynamic_syminfo[i].si_flags;

      FJALAR_DPRINTF ("%4d: ", i);
      print_symbol (30, dynamic_strings + dynamic_symbols[i].st_name);
      putchar (' ');

      switch (dynamic_syminfo[i].si_boundto)
	{
	case SYMINFO_BT_SELF:
	  fputs ("SELF       ", stdout);
	  break;
	case SYMINFO_BT_PARENT:
	  fputs ("PARENT     ", stdout);
	  break;
	default:
	  if (dynamic_syminfo[i].si_boundto > 0
	      && dynamic_syminfo[i].si_boundto < dynamic_size)
	    {
	      print_symbol (10,
			    dynamic_strings
			    + (dynamic_segment
			       [dynamic_syminfo[i].si_boundto].d_un.d_val));
	      putchar (' ' );
	    }
	  else
	    FJALAR_DPRINTF ("%-10d ", dynamic_syminfo[i].si_boundto);
	  break;
	}

      if (flags & SYMINFO_FLG_DIRECT)
 FJALAR_DPRINTF (" DIRECT");
      if (flags & SYMINFO_FLG_PASSTHRU)
 FJALAR_DPRINTF (" PASSTHRU");
      if (flags & SYMINFO_FLG_COPY)
 FJALAR_DPRINTF (" COPY");
      if (flags & SYMINFO_FLG_LAZYLOAD)
 FJALAR_DPRINTF (" LAZYLOAD");

      puts ("");
    }

  return 1;
}

#ifdef SUPPORT_DISASSEMBLY
static void
disassemble_section (section, file)
     Elf_Internal_Shdr *section;
     FILE *file;
{
  FJALAR_DPRINTF (_("\nAssembly dump of section %s\n"),
	  SECTION_NAME (section));

  /* XXX -- to be done --- XXX */

  return 1;
}
#endif

static int
dump_section (section, file)
     Elf_Internal_Shdr *section;
     FILE *file;
{
  bfd_size_type bytes;
  bfd_vma addr;
  unsigned char *data;
  unsigned char *start;

  bytes = section->sh_size;

  if (bytes == 0)
    {
      FJALAR_DPRINTF (_("\nSection '%s' has no data to dump.\n"),
	      SECTION_NAME (section));
      return 0;
    }
  else
    FJALAR_DPRINTF (_("\nHex dump of section '%s':\n"), SECTION_NAME (section));

  addr = section->sh_addr;

  start = (unsigned char *) get_data (NULL, file, section->sh_offset, bytes,
				      _("section data"));
  if (!start)
    return 0;

  data = start;

  while (bytes)
    {
      int j;
      int k;
      int lbytes;

      lbytes = (bytes > 16 ? 16 : bytes);

      FJALAR_DPRINTF ("  0x%8.8lx ", (unsigned long) addr);

      switch (elf_header.e_ident[EI_DATA])
	{
	default:
	case ELFDATA2LSB:
	  for (j = 15; j >= 0; j --)
	    {
	      if (j < lbytes)
	 FJALAR_DPRINTF ("%2.2x", data[j]);
	      else
	 FJALAR_DPRINTF ("  ");

	      if (!(j & 0x3))
	 FJALAR_DPRINTF (" ");
	    }
	  break;

	case ELFDATA2MSB:
	  for (j = 0; j < 16; j++)
	    {
	      if (j < lbytes)
	 FJALAR_DPRINTF ("%2.2x", data[j]);
	      else
	 FJALAR_DPRINTF ("  ");

	      if ((j & 3) == 3)
	 FJALAR_DPRINTF (" ");
	    }
	  break;
	}

      for (j = 0; j < lbytes; j++)
	{
	  k = data[j];
	  if (k >= ' ' && k < 0x80)
	    FJALAR_DPRINTF ("%c", k);
	  else
	    FJALAR_DPRINTF (".");
	}

      putchar ('\n');

      data  += lbytes;
      addr  += lbytes;
      bytes -= lbytes;
    }

  VG_(free) (start);

  return 1;
}


static unsigned long int
read_leb128 (data, length_return, sign)
     unsigned char *data;
     int *length_return;
     int sign;
{
  unsigned long int result = 0;
  unsigned int num_read = 0;
  int shift = 0;
  unsigned char byte;

  do
    {
      byte = *data++;
      num_read++;

      result |= (byte & 0x7f) << shift;

      shift += 7;

    }
  while (byte & 0x80);

  if (length_return != NULL)
    *length_return = num_read;

  if (sign && (shift < 32) && (byte & 0x40))
    result |= -1 << shift;

  return result;
}

typedef struct State_Machine_Registers
{
  unsigned long address;
  unsigned long last_address; /* Added for Kvasir */
  unsigned int file;
  unsigned int line;
  unsigned int column;
  int is_stmt;
  int basic_block;
  int end_sequence;
/* This variable hold the number of the last entry seen
   in the File Table.  */
  unsigned int last_file_entry;
} SMR;

static SMR state_machine_regs;

static void
reset_state_machine (is_stmt)
     int is_stmt;
{
  state_machine_regs.address = 0;
  state_machine_regs.file = 1;
  state_machine_regs.line = 1;
  state_machine_regs.column = 0;
  state_machine_regs.is_stmt = is_stmt;
  state_machine_regs.basic_block = 0;
  state_machine_regs.end_sequence = 0;
  state_machine_regs.last_file_entry = 0;
}

/* Handled an extend line op.  Returns true if this is the end
   of sequence.  */
static int
process_extended_line_op (data, is_stmt, pointer_size)
     unsigned char *data;
     int is_stmt;
     int pointer_size;
{
  unsigned char op_code;
  int bytes_read;
  unsigned int len;
  unsigned char *name;
  unsigned long adr;

  len = read_leb128 (data, & bytes_read, 0);
  data += bytes_read;

  if (len == 0)
    {
      warn (_("badly formed extended line op encountered!\n"));
      return bytes_read;
    }

  len += bytes_read;
  op_code = *data++;

  switch (op_code)
    {
    case DW_LNE_end_sequence:
      reset_state_machine (is_stmt);
      break;

    case DW_LNE_set_address:
      adr = byte_get (data, pointer_size);
      state_machine_regs.address = state_machine_regs.last_address = adr;
      break;

    case DW_LNE_define_file:
      ++state_machine_regs.last_file_entry;
      name = data;
      data += VG_(strlen) ((char *) data) + 1;
      read_leb128(data, & bytes_read, 0);
      data += bytes_read;
      read_leb128(data, & bytes_read, 0);
      data += bytes_read;
      read_leb128(data, & bytes_read, 0);
      break;

    default:
      FJALAR_DPRINTF (_("UNKNOWN: length %d\n"), len - bytes_read);
      break;
    }

  return len;
}

/* Size of pointers in the .debug_line section.  This information is not
   really present in that section.  It's obtained before dumping the debug
   sections by doing some pre-scan of the .debug_info section.  */
static int debug_line_pointer_size = 4;

static int
display_debug_lines (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char * start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned char *hdrptr;
  DWARF2_Internal_LineInfo info;
  unsigned char *standard_opcodes;
  unsigned char *data = start;
  unsigned char *end = start + section->sh_size;
  unsigned char *end_of_sequence;
  int offset_size;
  int initial_length_size;
  int dir_table_index;
  unsigned int cur_line_offset = 0;
  XArray* dir_table  = NULL;
  XArray* file_table = NULL;
  

  while (data < end)
    {
      cur_line_offset = data - start;
      
      dir_table = VG_(newXA) (VG_(malloc), "display_debug_lines.0", VG_(free), sizeof(char *));
      dir_table_index = 0;
      file_table = VG_(newXA) (VG_(malloc), "display_debug_lines.1", VG_(free), sizeof(char *));

      hdrptr = data;

      /* Check the length of the block.  */
      info.li_length = byte_get (hdrptr, 4);
      hdrptr += 4;

      if (info.li_length == 0xffffffff)
	{
	  /* This section is 64-bit DWARF 3.  */
	  info.li_length = byte_get (hdrptr, 8);
	  hdrptr += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      if (info.li_length + initial_length_size > section->sh_size)
	{
	  warn
	    (_("The line info appears to be corrupt - the section is too small\n"));
	  return 0;
	}

      /* Check its version number.  */
      info.li_version = byte_get (hdrptr, 2);
      hdrptr += 2;
      if (info.li_version != 2 && info.li_version != 3)
	{
	  warn (_("Only DWARF version 2 and 3 line info is currently supported.\n"));
	  return 0;
	}

      info.li_prologue_length = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;
      info.li_min_insn_length = byte_get (hdrptr, 1);
      hdrptr++;
      info.li_default_is_stmt = byte_get (hdrptr, 1);
      hdrptr++;
      info.li_line_base = byte_get (hdrptr, 1);
      hdrptr++;
      info.li_line_range = byte_get (hdrptr, 1);
      hdrptr++;
      info.li_opcode_base = byte_get (hdrptr, 1);
      hdrptr++;

      /* Sign extend the line base field.  */
      info.li_line_base <<= 24;
      info.li_line_base >>= 24;

      end_of_sequence = data + info.li_length + initial_length_size;

      reset_state_machine (info.li_default_is_stmt);

      /* Display the contents of the Opcodes table.  */
      standard_opcodes = hdrptr;

      /* Display the contents of the Directory table.  */
      data = standard_opcodes + info.li_opcode_base - 1;
      
      if (*data != 0)
	{
	  while (*data != 0)
	    {
              VG_(addToXA)(dir_table, &data);
	      data += VG_(strlen) ((char *) data) + 1;
              dir_table_index++;
	    }
	}

      /* Skip the NUL at the end of the table.  */
      data++;

      /* Display the contents of the File Name table.  */
      if (*data != 0)
	{
	  while (*data != 0)
	    {
	      int bytes_read;
              unsigned long dir_index = 0;
              char* full_name = NULL;
	      char* file_name = NULL;
              char* dir_name  = NULL;
              unsigned int dir_name_len = 0;
              unsigned int full_name_len = 0;              
              
	      ++state_machine_regs.last_file_entry;
	      file_name = data;
	      data += VG_(strlen) ((char *) data) + 1;

	      dir_index = read_leb128(data, &bytes_read, 0);
	      data += bytes_read;

              // dir_index == 0 implies
              // base directory
              if(dir_index > 0) {
                dir_name = *(char **)VG_(indexXA)(dir_table, dir_index - 1);
                dir_name_len = VG_(strlen)(dir_name);
              }

              full_name_len =  VG_(strlen)(file_name) + dir_name_len + 1 + 1;
              full_name = VG_(calloc)("debug_display_lines.2", 1, full_name_len);
              VG_(strncpy)(full_name, "", full_name_len);

              if(dir_name) {
                VG_(strcat)(full_name, dir_name);
                VG_(strcat)(full_name, "/");
              }

              VG_(strcat)(full_name, file_name);
              
              //              VG_(printf)("Full_name: %s\n", full_name);
              VG_(addToXA)(file_table, &full_name);
              
              // Don't care about modification date
              // and time
	      read_leb128(data, & bytes_read, 0);
	      data += bytes_read;
	      read_leb128(data, & bytes_read, 0);
	      data += bytes_read;
	    }
	}

      harvest_file_name_table(cur_line_offset, file_table);

      /* Skip the NUL at the end of the table.  */
      data++;

      while (data < end_of_sequence)
	{
	  unsigned char op_code;
	  int adv;
	  int bytes_read;

	  op_code = *data++;

	  if (op_code >= info.li_opcode_base)
	    {
	      op_code -= info.li_opcode_base;
	      adv      = (op_code / info.li_line_range) * info.li_min_insn_length;
	      state_machine_regs.address += adv;
	      genputtable(next_line_addr,
			  (void *)(int)state_machine_regs.last_address,
			  (void *)(int)state_machine_regs.address);
	      state_machine_regs.last_address = state_machine_regs.address;
	      adv = (op_code % info.li_line_range) + info.li_line_base;
	      state_machine_regs.line += adv;
	    }
	  else switch (op_code)
	    {
	    case DW_LNS_extended_op:
	      data += process_extended_line_op (data, info.li_default_is_stmt,
						debug_line_pointer_size);
	      break;

	    case DW_LNS_copy:
	      break;

	    case DW_LNS_advance_pc:
	      adv = info.li_min_insn_length * read_leb128 (data, & bytes_read, 0);
	      data += bytes_read;
	      state_machine_regs.address += adv;
	      genputtable(next_line_addr,
			  (void *)(int)state_machine_regs.last_address,
			  (void *)(int)state_machine_regs.address);
	      state_machine_regs.last_address = state_machine_regs.address;
	      break;

	    case DW_LNS_advance_line:
	      adv = read_leb128 (data, & bytes_read, 1);
	      data += bytes_read;
	      state_machine_regs.line += adv;
	      break;

	    case DW_LNS_set_file:
	      adv = read_leb128 (data, & bytes_read, 0);
	      data += bytes_read;
	      state_machine_regs.file = adv;
	      break;

	    case DW_LNS_set_column:
	      adv = read_leb128 (data, & bytes_read, 0);
	      data += bytes_read;
	      state_machine_regs.column = adv;
	      break;

	    case DW_LNS_negate_stmt:
	      adv = state_machine_regs.is_stmt;
	      adv = ! adv;
	      state_machine_regs.is_stmt = adv;
	      break;

	    case DW_LNS_set_basic_block:
	      state_machine_regs.basic_block = 1;
	      break;

	    case DW_LNS_const_add_pc:
	      adv = (((255 - info.li_opcode_base) / info.li_line_range)
		     * info.li_min_insn_length);
	      state_machine_regs.address += adv;
	      break;

	    case DW_LNS_fixed_advance_pc:
	      adv = byte_get (data, 2);
	      data += 2;
	      state_machine_regs.address += adv;
	      genputtable(next_line_addr,
			  (void *)(int)state_machine_regs.last_address,
			  (void *)(int)state_machine_regs.address);
	      state_machine_regs.last_address = state_machine_regs.address;
	      break;

	    case DW_LNS_set_prologue_end:
	      break;

	    case DW_LNS_set_epilogue_begin:
	      break;

	    case DW_LNS_set_isa:
	      adv = read_leb128 (data, & bytes_read, 0);
	      data += bytes_read;
	      break;

	    default:
	      {
		int j;
		for (j = standard_opcodes[op_code - 1]; j > 0 ; --j)
		  {
		    read_leb128 (data, &bytes_read, 0);
		    data += bytes_read;
		  }
	      }
	      break;
	    }
	}

      // We're not leaking the previous iteration's file_table. It's being passed to typedata.c
      // who will be in charge of it's deletion.
      VG_(deleteXA)(dir_table);
    }
  
  return 1;
}

static int
display_debug_pubnames (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  DWARF2_Internal_PubNames pubnames;
  unsigned char *end;

  end = start + section->sh_size;

  FJALAR_DPRINTF (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

  while (start < end)
    {
      unsigned char *data;
      unsigned long offset;
      int offset_size, initial_length_size;

      data = start;

      pubnames.pn_length = byte_get (data, 4);
      data += 4;
      if (pubnames.pn_length == 0xffffffff)
	{
	  pubnames.pn_length = byte_get (data, 8);
	  data += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      pubnames.pn_version = byte_get (data, 2);
      data += 2;
      pubnames.pn_offset = byte_get (data, offset_size);
      data += offset_size;
      pubnames.pn_size = byte_get (data, offset_size);
      data += offset_size;

      start += pubnames.pn_length + initial_length_size;

      if (pubnames.pn_version != 2 && pubnames.pn_version != 3)
	{
	  static int warned = 0;

	  if (! warned)
	    {
	      warn (_("Only DWARF 2 and 3 pubnames are currently supported\n"));
	      warned = 1;
	    }

	  continue;
	}

      FJALAR_DPRINTF (_("  Length:                              %ld\n"),
	      pubnames.pn_length);
      FJALAR_DPRINTF (_("  Version:                             %d\n"),
	      pubnames.pn_version);
      FJALAR_DPRINTF (_("  Offset into .debug_info section:     %ld\n"),
	      pubnames.pn_offset);
      FJALAR_DPRINTF (_("  Size of area in .debug_info section: %ld\n"),
	      pubnames.pn_size);

      FJALAR_DPRINTF (_("\n    Offset\tName\n"));

      do
	{
	  offset = byte_get (data, offset_size);

	  if (offset != 0)
	    {
	      data += offset_size;
	      FJALAR_DPRINTF ("    %ld\t\t%s\n", offset, data);
	      data += VG_(strlen) ((char *) data) + 1;
	    }
	}
      while (offset != 0);
    }

  FJALAR_DPRINTF ("\n");
  return 1;
}

// PG don't make this static!
char *
get_TAG_name (tag)
     unsigned long tag;
{
  switch (tag)
    {
    case DW_TAG_padding:		return "DW_TAG_padding";
    case DW_TAG_array_type:		return "DW_TAG_array_type";
    case DW_TAG_class_type:		return "DW_TAG_class_type";
    case DW_TAG_entry_point:		return "DW_TAG_entry_point";
    case DW_TAG_enumeration_type:	return "DW_TAG_enumeration_type";
    case DW_TAG_formal_parameter:	return "DW_TAG_formal_parameter";
    case DW_TAG_imported_declaration:	return "DW_TAG_imported_declaration";
    case DW_TAG_label:			return "DW_TAG_label";
    case DW_TAG_lexical_block:		return "DW_TAG_lexical_block";
    case DW_TAG_member:			return "DW_TAG_member";
    case DW_TAG_pointer_type:		return "DW_TAG_pointer_type";
    case DW_TAG_reference_type:		return "DW_TAG_reference_type";
    case DW_TAG_compile_unit:		return "DW_TAG_compile_unit";
    case DW_TAG_string_type:		return "DW_TAG_string_type";
    case DW_TAG_structure_type:		return "DW_TAG_structure_type";
    case DW_TAG_subroutine_type:	return "DW_TAG_subroutine_type";
    case DW_TAG_typedef:		return "DW_TAG_typedef";
    case DW_TAG_union_type:		return "DW_TAG_union_type";
    case DW_TAG_unspecified_parameters: return "DW_TAG_unspecified_parameters";
    case DW_TAG_variant:		return "DW_TAG_variant";
    case DW_TAG_common_block:		return "DW_TAG_common_block";
    case DW_TAG_common_inclusion:	return "DW_TAG_common_inclusion";
    case DW_TAG_inheritance:		return "DW_TAG_inheritance";
    case DW_TAG_inlined_subroutine:	return "DW_TAG_inlined_subroutine";
    case DW_TAG_module:			return "DW_TAG_module";
    case DW_TAG_ptr_to_member_type:	return "DW_TAG_ptr_to_member_type";
    case DW_TAG_set_type:		return "DW_TAG_set_type";
    case DW_TAG_subrange_type:		return "DW_TAG_subrange_type";
    case DW_TAG_with_stmt:		return "DW_TAG_with_stmt";
    case DW_TAG_access_declaration:	return "DW_TAG_access_declaration";
    case DW_TAG_base_type:		return "DW_TAG_base_type";
    case DW_TAG_catch_block:		return "DW_TAG_catch_block";
    case DW_TAG_const_type:		return "DW_TAG_const_type";
    case DW_TAG_constant:		return "DW_TAG_constant";
    case DW_TAG_enumerator:		return "DW_TAG_enumerator";
    case DW_TAG_file_type:		return "DW_TAG_file_type";
    case DW_TAG_friend:			return "DW_TAG_friend";
    case DW_TAG_namelist:		return "DW_TAG_namelist";
    case DW_TAG_namelist_item:		return "DW_TAG_namelist_item";
    case DW_TAG_packed_type:		return "DW_TAG_packed_type";
    case DW_TAG_subprogram:		return "DW_TAG_subprogram";
    case DW_TAG_template_type_param:	return "DW_TAG_template_type_param";
    case DW_TAG_template_value_param:	return "DW_TAG_template_value_param";
    case DW_TAG_thrown_type:		return "DW_TAG_thrown_type";
    case DW_TAG_try_block:		return "DW_TAG_try_block";
    case DW_TAG_variant_part:		return "DW_TAG_variant_part";
    case DW_TAG_variable:		return "DW_TAG_variable";
    case DW_TAG_volatile_type:		return "DW_TAG_volatile_type";
    case DW_TAG_MIPS_loop:		return "DW_TAG_MIPS_loop";
    case DW_TAG_format_label:		return "DW_TAG_format_label";
    case DW_TAG_function_template:	return "DW_TAG_function_template";
    case DW_TAG_class_template:		return "DW_TAG_class_template";
      /* DWARF 2.1 values.  */
    case DW_TAG_dwarf_procedure:	return "DW_TAG_dwarf_procedure";
    case DW_TAG_restrict_type:		return "DW_TAG_restrict_type";
    case DW_TAG_interface_type:		return "DW_TAG_interface_type";
    case DW_TAG_namespace:		return "DW_TAG_namespace";
    case DW_TAG_imported_module:	return "DW_TAG_imported_module";
    case DW_TAG_unspecified_type:	return "DW_TAG_unspecified_type";
    case DW_TAG_partial_unit:		return "DW_TAG_partial_unit";
    case DW_TAG_imported_unit:		return "DW_TAG_imported_unit";
      /* UPC values.  */
    case DW_TAG_upc_shared_type:        return "DW_TAG_upc_shared_type";
    case DW_TAG_upc_strict_type:        return "DW_TAG_upc_strict_type";
    case DW_TAG_upc_relaxed_type:       return "DW_TAG_upc_relaxed_type";
    default:
      {
	static char buffer[100];

	sprintf (buffer, _("Unknown TAG value: %lx"), tag);
	return buffer;
      }
    }
}

static char *
get_AT_name (attribute)
     unsigned long attribute;
{
  switch (attribute)
    {
    case DW_AT_sibling:			return "DW_AT_sibling";
    case DW_AT_location:		return "DW_AT_location";
    case DW_AT_name:			return "DW_AT_name";
    case DW_AT_ordering:		return "DW_AT_ordering";
    case DW_AT_subscr_data:		return "DW_AT_subscr_data";
    case DW_AT_byte_size:		return "DW_AT_byte_size";
    case DW_AT_bit_offset:		return "DW_AT_bit_offset";
    case DW_AT_bit_size:		return "DW_AT_bit_size";
    case DW_AT_element_list:		return "DW_AT_element_list";
    case DW_AT_stmt_list:		return "DW_AT_stmt_list";
    case DW_AT_low_pc:			return "DW_AT_low_pc";
    case DW_AT_high_pc:			return "DW_AT_high_pc";
    case DW_AT_language:		return "DW_AT_language";
    case DW_AT_member:			return "DW_AT_member";
    case DW_AT_discr:			return "DW_AT_discr";
    case DW_AT_discr_value:		return "DW_AT_discr_value";
    case DW_AT_visibility:		return "DW_AT_visibility";
    case DW_AT_import:			return "DW_AT_import";
    case DW_AT_string_length:		return "DW_AT_string_length";
    case DW_AT_common_reference:	return "DW_AT_common_reference";
    case DW_AT_comp_dir:		return "DW_AT_comp_dir";
    case DW_AT_const_value:		return "DW_AT_const_value";
    case DW_AT_containing_type:		return "DW_AT_containing_type";
    case DW_AT_default_value:		return "DW_AT_default_value";
    case DW_AT_inline:			return "DW_AT_inline";
    case DW_AT_is_optional:		return "DW_AT_is_optional";
    case DW_AT_lower_bound:		return "DW_AT_lower_bound";
    case DW_AT_producer:		return "DW_AT_producer";
    case DW_AT_prototyped:		return "DW_AT_prototyped";
    case DW_AT_return_addr:		return "DW_AT_return_addr";
    case DW_AT_start_scope:		return "DW_AT_start_scope";
    case DW_AT_stride_size:		return "DW_AT_stride_size";
    case DW_AT_upper_bound:		return "DW_AT_upper_bound";
    case DW_AT_abstract_origin:		return "DW_AT_abstract_origin";
    case DW_AT_accessibility:		return "DW_AT_accessibility";
    case DW_AT_address_class:		return "DW_AT_address_class";
    case DW_AT_artificial:		return "DW_AT_artificial";
    case DW_AT_base_types:		return "DW_AT_base_types";
    case DW_AT_calling_convention:	return "DW_AT_calling_convention";
    case DW_AT_count:			return "DW_AT_count";
    case DW_AT_data_member_location:	return "DW_AT_data_member_location";
    case DW_AT_decl_column:		return "DW_AT_decl_column";
    case DW_AT_decl_file:		return "DW_AT_decl_file";
    case DW_AT_decl_line:		return "DW_AT_decl_line";
    case DW_AT_declaration:		return "DW_AT_declaration";
    case DW_AT_discr_list:		return "DW_AT_discr_list";
    case DW_AT_encoding:		return "DW_AT_encoding";
    case DW_AT_external:		return "DW_AT_external";
    case DW_AT_frame_base:		return "DW_AT_frame_base";
    case DW_AT_friend:			return "DW_AT_friend";
    case DW_AT_identifier_case:		return "DW_AT_identifier_case";
    case DW_AT_macro_info:		return "DW_AT_macro_info";
    case DW_AT_namelist_items:		return "DW_AT_namelist_items";
    case DW_AT_priority:		return "DW_AT_priority";
    case DW_AT_segment:			return "DW_AT_segment";
    case DW_AT_specification:		return "DW_AT_specification";
    case DW_AT_static_link:		return "DW_AT_static_link";
    case DW_AT_type:			return "DW_AT_type";
    case DW_AT_use_location:		return "DW_AT_use_location";
    case DW_AT_variable_parameter:	return "DW_AT_variable_parameter";
    case DW_AT_virtuality:		return "DW_AT_virtuality";
    case DW_AT_vtable_elem_location:	return "DW_AT_vtable_elem_location";
      /* DWARF 2.1 values.  */
    case DW_AT_allocated:		return "DW_AT_allocated";
    case DW_AT_associated:		return "DW_AT_associated";
    case DW_AT_data_location:		return "DW_AT_data_location";
    case DW_AT_stride:			return "DW_AT_stride";
    case DW_AT_entry_pc:		return "DW_AT_entry_pc";
    case DW_AT_use_UTF8:		return "DW_AT_use_UTF8";
    case DW_AT_extension:		return "DW_AT_extension";
    case DW_AT_ranges:			return "DW_AT_ranges";
    case DW_AT_trampoline:		return "DW_AT_trampoline";
    case DW_AT_call_column:		return "DW_AT_call_column";
    case DW_AT_call_file:		return "DW_AT_call_file";
    case DW_AT_call_line:		return "DW_AT_call_line";
      /* SGI/MIPS extensions.  */
    case DW_AT_MIPS_fde:		return "DW_AT_MIPS_fde";
    case DW_AT_MIPS_loop_begin:		return "DW_AT_MIPS_loop_begin";
    case DW_AT_MIPS_tail_loop_begin:	return "DW_AT_MIPS_tail_loop_begin";
    case DW_AT_MIPS_epilog_begin:	return "DW_AT_MIPS_epilog_begin";
    case DW_AT_MIPS_loop_unroll_factor: return "DW_AT_MIPS_loop_unroll_factor";
    case DW_AT_MIPS_software_pipeline_depth:
      return "DW_AT_MIPS_software_pipeline_depth";
    case DW_AT_MIPS_linkage_name:	return "DW_AT_MIPS_linkage_name";
    case DW_AT_MIPS_stride:		return "DW_AT_MIPS_stride";
    case DW_AT_MIPS_abstract_name:	return "DW_AT_MIPS_abstract_name";
    case DW_AT_MIPS_clone_origin:	return "DW_AT_MIPS_clone_origin";
    case DW_AT_MIPS_has_inlines:	return "DW_AT_MIPS_has_inlines";
      /* GNU extensions.  */
    case DW_AT_sf_names:		return "DW_AT_sf_names";
    case DW_AT_src_info:		return "DW_AT_src_info";
    case DW_AT_mac_info:		return "DW_AT_mac_info";
    case DW_AT_src_coords:		return "DW_AT_src_coords";
    case DW_AT_body_begin:		return "DW_AT_body_begin";
    case DW_AT_body_end:		return "DW_AT_body_end";
    case DW_AT_GNU_vector:		return "DW_AT_GNU_vector";
      /* UPC extension.  */
    case DW_AT_upc_threads_scaled:	return "DW_AT_upc_threads_scaled";
    default:
      {
	static char buffer[100];

	sprintf (buffer, _("Unknown AT value: %lx"), attribute);
	return buffer;
      }
    }
}

static char *
get_FORM_name (form)
     unsigned long form;
{
  switch (form)
    {
    case DW_FORM_addr:		return "DW_FORM_addr";
    case DW_FORM_block2:	return "DW_FORM_block2";
    case DW_FORM_block4:	return "DW_FORM_block4";
    case DW_FORM_data2:		return "DW_FORM_data2";
    case DW_FORM_data4:		return "DW_FORM_data4";
    case DW_FORM_data8:		return "DW_FORM_data8";
    case DW_FORM_string:	return "DW_FORM_string";
    case DW_FORM_block:		return "DW_FORM_block";
    case DW_FORM_block1:	return "DW_FORM_block1";
    case DW_FORM_data1:		return "DW_FORM_data1";
    case DW_FORM_flag:		return "DW_FORM_flag";
    case DW_FORM_sdata:		return "DW_FORM_sdata";
    case DW_FORM_strp:		return "DW_FORM_strp";
    case DW_FORM_udata:		return "DW_FORM_udata";
    case DW_FORM_ref_addr:	return "DW_FORM_ref_addr";
    case DW_FORM_ref1:		return "DW_FORM_ref1";
    case DW_FORM_ref2:		return "DW_FORM_ref2";
    case DW_FORM_ref4:		return "DW_FORM_ref4";
    case DW_FORM_ref8:		return "DW_FORM_ref8";
    case DW_FORM_ref_udata:	return "DW_FORM_ref_udata";
    case DW_FORM_indirect:	return "DW_FORM_indirect";
    default:
      {
	static char buffer[100];

	sprintf (buffer, _("Unknown FORM value: %lx"), form);
	return buffer;
      }
    }
}

/* FIXME:  There are better and more effiecint ways to handle
   these structures.  For now though, I just want something that
   is simple to implement.  */
typedef struct abbrev_attr
{
  unsigned long attribute;
  unsigned long form;
  struct abbrev_attr *next;
}
abbrev_attr;

typedef struct abbrev_entry
{
  unsigned long entry;
  unsigned long tag;
  int children;
  struct abbrev_attr *first_attr;
  struct abbrev_attr *last_attr;
  struct abbrev_entry *next;
}
abbrev_entry;

static abbrev_entry *first_abbrev = NULL;
static abbrev_entry *last_abbrev = NULL;

static void
free_abbrevs ()
{
  abbrev_entry *abbrev;

  for (abbrev = first_abbrev; abbrev;)
    {
      abbrev_entry *next = abbrev->next;
      abbrev_attr *attr;

      for (attr = abbrev->first_attr; attr;)
	{
	  abbrev_attr *next_attr = attr->next;

	  VG_(free) (attr);
	  attr = next_attr;
	}

      VG_(free) (abbrev);
      abbrev = next;
    }

  last_abbrev = first_abbrev = NULL;
}

static void
add_abbrev (number, tag, children)
     unsigned long number;
     unsigned long tag;
     int children;
{
  abbrev_entry *entry;

  entry = (abbrev_entry *) VG_(malloc) ("readelf.c: add_abbrev", sizeof (*entry));

  if (entry == NULL)
    /* ugg */
    return;

  entry->entry      = number;
  entry->tag        = tag;
  entry->children   = children;
  entry->first_attr = NULL;
  entry->last_attr  = NULL;
  entry->next       = NULL;

  if (first_abbrev == NULL)
    first_abbrev = entry;
  else
    last_abbrev->next = entry;

  last_abbrev = entry;
}

static void
add_abbrev_attr (attribute, form)
     unsigned long attribute;
     unsigned long form;
{
  abbrev_attr *attr;

  attr = (abbrev_attr *) VG_(malloc) ("readelf.c: add_abbrev_attr", sizeof (*attr));

  if (attr == NULL)
    /* ugg */
    return;

  attr->attribute = attribute;
  attr->form      = form;
  attr->next      = NULL;

  if (last_abbrev->first_attr == NULL)
    last_abbrev->first_attr = attr;
  else
    last_abbrev->last_attr->next = attr;

  last_abbrev->last_attr = attr;
}

/* Processes the (partial) contents of a .debug_abbrev section.
   Returns NULL if the end of the section was encountered.
   Returns the address after the last byte read if the end of
   an abbreviation set was found.  */

static unsigned char *
process_abbrev_section (start, end)
     unsigned char *start;
     unsigned char *end;
{
  if (first_abbrev != NULL)
    return NULL;

  while (start < end)
    {
      int bytes_read;
      unsigned long entry;
      unsigned long tag;
      unsigned long attribute;
      int children;

      entry = read_leb128 (start, & bytes_read, 0);
      start += bytes_read;

      /* A single zero is supposed to end the section according
	 to the standard.  If there's more, then signal that to
	 the caller.  */
      if (entry == 0)
	return start == end ? NULL : start;

      tag = read_leb128 (start, & bytes_read, 0);
      start += bytes_read;

      children = *start++;

      add_abbrev (entry, tag, children);

      do
	{
	  unsigned long form;

	  attribute = read_leb128 (start, & bytes_read, 0);
	  start += bytes_read;

	  form = read_leb128 (start, & bytes_read, 0);
	  start += bytes_read;

	  if (attribute != 0)
	    add_abbrev_attr (attribute, form);
	}
      while (attribute != 0);
    }

  return NULL;
}


static int
display_debug_macinfo (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned char *end = start + section->sh_size;
  unsigned char *curr = start;
  unsigned int bytes_read;
  enum dwarf_macinfo_record_type op;

  FJALAR_DPRINTF (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

  while (curr < end)
    {
      unsigned int lineno;
      const char *string;

      op = *curr;
      curr++;

      switch (op)
	{
	case DW_MACINFO_start_file:
	  {
	    unsigned int filenum;

	    lineno = read_leb128 (curr, & bytes_read, 0);
	    curr += bytes_read;
	    filenum = read_leb128 (curr, & bytes_read, 0);
	    curr += bytes_read;

	    FJALAR_DPRINTF (_(" DW_MACINFO_start_file - lineno: %d filenum: %d\n"), lineno, filenum);
	  }
	  break;

	case DW_MACINFO_end_file:
	  FJALAR_DPRINTF (_(" DW_MACINFO_end_file\n"));
	  break;

	case DW_MACINFO_define:
	  lineno = read_leb128 (curr, & bytes_read, 0);
	  curr += bytes_read;
	  string = curr;
	  curr += VG_(strlen) (string) + 1;
	  FJALAR_DPRINTF (_(" DW_MACINFO_define - lineno : %d macro : %s\n"), lineno, string);
	  break;

	case DW_MACINFO_undef:
	  lineno = read_leb128 (curr, & bytes_read, 0);
	  curr += bytes_read;
	  string = curr;
	  curr += VG_(strlen) (string) + 1;
	  FJALAR_DPRINTF (_(" DW_MACINFO_undef - lineno : %d macro : %s\n"), lineno, string);
	  break;

	case DW_MACINFO_vendor_ext:
	  {
	    unsigned int constant;

	    constant = read_leb128 (curr, & bytes_read, 0);
	    curr += bytes_read;
	    string = curr;
	    curr += VG_(strlen) (string) + 1;
	    FJALAR_DPRINTF (_(" DW_MACINFO_vendor_ext - constant : %d string : %s\n"), constant, string);
	  }
	  break;
	}
    }

  return 1;
}


static int
display_debug_abbrev (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  abbrev_entry *entry;
  unsigned char *end = start + section->sh_size;

  FJALAR_DPRINTF (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

  do
    {
      start = process_abbrev_section (start, end);

      if (first_abbrev == NULL)
	continue;

      FJALAR_DPRINTF (_("  Number TAG\n"));

      for (entry = first_abbrev; entry; entry = entry->next)
	{
	  abbrev_attr *attr;

	  FJALAR_DPRINTF (_("   %ld      %s    [%s]\n"),
		  entry->entry,
		  get_TAG_name (entry->tag),
		  entry->children ? _("has children") : _("no children"));

	  for (attr = entry->first_attr; attr; attr = attr->next)
	    {
	      FJALAR_DPRINTF (_("    %-18s %s\n"),
		      get_AT_name (attr->attribute),
		      get_FORM_name (attr->form));
	    }
	}

      free_abbrevs ();
    }
  while (start);

  FJALAR_DPRINTF ("\n");

  return 1;
}


static unsigned char *
display_block (data, length, ok_to_harvest)
     unsigned char *data;
     unsigned long length;
     char ok_to_harvest;
{
  if (print_results && ok_to_harvest)
    FJALAR_DPRINTF (_(" %lu byte block: "), length);

  while (length --)
    {
      unsigned long temp = (unsigned long) byte_get (data++, 1);
      if (print_results && ok_to_harvest)
        FJALAR_DPRINTF ("%lx ", temp);
      //    FJALAR_DPRINTF ("%lx ", (unsigned long) byte_get (data++, 1));
    }

  return data;
}

static  void
decode_location_expression (data, pointer_size, length, ok_to_harvest, entry, ll)
     unsigned char * data;
     unsigned int pointer_size;
     unsigned long length;
     char ok_to_harvest;
     dwarf_entry* entry;
     location_list* ll;
{
  unsigned op;
  int bytes_read;
  unsigned long uvalue;
  unsigned char *end = data + length;

  unsigned long addr;

  int print_results_and_ok = print_results && ok_to_harvest;



  while (data < end)
    {
      op = *data++;
      if(ll) {
        ll->atom = op;
      }
      switch (op)
	{
	  long const_data;
	case DW_OP_addr:
          addr = (unsigned long) byte_get (data, pointer_size);
          if (ok_to_harvest)
            {
              if (print_results_and_ok)
                {
                  FJALAR_DPRINTF ("DW_OP_addr: %lx", addr);
                }
              harvest_variable_addr_value(entry, addr);
            }
          data += pointer_size;
	  break;
	case DW_OP_deref:
	  if (print_results_and_ok) {FJALAR_DPRINTF ("DW_OP_deref");}
	  if (tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, 0);
	  }

	  break;
	case DW_OP_const1u:
	  if (print_results_and_ok) {FJALAR_DPRINTF ("DW_OP_const1u: %lu", (unsigned long) byte_get (data++, 1));}
          else {byte_get (data++, 1);}
	  break;
	case DW_OP_const1s:
	  if (print_results_and_ok) {FJALAR_DPRINTF ("DW_OP_const1s: %ld", (long) byte_get (data++, 1));}
          else {byte_get (data++, 1);}
	  break;
	case DW_OP_const2u:

	  const_data =  (long) byte_get (data, 2);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_const2u: %lu", (unsigned long) const_data);
              data += 2;
            }
          else
            {
              byte_get (data, 2);
              data += 2;
            }

	  if (tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, const_data);
	    harvest_formal_param_location_offset(entry, const_data);
	  }

	  break;
	case DW_OP_const2s:
	  const_data =  (long) byte_get (data, 2);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_const2s: %ld", (long) const_data);
              data += 2;
            }
          else
            {
              byte_get (data, 2);
              data += 2;
            }

	  if (entry && tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, const_data);
	    harvest_formal_param_location_offset(entry, const_data);
	  }

	  break;
	case DW_OP_const4u:
	  const_data =  byte_get (data, 4);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_const4u: %lu", (unsigned long)const_data);
              data += 4;
            }
          else
            {
              byte_get (data, 4);
              data += 4;
            }

	  if (entry && tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, const_data);
	    harvest_formal_param_location_offset(entry, const_data);
	  }

	  break;
	case DW_OP_const4s:
	  const_data = (long) byte_get (data, 4);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_const4s: %ld", const_data);
              data += 4;
            }
          else
            {
              byte_get (data, 4);
              data += 4;
            }

	  if (entry && tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, const_data);
	    harvest_formal_param_location_offset(entry, const_data);
	  }

	  break;
	case DW_OP_const8u:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_const8u: %lu %lu", (unsigned long) byte_get (data, 4),
                      (unsigned long) byte_get (data + 4, 4));
              data += 8;
            }
          else
            {
              byte_get (data, 4);
              byte_get (data + 4, 4);
              data += 8;
            }
	  break;
	case DW_OP_const8s:

          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_const8s: %ld %ld", (long) byte_get (data, 4),
                      (long) byte_get (data + 4, 4));
              data += 8;
            }
          else
            {
              byte_get (data, 4);
              byte_get (data + 4, 4);
              data += 8;
            }
	  break;
	case DW_OP_constu:

	  const_data = read_leb128 (data, &bytes_read, 0);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_constu: %lu", const_data);
              data += bytes_read;
            }
          else
            {
              read_leb128 (data, &bytes_read, 0);
              data += bytes_read;
            }

	  if (entry && tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, const_data);
	    harvest_formal_param_location_offset(entry, const_data);
	  }

	  break;
	case DW_OP_consts:

	  const_data = read_leb128 (data, &bytes_read, 1);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_consts: %ld", const_data);
              data += bytes_read;
            }
          else
            {
              read_leb128 (data, &bytes_read, 1);
              data += bytes_read;
            }

	  if (entry && tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, const_data);
	    harvest_formal_param_location_offset(entry, const_data);
	  }

	  break;
	case DW_OP_dup:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_dup");
	  break;
	case DW_OP_drop:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_drop");
	  break;
	case DW_OP_over:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_over");
	  break;
	case DW_OP_pick:
	  if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_pick: %ld", (unsigned long) byte_get (data++, 1));
            }
          else
            {
              byte_get (data++, 1);
            }
	  break;
	case DW_OP_swap:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_swap");
	  break;
	case DW_OP_rot:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_rot");
	  break;
	case DW_OP_xderef:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_xderef");
	  break;
	case DW_OP_abs:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_abs");
	  break;
	case DW_OP_and:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_and");
	  break;
	case DW_OP_div:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_div");
	  break;
	case DW_OP_minus:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_minus");
	  break;
	case DW_OP_mod:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_mod");
	  break;
	case DW_OP_mul:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_mul");
	  break;
	case DW_OP_neg:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_neg");
	  break;
	case DW_OP_not:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_not");
	  break;
	case DW_OP_or:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_or");
	  break;
	case DW_OP_plus:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_plus");
	  break;
	case DW_OP_plus_uconst:
	  if (ok_to_harvest)
            {
              unsigned long uconst_data = read_leb128 (data, &bytes_read, 0);

              if (print_results)
                {
                  FJALAR_DPRINTF ("DW_OP_plus_uconst: %lu",
                          uconst_data);
                }

	      if (entry && tag_is_formal_parameter(entry->tag_name)) {
		harvest_formal_param_location_atom(entry, op, (long)uconst_data);
		harvest_formal_param_location_offset(entry, (long)uconst_data);
	      }


              harvest_data_member_location(entry, uconst_data);

              data += bytes_read;
            }
          else
            {
              read_leb128 (data, &bytes_read, 0);
              data += bytes_read;
            }
	  break;
	case DW_OP_shl:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_shl");
	  break;
	case DW_OP_shr:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_shr");
	  break;
	case DW_OP_shra:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_shra");
	  break;
	case DW_OP_xor:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_xor");
	  break;
	case DW_OP_bra:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_bra: %ld", (long) byte_get (data, 2));
              data += 2;
            }
          else
            {
              byte_get (data, 2);
              data += 2;
            }
	  break;
	case DW_OP_eq:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_eq");
	  break;
	case DW_OP_ge:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_ge");
	  break;
	case DW_OP_gt:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_gt");
	  break;
	case DW_OP_le:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_le");
	  break;
	case DW_OP_lt:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_lt");
	  break;
	case DW_OP_ne:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_ne");
	  break;
	case DW_OP_skip:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_skip: %ld", (long) byte_get (data, 2));
              data += 2;
            }
          else
            {
              byte_get (data, 2);
              data += 2;
            }
	  break;

	case DW_OP_lit0:
	case DW_OP_lit1:
	case DW_OP_lit2:
	case DW_OP_lit3:
	case DW_OP_lit4:
	case DW_OP_lit5:
	case DW_OP_lit6:
	case DW_OP_lit7:
	case DW_OP_lit8:
	case DW_OP_lit9:
	case DW_OP_lit10:
	case DW_OP_lit11:
	case DW_OP_lit12:
	case DW_OP_lit13:
	case DW_OP_lit14:
	case DW_OP_lit15:
	case DW_OP_lit16:
	case DW_OP_lit17:
	case DW_OP_lit18:
	case DW_OP_lit19:
	case DW_OP_lit20:
	case DW_OP_lit21:
	case DW_OP_lit22:
	case DW_OP_lit23:
	case DW_OP_lit24:
	case DW_OP_lit25:
	case DW_OP_lit26:
	case DW_OP_lit27:
	case DW_OP_lit28:
	case DW_OP_lit29:
	case DW_OP_lit30:
	case DW_OP_lit31:
	  if (entry && (tag_is_formal_parameter(entry->tag_name))) {
	    harvest_formal_param_location_atom(entry, op, 0);
	  }
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_lit%d", op - DW_OP_lit0);
	  break;

	case DW_OP_reg0:
	case DW_OP_reg1:
	case DW_OP_reg2:
	case DW_OP_reg3:
	case DW_OP_reg4:
	case DW_OP_reg5:
	case DW_OP_reg6:
	case DW_OP_reg7:
	case DW_OP_reg8:
	case DW_OP_reg9:
	case DW_OP_reg10:
	case DW_OP_reg11:
	case DW_OP_reg12:
	case DW_OP_reg13:
	case DW_OP_reg14:
	case DW_OP_reg15:
	case DW_OP_reg16:
	case DW_OP_reg17:
	case DW_OP_reg18:
	case DW_OP_reg19:
	case DW_OP_reg20:
	case DW_OP_reg21:
	case DW_OP_reg22:
	case DW_OP_reg23:
	case DW_OP_reg24:
	case DW_OP_reg25:
	case DW_OP_reg26:
	case DW_OP_reg27:
	case DW_OP_reg28:
	case DW_OP_reg29:
	case DW_OP_reg30:
	case DW_OP_reg31:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_reg%d", op - DW_OP_reg0);
	  if (ok_to_harvest && entry && tag_is_formal_parameter(entry->tag_name)) {
	    harvest_formal_param_location_atom(entry, op, 0);
	  }
	  break;

	case DW_OP_breg0:
	case DW_OP_breg1:
	case DW_OP_breg2:
	case DW_OP_breg3:
	case DW_OP_breg4:
	case DW_OP_breg5:
	case DW_OP_breg6:
	case DW_OP_breg7:
	case DW_OP_breg8:
	case DW_OP_breg9:
	case DW_OP_breg10:
	case DW_OP_breg11:
	case DW_OP_breg12:
	case DW_OP_breg13:
	case DW_OP_breg14:
	case DW_OP_breg15:
	case DW_OP_breg16:
	case DW_OP_breg17:
	case DW_OP_breg18:
	case DW_OP_breg19:
	case DW_OP_breg20:
	case DW_OP_breg21:
	case DW_OP_breg22:
	case DW_OP_breg23:
	case DW_OP_breg24:
	case DW_OP_breg25:
	case DW_OP_breg26:
	case DW_OP_breg27:
	case DW_OP_breg28:
	case DW_OP_breg29:
	case DW_OP_breg30:
	case DW_OP_breg31:
          if (ok_to_harvest)
            {
              unsigned long breg_value = read_leb128 (data, &bytes_read, 1);
              if(ll) {
                ll->atom_offset = breg_value;
              }
              if (print_results_and_ok)
                {
                  FJALAR_DPRINTF ("DW_OP_breg%d: %ld", op - DW_OP_breg0,
                          breg_value);
                }

	      //RUDD DEBUG
	      if(entry) {
		if (tag_is_variable(entry->tag_name)) {
		  harvest_local_var_offset(entry, breg_value);
		}
		else if (tag_is_formal_parameter(entry->tag_name)) {
		  harvest_formal_param_location_atom(entry, op, breg_value);
		  harvest_formal_param_location_offset(entry, breg_value);
		}
	      }

              data += bytes_read;
            }
          else {
            if (print_results_and_ok)
              {
                FJALAR_DPRINTF ("DW_OP_breg%d: %ld", op - DW_OP_breg0,
                        read_leb128 (data, &bytes_read, 1));
                data += bytes_read;
              }
            else
              {
                read_leb128 (data, &bytes_read, 1);
                data += bytes_read;
              }
          }
	  break;

	case DW_OP_regx:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_regx: %lu", read_leb128 (data, &bytes_read, 0));
              data += bytes_read;
            }
          else
            {
              read_leb128 (data, &bytes_read, 0);
              data += bytes_read;
            }
	  break;
	case DW_OP_fbreg:
          if (ok_to_harvest)
            {
              unsigned long fbreg_value = read_leb128 (data, &bytes_read, 1);
              if(ll) {
                ll->atom_offset = fbreg_value;
              }
              if (print_results_and_ok)
                {
                  FJALAR_DPRINTF ("DW_OP_fbreg: %ld", fbreg_value);
                }

	      if(entry) {
		if (tag_is_variable(entry->tag_name)) {
		  harvest_local_var_offset(entry, fbreg_value);
		}
		else if (tag_is_formal_parameter(entry->tag_name)) {
		  harvest_formal_param_location_atom(entry, op, fbreg_value);
		  harvest_formal_param_location_offset(entry, fbreg_value);
		}
	      }

              data += bytes_read;
            }
          else
            {
              read_leb128 (data, &bytes_read, 1);
              data += bytes_read;
            }
	  break;
	case DW_OP_bregx:
          if (print_results_and_ok)
            {
              uvalue = read_leb128 (data, &bytes_read, 0);
              data += bytes_read;
              FJALAR_DPRINTF ("DW_OP_bregx: %lu %ld", uvalue,
                      read_leb128 (data, &bytes_read, 1));
              data += bytes_read;
            }
          else
            {
              uvalue = read_leb128 (data, &bytes_read, 0);
              data += bytes_read;
              read_leb128 (data, &bytes_read, 1);
              data += bytes_read;
            }
          break;
	case DW_OP_piece:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_piece: %lu", read_leb128 (data, &bytes_read, 0));
              data += bytes_read;
            }
          else
            {
              read_leb128 (data, &bytes_read, 0);
              data += bytes_read;
            }
	  break;
	case DW_OP_deref_size:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_deref_size: %ld", (long) byte_get (data++, 1));
            }
          else
            {
              byte_get (data++, 1);
            }
	  break;
	case DW_OP_xderef_size:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_xderef_size: %ld", (long) byte_get (data++, 1));
            }
          else
            {
              byte_get (data++, 1);
            }
	  break;
	case DW_OP_nop:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_nop");
	  break;

	  /* DWARF 3 extensions.  */
	case DW_OP_push_object_address:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_push_object_address");
	  break;
	case DW_OP_call2:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_call2: <%lx>", (long) byte_get (data, 2));
              data += 2;
            }
          else
            {
              byte_get (data, 2);
              data += 2;
            }
	  break;
	case DW_OP_call4:
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF ("DW_OP_call4: <%lx>", (long) byte_get (data, 4));
              data += 4;
            }
          else
            {
              byte_get (data, 4);
              data += 4;
            }
	  break;
	case DW_OP_call_ref:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_call_ref");
	  break;

	  /* GNU extensions.  */
	case DW_OP_GNU_push_tls_address:
	  if (print_results_and_ok) FJALAR_DPRINTF ("DW_OP_GNU_push_tls_address");
	  break;

	default:
	  if (op >= DW_OP_lo_user
	      && op <= DW_OP_hi_user)
	    FJALAR_DPRINTF (_("(User defined location op)"));
	  else
	    FJALAR_DPRINTF (_("(Unknown location op)"));
	  /* No way to tell where the next op is, so just bail.  */
	  return;
	}

      /* Separate the ops.  */
      if (data < end)
        {
          if (print_results_and_ok)
            FJALAR_DPRINTF ("; ");
        }
    }
}

/*
  unsigned op;
  int bytes_read;
  unsigned long uvalue;
  unsigned char *end = data + length;

  while (data < end)
    {
      op = *data++;

      switch (op)
	{
	case DW_OP_addr:
	  if (display) FJALAR_DPRINTF ("DW_OP_addr: %lx",
		  (unsigned long) byte_get (data, pointer_size));
	  data += pointer_size;
	  break;
	case DW_OP_deref:
	  if (display) FJALAR_DPRINTF ("DW_OP_deref");
	  break;
	case DW_OP_const1u:
	  if (display) FJALAR_DPRINTF ("DW_OP_const1u: %lu", (unsigned long) byte_get (data++, 1));
          else data++;
	  break;
	case DW_OP_const1s:
	  if (display) FJALAR_DPRINTF ("DW_OP_const1s: %ld", (long) byte_get (data++, 1));
          else data++;
	  break;
	case DW_OP_const2u:
	  if (display) FJALAR_DPRINTF ("DW_OP_const2u: %lu", (unsigned long) byte_get (data, 2));
	  data += 2;
	  break;
	case DW_OP_const2s:
	  if (display) FJALAR_DPRINTF ("DW_OP_const2s: %ld", (long) byte_get (data, 2));
	  data += 2;
	  break;
	case DW_OP_const4u:
	  if (display) FJALAR_DPRINTF ("DW_OP_const4u: %lu", (unsigned long) byte_get (data, 4));
	  data += 4;
	  break;
	case DW_OP_const4s:
	  if (display) FJALAR_DPRINTF ("DW_OP_const4s: %ld", (long) byte_get (data, 4));
	  data += 4;
	  break;
	case DW_OP_const8u:
	  if (display) FJALAR_DPRINTF ("DW_OP_const8u: %lu %lu", (unsigned long) byte_get (data, 4),
		  (unsigned long) byte_get (data + 4, 4));
	  data += 8;
	  break;
	case DW_OP_const8s:
	  if (display) FJALAR_DPRINTF ("DW_OP_const8s: %ld %ld", (long) byte_get (data, 4),
		  (long) byte_get (data + 4, 4));
	  data += 8;
	  break;
	case DW_OP_constu:
	  if (display) FJALAR_DPRINTF ("DW_OP_constu: %lu", read_leb128 (data, &bytes_read, 0));
	  data += bytes_read;
	  break;
	case DW_OP_consts:
	  if (display) FJALAR_DPRINTF ("DW_OP_consts: %ld", read_leb128 (data, &bytes_read, 1));
	  data += bytes_read;
	  break;
	case DW_OP_dup:
	  if (display) FJALAR_DPRINTF ("DW_OP_dup");
	  break;
	case DW_OP_drop:
	  if (display) FJALAR_DPRINTF ("DW_OP_drop");
	  break;
	case DW_OP_over:
	  if (display) FJALAR_DPRINTF ("DW_OP_over");
	  break;
	case DW_OP_pick:
	  if (display) FJALAR_DPRINTF ("DW_OP_pick: %ld", (unsigned long) byte_get (data++, 1));
          else data++;
	  break;
	case DW_OP_swap:
	  if (display) FJALAR_DPRINTF ("DW_OP_swap");
	  break;
	case DW_OP_rot:
	  if (display) FJALAR_DPRINTF ("DW_OP_rot");
	  break;
	case DW_OP_xderef:
	  if (display) FJALAR_DPRINTF ("DW_OP_xderef");
	  break;
	case DW_OP_abs:
	  if (display) FJALAR_DPRINTF ("DW_OP_abs");
	  break;
	case DW_OP_and:
	  if (display) FJALAR_DPRINTF ("DW_OP_and");
	  break;
	case DW_OP_div:
	  if (display) FJALAR_DPRINTF ("DW_OP_div");
	  break;
	case DW_OP_minus:
	  if (display) FJALAR_DPRINTF ("DW_OP_minus");
	  break;
	case DW_OP_mod:
	  if (display) FJALAR_DPRINTF ("DW_OP_mod");
	  break;
	case DW_OP_mul:
	  if (display) FJALAR_DPRINTF ("DW_OP_mul");
	  break;
	case DW_OP_neg:
	  if (display) FJALAR_DPRINTF ("DW_OP_neg");
	  break;
	case DW_OP_not:
	  if (display) FJALAR_DPRINTF ("DW_OP_not");
	  break;
	case DW_OP_or:
	  if (display) FJALAR_DPRINTF ("DW_OP_or");
	  break;
	case DW_OP_plus:
	  if (display) FJALAR_DPRINTF ("DW_OP_plus");
	  break;
	case DW_OP_plus_uconst:
	  if (display)
            {
              unsigned long uconst_data = read_leb128 (data, &bytes_read, 0);
              if (location_data)
                *location_data = (long)uconst_data;
              FJALAR_DPRINTF ("DW_OP_plus_uconst: %lu",
                      uconst_data);
            }
	  data += bytes_read;
	  break;
	case DW_OP_shl:
	  if (display) FJALAR_DPRINTF ("DW_OP_shl");
	  break;
	case DW_OP_shr:
	  if (display) FJALAR_DPRINTF ("DW_OP_shr");
	  break;
	case DW_OP_shra:
	  if (display) FJALAR_DPRINTF ("DW_OP_shra");
	  break;
	case DW_OP_xor:
	  if (display) FJALAR_DPRINTF ("DW_OP_xor");
	  break;
	case DW_OP_bra:
	  if (display) FJALAR_DPRINTF ("DW_OP_bra: %ld", (long) byte_get (data, 2));
	  data += 2;
	  break;
	case DW_OP_eq:
	  if (display) FJALAR_DPRINTF ("DW_OP_eq");
	  break;
	case DW_OP_ge:
	  if (display) FJALAR_DPRINTF ("DW_OP_ge");
	  break;
	case DW_OP_gt:
	  if (display) FJALAR_DPRINTF ("DW_OP_gt");
	  break;
	case DW_OP_le:
	  if (display) FJALAR_DPRINTF ("DW_OP_le");
	  break;
	case DW_OP_lt:
	  if (display) FJALAR_DPRINTF ("DW_OP_lt");
	  break;
	case DW_OP_ne:
	  if (display) FJALAR_DPRINTF ("DW_OP_ne");
	  break;
	case DW_OP_skip:
	  if (display) FJALAR_DPRINTF ("DW_OP_skip: %ld", (long) byte_get (data, 2));
	  data += 2;
	  break;

	case DW_OP_lit0:
	case DW_OP_lit1:
	case DW_OP_lit2:
	case DW_OP_lit3:
	case DW_OP_lit4:
	case DW_OP_lit5:
	case DW_OP_lit6:
	case DW_OP_lit7:
	case DW_OP_lit8:
	case DW_OP_lit9:
	case DW_OP_lit10:
	case DW_OP_lit11:
	case DW_OP_lit12:
	case DW_OP_lit13:
	case DW_OP_lit14:
	case DW_OP_lit15:
	case DW_OP_lit16:
	case DW_OP_lit17:
	case DW_OP_lit18:
	case DW_OP_lit19:
	case DW_OP_lit20:
	case DW_OP_lit21:
	case DW_OP_lit22:
	case DW_OP_lit23:
	case DW_OP_lit24:
	case DW_OP_lit25:
	case DW_OP_lit26:
	case DW_OP_lit27:
	case DW_OP_lit28:
	case DW_OP_lit29:
	case DW_OP_lit30:
	case DW_OP_lit31:
	  if (display) FJALAR_DPRINTF ("DW_OP_lit%d", op - DW_OP_lit0);
	  break;

	case DW_OP_reg0:
	case DW_OP_reg1:
	case DW_OP_reg2:
	case DW_OP_reg3:
	case DW_OP_reg4:
	case DW_OP_reg5:
	case DW_OP_reg6:
	case DW_OP_reg7:
	case DW_OP_reg8:
	case DW_OP_reg9:
	case DW_OP_reg10:
	case DW_OP_reg11:
	case DW_OP_reg12:
	case DW_OP_reg13:
	case DW_OP_reg14:
	case DW_OP_reg15:
	case DW_OP_reg16:
	case DW_OP_reg17:
	case DW_OP_reg18:
	case DW_OP_reg19:
	case DW_OP_reg20:
	case DW_OP_reg21:
	case DW_OP_reg22:
	case DW_OP_reg23:
	case DW_OP_reg24:
	case DW_OP_reg25:
	case DW_OP_reg26:
	case DW_OP_reg27:
	case DW_OP_reg28:
	case DW_OP_reg29:
	case DW_OP_reg30:
	case DW_OP_reg31:
	  if (display) FJALAR_DPRINTF ("DW_OP_reg%d", op - DW_OP_reg0);
	  break;

	case DW_OP_breg0:
	case DW_OP_breg1:
	case DW_OP_breg2:
	case DW_OP_breg3:
	case DW_OP_breg4:
	case DW_OP_breg5:
	case DW_OP_breg6:
	case DW_OP_breg7:
	case DW_OP_breg8:
	case DW_OP_breg9:
	case DW_OP_breg10:
	case DW_OP_breg11:
	case DW_OP_breg12:
	case DW_OP_breg13:
	case DW_OP_breg14:
	case DW_OP_breg15:
	case DW_OP_breg16:
	case DW_OP_breg17:
	case DW_OP_breg18:
	case DW_OP_breg19:
	case DW_OP_breg20:
	case DW_OP_breg21:
	case DW_OP_breg22:
	case DW_OP_breg23:
	case DW_OP_breg24:
	case DW_OP_breg25:
	case DW_OP_breg26:
	case DW_OP_breg27:
	case DW_OP_breg28:
	case DW_OP_breg29:
	case DW_OP_breg30:
	case DW_OP_breg31:
	  if (display) FJALAR_DPRINTF ("DW_OP_breg%d: %ld", op - DW_OP_breg0,
		  read_leb128 (data, &bytes_read, 1));
	  data += bytes_read;
	  break;

	case DW_OP_regx:
	  if (display) FJALAR_DPRINTF ("DW_OP_regx: %lu", read_leb128 (data, &bytes_read, 0));
	  data += bytes_read;
	  break;
	case DW_OP_fbreg:
	  if (display)
            {
              unsigned long fbreg_value = read_leb128 (data, &bytes_read, 1);
              if (location_data)
                *location_data = (long)fbreg_value;
              FJALAR_DPRINTF ("DW_OP_fbreg: %ld", fbreg_value);
            }
	  data += bytes_read;
	  break;
	case DW_OP_bregx:
	  uvalue = read_leb128 (data, &bytes_read, 0);
	  data += bytes_read;
	  if (display) FJALAR_DPRINTF ("DW_OP_bregx: %lu %ld", uvalue,
		  read_leb128 (data, &bytes_read, 1));
	  data += bytes_read;
	  break;
	case DW_OP_piece:
	  if (display) FJALAR_DPRINTF ("DW_OP_piece: %lu", read_leb128 (data, &bytes_read, 0));
	  data += bytes_read;
	  break;
	case DW_OP_deref_size:
	  if (display) FJALAR_DPRINTF ("DW_OP_deref_size: %ld", (long) byte_get (data++, 1));
          else data++;
	  break;
	case DW_OP_xderef_size:
	  if (display) FJALAR_DPRINTF ("DW_OP_xderef_size: %ld", (long) byte_get (data++, 1));
          else data++;
	  break;
	case DW_OP_nop:
	  if (display) FJALAR_DPRINTF ("DW_OP_nop");
	  break;

	  // DWARF 3 extensions.
	case DW_OP_push_object_address:
	  if (display) FJALAR_DPRINTF ("DW_OP_push_object_address");
	  break;
	case DW_OP_call2:
	  if (display) FJALAR_DPRINTF ("DW_OP_call2: <%lx>", (long) byte_get (data, 2));
	  data += 2;
	  break;
	case DW_OP_call4:
	  if (display) FJALAR_DPRINTF ("DW_OP_call4: <%lx>", (long) byte_get (data, 4));
	  data += 4;
	  break;
	case DW_OP_call_ref:
	  if (display) FJALAR_DPRINTF ("DW_OP_call_ref");
	  break;

	  // GNU extensions.
	case DW_OP_GNU_push_tls_address:
	  if (display) FJALAR_DPRINTF ("DW_OP_GNU_push_tls_address");
	  break;

	default:
	  if (op >= DW_OP_lo_user
	      && op <= DW_OP_hi_user)
            {
              if (display) FJALAR_DPRINTF (_("(User defined location op)"));
            }
	  else
            {
              if (display) FJALAR_DPRINTF (_("(Unknown location op)"));
            }
	  // No way to tell where the next op is, so just bail.
	  return;
	}

      // Separate the ops.
      if (data < end)
        {
          if (display) FJALAR_DPRINTF ("; ");
        }
    }
}
*/

static const char *debug_loc_contents;
static bfd_vma debug_loc_size;

static void
load_debug_loc (file)
     FILE *file;
{
  Elf_Internal_Shdr *sec;
  unsigned int i;

  /* If it is already loaded, do nothing.  */
  if (debug_loc_contents != NULL)
    return;

  /* Locate the .debug_loc section.  */
  for (i = 0, sec = section_headers;
       i < elf_header.e_shnum;
       i++, sec++)
    if (VG_(strcmp) (SECTION_NAME (sec), ".debug_loc") == 0)
      break;

  if (i == elf_header.e_shnum || sec->sh_size == 0)
    return;

  debug_loc_size = sec->sh_size;

  debug_loc_contents = ((char *)
			get_data (NULL, file, sec->sh_offset, sec->sh_size,
				  _("debug_loc section data")));
}

static void
free_debug_loc ()
{
  if (debug_loc_contents == NULL)
    return;

  VG_(free) ((char *) debug_loc_contents);
  debug_loc_contents = NULL;
  debug_loc_size = 0;
}


static int
display_debug_loc (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned char *section_end;
  unsigned long bytes;
  unsigned char *section_begin = start;
  bfd_vma addr;

  addr = section->sh_addr;
  bytes = section->sh_size;
  section_end = start + bytes;

  if (bytes == 0)
    {
      FJALAR_DPRINTF (_("\nThe .debug_loc section is empty.\n"));
      return 0;
    }

  FJALAR_DPRINTF (_("Contents of the .debug_loc section:\n\n"));
  FJALAR_DPRINTF (_("\n    Offset   Begin    End      Expression\n"));

  while (start < section_end)
    {
      unsigned long begin;
      unsigned long end;
      unsigned short length;
      unsigned long offset;

      offset = start - section_begin;

      while (1)
	{
	  /* Normally, the lists in the debug_loc section are related to a
	     given compilation unit, and thus, we would use the pointer size
	     of that compilation unit.  However, since we are displaying it
	     seperately here, we either have to store pointer sizes of all
	     compilation units, or assume they don't change.   We assume,
	     like the debug_line display, that it doesn't change.  */
          location_list* ll = VG_(calloc)("readelf.c: display_debug_loc", sizeof(location_list), 1);

	  begin = byte_get (start, debug_line_pointer_size);
	  start += debug_line_pointer_size;
	  end = byte_get (start, debug_line_pointer_size);
	  start += debug_line_pointer_size;

	  if (begin == 0 && end == 0)
	    break;

	  /* For now, skip any base address specifiers.  */
	  if (begin == 0xffffffff)
	    continue;

	  begin += addr;
	  end += addr;

	  length = byte_get (start, 2);
	  start += 2;

          FJALAR_DPRINTF ("    %8.8lx %8.8lx %8.8lx (", offset, begin, end);
          ll->offset = offset;
          ll->begin = begin;
          ll->end = end;
	  decode_location_expression (start, debug_line_pointer_size, length, 1, 0, ll);

	  FJALAR_DPRINTF (")\n");


          harvest_location_list_entry(ll, offset);
	  start += length;
	}
      FJALAR_DPRINTF ("\n");
    }
  return 1;
}

static const char *debug_str_contents;
static bfd_vma debug_str_size;

static void
load_debug_str (file)
     FILE *file;
{
  Elf_Internal_Shdr *sec;
  unsigned int i;

  /* If it is already loaded, do nothing.  */
  if (debug_str_contents != NULL)
    return;

  /* Locate the .debug_str section.  */
  for (i = 0, sec = section_headers;
       i < elf_header.e_shnum;
       i++, sec++)
    if (VG_(strcmp) (SECTION_NAME (sec), ".debug_str") == 0)
      break;

  if (i == elf_header.e_shnum || sec->sh_size == 0)
    return;

  debug_str_size = sec->sh_size;

  debug_str_contents = ((char *)
			get_data (NULL, file, sec->sh_offset, sec->sh_size,
				  _("debug_str section data")));
}

static void
free_debug_str ()
{
  if (debug_str_contents == NULL)
    return;

  VG_(free) ((char *) debug_str_contents);
  debug_str_contents = NULL;
  debug_str_size = 0;
}

static const char *
fetch_indirect_string (offset)
     unsigned long offset;
{
  if (debug_str_contents == NULL)
    return _("<no .debug_str section>");

  if (offset > debug_str_size)
    return _("<offset is too big>");

  return debug_str_contents + offset;
}

static int
display_debug_str (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned long bytes;
  bfd_vma addr;

  addr  = section->sh_addr;
  bytes = section->sh_size;

  if (bytes == 0)
    {
      FJALAR_DPRINTF (_("\nThe .debug_str section is empty.\n"));
      return 0;
    }

  FJALAR_DPRINTF (_("Contents of the .debug_str section:\n\n"));

  while (bytes)
    {
      int j;
      int k;
      int lbytes;

      lbytes = (bytes > 16 ? 16 : bytes);

      FJALAR_DPRINTF ("  0x%8.8lx ", (unsigned long) addr);

      for (j = 0; j < 16; j++)
	{
	  if (j < lbytes)
	    FJALAR_DPRINTF ("%2.2x", start[j]);
	  else
	    FJALAR_DPRINTF ("  ");

	  if ((j & 3) == 3)
	    FJALAR_DPRINTF (" ");
	}

      for (j = 0; j < lbytes; j++)
	{
	  k = start[j];
	  if (k >= ' ' && k < 0x80)
	    FJALAR_DPRINTF ("%c", k);
	  else
	    FJALAR_DPRINTF (".");
	}

      putchar ('\n');

      start += lbytes;
      addr  += lbytes;
      bytes -= lbytes;
    }

  return 1;
}

static unsigned char *
read_and_display_attr_value (attribute, form, data, cu_offset, pointer_size,
                             offset_size, dwarf_version, entry, ok)
     unsigned long attribute;
     unsigned long form;
     unsigned char *data;
     unsigned long cu_offset;
     unsigned long pointer_size;
     unsigned long offset_size;
     int dwarf_version;
     dwarf_entry* entry;
     char ok;
{
  unsigned long uvalue = 0;
  unsigned char *block_start = NULL;
  int bytes_read;

  int print_results_and_ok = print_results && ok;

  switch (form)
    {
    default:
      break;

    case DW_FORM_ref_addr:
      if (dwarf_version == 2)
	{
	  uvalue = byte_get (data, pointer_size);
	  data += pointer_size;
	}
      else if (dwarf_version == 3)
	{
	  uvalue = byte_get (data, offset_size);
	  data += offset_size;
	}
      else
        {
	  error (_("Internal error: DWARF version is not 2 or 3.\n"));
	}
      break;

    case DW_FORM_addr:
      uvalue = byte_get (data, pointer_size);
      data += pointer_size;
      break;

    case DW_FORM_strp:
      uvalue = byte_get (data, offset_size);
      data += offset_size;
      break;

    case DW_FORM_ref1:
    case DW_FORM_flag:
    case DW_FORM_data1:
      uvalue = byte_get (data++, 1);
      break;

    case DW_FORM_ref2:
    case DW_FORM_data2:
      uvalue = byte_get (data, 2);
      data += 2;
      break;

    case DW_FORM_ref4:
    case DW_FORM_data4:
      uvalue = byte_get (data, 4);
      data += 4;
      break;

    case DW_FORM_sdata:
      uvalue = read_leb128 (data, & bytes_read, 1);
      data += bytes_read;
      break;

    case DW_FORM_ref_udata:
    case DW_FORM_udata:
      uvalue = read_leb128 (data, & bytes_read, 0);
      data += bytes_read;
      break;

    case DW_FORM_indirect:
      form = read_leb128 (data, & bytes_read, 0);
      data += bytes_read;
      if (print_results_and_ok) {FJALAR_DPRINTF (" %s", get_FORM_name (form));}
      return read_and_display_attr_value (attribute, form, data, cu_offset,
					  pointer_size, offset_size,
					  dwarf_version, entry, ok);
    }

  switch (form)
    {
    case DW_FORM_ref_addr:
      if (print_results_and_ok) {FJALAR_DPRINTF (" <#%lx>", uvalue);}
      break;

      // DW_AT_type returns data in this form (REMEMBER cu_offset!):
    case DW_FORM_ref1:
    case DW_FORM_ref2:
    case DW_FORM_ref4:
    case DW_FORM_ref_udata:
      if (ok)
        {
          if (DW_AT_type == attribute) {
            harvest_type_value(entry, uvalue + cu_offset);
          }

	  if (DW_AT_sibling == attribute) {
	    harvest_sibling(entry, uvalue + cu_offset);
	  }
	  if (DW_AT_specification == attribute) {
	    harvest_specification_value(entry, uvalue + cu_offset);
	  }
          if (DW_AT_abstract_origin == attribute) {
            harvest_abstract_origin_value(entry, uvalue + cu_offset);
          }

          if (print_results)
            {
              FJALAR_DPRINTF (" <%lx>", uvalue + cu_offset);
            }
        }
      break;

    case DW_FORM_addr:
      if (ok)
        {
          harvest_address_value(entry, attribute, uvalue);
          if (print_results)
            FJALAR_DPRINTF (" %#lx", uvalue);
        }
      break;
      if (print_results_and_ok)

      // DW_AT_byte_size, DW_AT_encoding, DW_AT_const_value,
      // DW_AT_bit_size, DW_AT_bit_offset, DW_AT_external, DW_AT_upper_bound
      // return data in this form:
    case DW_FORM_flag:
    case DW_FORM_data1:
    case DW_FORM_data2:
    case DW_FORM_data4:
    case DW_FORM_sdata:
    case DW_FORM_udata:
      if (ok)
        {
          harvest_ordinary_unsigned_value(entry, attribute, uvalue);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF (" %ld", uvalue);
            }
        }
      break;

    case DW_FORM_ref8:
    case DW_FORM_data8:
      uvalue = byte_get (data, 4);
      if (print_results_and_ok) {FJALAR_DPRINTF (" %lx", uvalue);}
      if (print_results_and_ok)
        {
          uvalue |= byte_get (data +4, 4) << 32;
                              //printf (" %lx", (unsigned long) byte_get (data + 4, 4));
        }
      else
        {
          byte_get (data + 4, 4);
        }
      data += 8;
      break;

      // DW_AT_name/DW_AT_comp_dir can be a string, or an indirect string ... (see below)
    case DW_FORM_string:
      if (ok)
        {
          harvest_string(entry, attribute, data);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF (" %s", data);
            }
        }
      data += VG_(strlen) ((char *) data) + 1;
      break;

    case DW_FORM_block:
      uvalue = read_leb128 (data, & bytes_read, 0);
      block_start = data + bytes_read;
      data = display_block (block_start, uvalue, ok);
      break;

    case DW_FORM_block1:
      uvalue = byte_get (data, 1);
      block_start = data + 1;
      data = display_block (block_start, uvalue, ok);
      break;

    case DW_FORM_block2:
      uvalue = byte_get (data, 2);
      block_start = data + 2;
      data = display_block (block_start, uvalue, ok);
      break;

    case DW_FORM_block4:
      uvalue = byte_get (data, 4);
      block_start = data + 4;
      data = display_block (block_start, uvalue, ok);
      break;

      // DW_AT_name/DW_AT_comp_dir can be an indirect string ... but it can also be a string (see above)
    case DW_FORM_strp:
      if (ok)
        {
          const char* ind_str = fetch_indirect_string (uvalue);
          harvest_string(entry, attribute, ind_str);
          if (print_results_and_ok)
            {
              FJALAR_DPRINTF (_(" (indirect string, offset: 0x%lx): %s"),
                      uvalue, ind_str);
            }
        }
      break;

    case DW_FORM_indirect:
      /* Handled above.  */
      break;

    default:
      warn (_("Unrecognized form: %d\n"), form);
      break;
    }

  /* For some attributes we can display futher information.  */

  if (print_results_and_ok) {FJALAR_DPRINTF ("\t");}

  switch (attribute)
    {
    case DW_AT_inline:
      switch (uvalue)
	{
	case DW_INL_not_inlined:
          if (print_results_and_ok) {FJALAR_DPRINTF (_("(not inlined)"));}
	  break;
	case DW_INL_inlined:
          if (print_results_and_ok) {FJALAR_DPRINTF (_("(inlined)"));}
	  break;
	case DW_INL_declared_not_inlined:
          if (print_results_and_ok) {FJALAR_DPRINTF (_("(declared as inline but ignored)"));}
	  break;
	case DW_INL_declared_inlined:
          if (print_results_and_ok) {FJALAR_DPRINTF (_("(declared as inline and inlined)"));}
	  break;
	default:
          if (print_results_and_ok) {FJALAR_DPRINTF (_("  (Unknown inline attribute value: %lx)"), uvalue);}
	  break;
	}
      break;

    case DW_AT_language:
      switch (uvalue)
	{
	case DW_LANG_C:			if (print_results_and_ok) {FJALAR_DPRINTF ("(non-ANSI C)");} break;
	case DW_LANG_C89:		if (print_results_and_ok) {FJALAR_DPRINTF ("(ANSI C)");} break;
	case DW_LANG_C_plus_plus:	if (print_results_and_ok) {FJALAR_DPRINTF ("(C++)");} break;
	case DW_LANG_Fortran77:		if (print_results_and_ok) {FJALAR_DPRINTF ("(FORTRAN 77)");} break;
	case DW_LANG_Fortran90:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Fortran 90)");} break;
	case DW_LANG_Modula2:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Modula 2)");} break;
	case DW_LANG_Pascal83:		if (print_results_and_ok) {FJALAR_DPRINTF ("(ANSI Pascal)");} break;
	case DW_LANG_Ada83:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Ada)");} break;
	case DW_LANG_Cobol74:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Cobol 74)");} break;
	case DW_LANG_Cobol85:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Cobol 85)");} break;
	  /* DWARF 2.1 values.	*/
	case DW_LANG_C99:		if (print_results_and_ok) {FJALAR_DPRINTF ("(ANSI C99)");} break;
	case DW_LANG_Ada95:		if (print_results_and_ok) {FJALAR_DPRINTF ("(ADA 95)");} break;
	case DW_LANG_Fortran95:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Fortran 95)");} break;
	  /* MIPS extension.  */
	case DW_LANG_Mips_Assembler:	if (print_results_and_ok) {FJALAR_DPRINTF ("(MIPS assembler)");} break;
	  /* UPC extension.  */
	case DW_LANG_Upc:		if (print_results_and_ok) {FJALAR_DPRINTF ("(Unified Parallel C)");} break;
	default:
	  if (print_results_and_ok) {FJALAR_DPRINTF ("(Unknown: %lx)", uvalue);}
	  break;
	}
      break;

    case DW_AT_encoding:
      switch (uvalue)
	{
	case DW_ATE_void:		if (print_results_and_ok) {FJALAR_DPRINTF ("(void)");} break;
	case DW_ATE_address:		if (print_results_and_ok) {FJALAR_DPRINTF ("(machine address)");} break;
	case DW_ATE_boolean:		if (print_results_and_ok) {FJALAR_DPRINTF ("(boolean)");} break;
	case DW_ATE_complex_float:	if (print_results_and_ok) {FJALAR_DPRINTF ("(complex float)");} break;
	case DW_ATE_float:		if (print_results_and_ok) {FJALAR_DPRINTF ("(float)");} break;
	case DW_ATE_signed:		if (print_results_and_ok) {FJALAR_DPRINTF ("(signed)");} break;
	case DW_ATE_signed_char:	if (print_results_and_ok) {FJALAR_DPRINTF ("(signed char)");} break;
	case DW_ATE_unsigned:		if (print_results_and_ok) {FJALAR_DPRINTF ("(unsigned)");} break;
	case DW_ATE_unsigned_char:	if (print_results_and_ok) {FJALAR_DPRINTF ("(unsigned char)");} break;
	  /* DWARF 2.1 value.  */
	case DW_ATE_imaginary_float:	if (print_results_and_ok) {FJALAR_DPRINTF ("(imaginary float)");} break;
	default:
	  if (uvalue >= DW_ATE_lo_user
	      && uvalue <= DW_ATE_hi_user)
            {
	    if (print_results_and_ok) {FJALAR_DPRINTF ("(user defined type)");}
            }
	  else
            {
	    if (print_results_and_ok) {FJALAR_DPRINTF ("(unknown type)");}
            }
	  break;
	}
      break;

    case DW_AT_accessibility:
      switch (uvalue)
	{
	case DW_ACCESS_public:
          if (print_results_and_ok) FJALAR_DPRINTF ("(public)");
          if (ok) harvest_accessibility(entry, DW_ACCESS_public);
          break;
	case DW_ACCESS_protected:
          if (print_results_and_ok) FJALAR_DPRINTF ("(protected)");
          if (ok) harvest_accessibility(entry, DW_ACCESS_protected);
          break;
	case DW_ACCESS_private:
          if (print_results_and_ok) FJALAR_DPRINTF ("(private)");
          if (ok) harvest_accessibility(entry, DW_ACCESS_private);
          break;
	default:
	  if (print_results_and_ok) FJALAR_DPRINTF ("(unknown accessibility)");
	  break;
	}
      break;

    case DW_AT_visibility:
      switch (uvalue)
	{
	case DW_VIS_local:		if (print_results_and_ok) FJALAR_DPRINTF ("(local)"); break;
	case DW_VIS_exported:		if (print_results_and_ok) FJALAR_DPRINTF ("(exported)"); break;
	case DW_VIS_qualified:		if (print_results_and_ok) FJALAR_DPRINTF ("(qualified)"); break;
	default:			if (print_results_and_ok) FJALAR_DPRINTF ("(unknown visibility)"); break;
	}
      break;

    case DW_AT_virtuality:
      switch (uvalue)
	{
	case DW_VIRTUALITY_none:	if (print_results_and_ok) FJALAR_DPRINTF ("(none)"); break;
	case DW_VIRTUALITY_virtual:	if (print_results_and_ok) FJALAR_DPRINTF ("(virtual)"); break;
	case DW_VIRTUALITY_pure_virtual:if (print_results_and_ok) FJALAR_DPRINTF ("(pure_virtual)"); break;
	default:			if (print_results_and_ok) FJALAR_DPRINTF ("(unknown virtuality)"); break;
	}
      break;

    case DW_AT_identifier_case:
      switch (uvalue)
	{
	case DW_ID_case_sensitive:	if (print_results_and_ok) FJALAR_DPRINTF ("(case_sensitive)"); break;
	case DW_ID_up_case:		if (print_results_and_ok) FJALAR_DPRINTF ("(up_case)"); break;
	case DW_ID_down_case:		if (print_results_and_ok) FJALAR_DPRINTF ("(down_case)"); break;
	case DW_ID_case_insensitive:	if (print_results_and_ok) FJALAR_DPRINTF ("(case_insensitive)"); break;
	default:			if (print_results_and_ok) FJALAR_DPRINTF ("(unknown case)"); break;
	}
      break;

    case DW_AT_calling_convention:
      switch (uvalue)
	{
	case DW_CC_normal:	if (print_results_and_ok) FJALAR_DPRINTF ("(normal)"); break;
	case DW_CC_program:	if (print_results_and_ok) FJALAR_DPRINTF ("(program)"); break;
	case DW_CC_nocall:	if (print_results_and_ok) FJALAR_DPRINTF ("(nocall)"); break;
	default:
	  if (uvalue >= DW_CC_lo_user
	      && uvalue <= DW_CC_hi_user)
            {
              if (print_results_and_ok) FJALAR_DPRINTF ("(user defined)");
            }
	  else
            {
              if (print_results_and_ok) FJALAR_DPRINTF ("(unknown convention)");
            }
	}
      break;

    case DW_AT_ordering:
      switch (uvalue)
	{
	case -1: if (print_results_and_ok) FJALAR_DPRINTF ("(undefined)"); break;
	case 0:  if (print_results_and_ok) FJALAR_DPRINTF ("(row major)"); break;
	case 1:  if (print_results_and_ok) FJALAR_DPRINTF ("(column major)"); break;
	}
      break;

      // DW_AT_location, DW_AT_data_member_location return data in this form:
    case DW_AT_location:
      if (block_start)
	{
	  if (print_results_and_ok) FJALAR_DPRINTF ("(");
	  decode_location_expression (block_start, pointer_size, uvalue, ok, entry, 0);
	  if (print_results_and_ok) FJALAR_DPRINTF (")");
	}
      else if (form == DW_FORM_data4 || form == DW_FORM_data8)
	{
	  if (print_results_and_ok) FJALAR_DPRINTF ("(");
	  if (print_results_and_ok) FJALAR_DPRINTF ("location list");
	  if (print_results_and_ok) FJALAR_DPRINTF (")");
	}
      break;

    case DW_AT_data_member_location:
      if (block_start)
	{
	  if (print_results_and_ok) FJALAR_DPRINTF ("(");
	  decode_location_expression (block_start, pointer_size, uvalue, ok, entry, 0);
	  if (print_results_and_ok) FJALAR_DPRINTF (")");
	}
      else if (form == DW_FORM_data4 || form == DW_FORM_data8)
	{
          if (print_results_and_ok) FJALAR_DPRINTF ("(");
          if (print_results_and_ok) FJALAR_DPRINTF ("location list");
          if (print_results_and_ok) FJALAR_DPRINTF (")");
	}
      break;

    case DW_AT_frame_base:
    case DW_AT_vtable_elem_location:
    case DW_AT_allocated:
    case DW_AT_associated:
    case DW_AT_data_location:
    case DW_AT_stride:
    case DW_AT_upper_bound:
    case DW_AT_lower_bound:
      if (block_start)
	{
          if (print_results_and_ok) FJALAR_DPRINTF ("(");
	  decode_location_expression (block_start, pointer_size, uvalue, ok, entry, 0);
          if (print_results_and_ok) FJALAR_DPRINTF (")");
	}
      else if (form == DW_FORM_data4 || form == DW_FORM_data8)
	{
          // RUDD
          harvest_frame_base(entry, DW_OP_list, uvalue);
          if (print_results_and_ok) FJALAR_DPRINTF ("(");
          if (print_results_and_ok) FJALAR_DPRINTF ("location list");
          if (print_results_and_ok) FJALAR_DPRINTF (")");
	}
      break;
    case DW_AT_stmt_list:
      harvest_stmt_list(entry, uvalue);
      break;
    case DW_AT_decl_file:
      harvest_decl_file(entry, uvalue);
      break;
    default:
      break;
    }

  return data;
}

static unsigned char *
read_and_display_attr (attribute, form, data, cu_offset, pointer_size,
                       offset_size, dwarf_version, entry, ok_to_harvest)
     unsigned long attribute;
     unsigned long form;
     unsigned char *data;
     unsigned long cu_offset;
     unsigned long pointer_size;
     unsigned long offset_size;
     int dwarf_version;
     dwarf_entry* entry;
     char ok_to_harvest;
{
  char entry_is_listening = entry_is_listening_for_attribute(entry, attribute);

  // Ok process attributes when ok_to_harvest is on and the entry is listening:
  char ok_to_process = entry_is_listening && ok_to_harvest;
  //  FJALAR_DPRINTF("ENTRY LISTENING: %d\n", (int)entry_is_listening);
  //  if (ok_to_process)
  if (print_results && ok_to_process)
    FJALAR_DPRINTF ("     %-18s:", get_AT_name (attribute));
  data = read_and_display_attr_value (attribute, form, data, cu_offset,
				      pointer_size, offset_size, dwarf_version,
                                      entry, ok_to_process);
  if (ok_to_process && print_results)
    FJALAR_DPRINTF ("\n");
  return data;
}

static int
display_debug_info (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file;
{
  unsigned char *end = start + section->sh_size;
  unsigned char *section_begin = start;

  // PG - Number of relevant entries to record in the dwarf_entry array
  unsigned long num_relevant_entries = 0;
  unsigned long idx = 0; // The index in the array, (< dwarf_entry_array_size)

  // PG - Do one dummy run to see how many entries need to be put in the dwarf_entry array
  // The sole purpose of this run is to get a number into num_relevant_entries
  Elf_Internal_Shdr *section_dummy = section;
  unsigned char *start_dummy = start;
  FILE *file_dummy = file;

  unsigned char *end_dummy = start_dummy + section_dummy->sh_size;
  unsigned char *section_begin_dummy = start_dummy;

  // We're going to need to keep an array of compile units
  unsigned long num_compile_units = 0;

  //  FJALAR_DPRINTF (_("The section %s contains:\n\n"), SECTION_NAME (section_dummy));

  load_debug_str (file_dummy);
  load_debug_loc (file_dummy);

  while (start_dummy < end_dummy)
    {
      DWARF2_Internal_CompUnit compunit;
      Elf_Internal_Shdr *relsec;
      unsigned char *hdrptr;
      unsigned char *cu_abbrev_offset_ptr;
      unsigned char *tags;
      unsigned int i;
      int level;
      unsigned long cu_offset;
      int offset_size;
      int initial_length_size;

      hdrptr = start_dummy;

      compunit.cu_length = byte_get (hdrptr, 4);
      hdrptr += 4;

      if (compunit.cu_length == 0xffffffff)
	{
	  compunit.cu_length = byte_get (hdrptr, 8);
	  hdrptr += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      compunit.cu_version = byte_get (hdrptr, 2);
      hdrptr += 2;

      /* Apply addends of RELA relocations.  */
      for (relsec = section_headers;
	   relsec < section_headers + elf_header.e_shnum;
	   ++relsec)
	{
	  unsigned long nrelas;
	  Elf_Internal_Rela *rela, *rp;
	  Elf_Internal_Shdr *symsec;
	  Elf_Internal_Sym *symtab;
	  Elf_Internal_Sym *sym;

	  if (relsec->sh_type != SHT_RELA
	      || SECTION_HEADER (relsec->sh_info) != section_dummy
	      || relsec->sh_size == 0)
	    continue;

	  if (!slurp_rela_relocs (file_dummy, relsec->sh_offset, relsec->sh_size,
				  & rela, & nrelas))
	    return 0;

	  symsec = SECTION_HEADER (relsec->sh_link);
	  symtab = GET_ELF_SYMBOLS (file_dummy, symsec);

	  for (rp = rela; rp < rela + nrelas; ++rp)
	    {
	      unsigned char *loc;

	      if (rp->r_offset >= (bfd_vma) (hdrptr - section_begin_dummy)
		  && section_dummy->sh_size > (bfd_vma) offset_size
		  && rp->r_offset <= section_dummy->sh_size - offset_size)
		loc = section_begin_dummy + rp->r_offset;
	      else
		continue;

	      if (is_32bit_elf)
		{
		  sym = symtab + ELF32_R_SYM (rp->r_info);

		  if (ELF32_R_SYM (rp->r_info) != 0
		      && ELF32_ST_TYPE (sym->st_info) != STT_SECTION)
		    {
		      warn (_("Skipping unexpected symbol type %u\n"),
			    ELF32_ST_TYPE (sym->st_info));
		      continue;
		    }
		}
	      else
		{
		  sym = symtab + ELF64_R_SYM (rp->r_info);

		  if (ELF64_R_SYM (rp->r_info) != 0
		      && ELF64_ST_TYPE (sym->st_info) != STT_SECTION)
		    {
		      warn (_("Skipping unexpected symbol type %u\n"),
			    ELF64_ST_TYPE (sym->st_info));
		      continue;
		    }
		}

	      byte_put (loc, rp->r_addend, offset_size);
	    }

	  VG_(free) (rela);
	  break;
	}

      cu_abbrev_offset_ptr = hdrptr;
      compunit.cu_abbrev_offset = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;

      compunit.cu_pointer_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      tags = hdrptr;
      cu_offset = start_dummy - section_begin_dummy;
      start_dummy += compunit.cu_length + initial_length_size;
      
      num_compile_units++;
      //      FJALAR_DPRINTF (_("  Compilation Unit @ %lx:\n"), cu_offset);
      //      FJALAR_DPRINTF (_("   Length:        %ld\n"), compunit.cu_length);
      //      FJALAR_DPRINTF (_("   Version:       %d\n"), compunit.cu_version);
      //      FJALAR_DPRINTF (_("   Abbrev Offset: %ld\n"), compunit.cu_abbrev_offset);
      //      FJALAR_DPRINTF (_("   Pointer Size:  %d\n"), compunit.cu_pointer_size);

      if (compunit.cu_version != 2 && compunit.cu_version != 3)
	{
	  warn (_("Only version 2 and 3 DWARF debug information is currently supported.\n"));
	  continue;
	}

      free_abbrevs ();

      /* Read in the abbrevs used by this compilation unit.  */
      {
	Elf_Internal_Shdr *sec;
	unsigned char *begin;

	/* Locate the .debug_abbrev section and process it.  */
	for (i = 0, sec = section_headers;
	     i < elf_header.e_shnum;
	     i++, sec++)
	  if (VG_(strcmp) (SECTION_NAME (sec), ".debug_abbrev") == 0)
	    break;

	if (i == elf_header.e_shnum || sec->sh_size == 0)
	  {
	    warn (_("Unable to locate .debug_abbrev section!\n"));
	    return 0;
	  }

	begin = ((unsigned char *)
		 get_data (NULL, file_dummy, sec->sh_offset, sec->sh_size,
			   _("debug_abbrev section data")));
	if (!begin)
	  return 0;

	process_abbrev_section (begin + compunit.cu_abbrev_offset,
				begin + sec->sh_size);

	VG_(free) (begin);
      }

      level = 0;
      while (tags < start_dummy)
	{
	  int bytes_read;
	  unsigned long abbrev_number;
	  abbrev_entry *entry;
	  abbrev_attr *attr;
          char is_relevant_entry; // PG
          dwarf_entry my_dwarf_entry = {0, 0, 0, 0, NULL};

	  abbrev_number = read_leb128 (tags, & bytes_read, 0);
	  tags += bytes_read;

	  /* A null DIE marks the end of a list of children.  */
	  if (abbrev_number == 0)
	    {
	      --level;
	      continue;
	    }

	  /* Scan through the abbreviation list until we reach the
	     correct entry.  */
	  for (entry = first_abbrev;
	       entry && entry->entry != abbrev_number;
	       entry = entry->next)
	    continue;

	  if (entry == NULL)
	    {
	      warn (_("Unable to locate entry %lu in the abbreviation table\n"),
		    abbrev_number);
	      return 0;
	    }

          // PG - increment relevant entry and make a note of it:
          is_relevant_entry = tag_is_relevant_entry(entry->tag);
          if (is_relevant_entry)
            {
              num_relevant_entries++;
            }

          my_dwarf_entry.tag_name = entry->tag;

	  for (attr = entry->first_attr; attr; attr = attr->next)
	    tags = read_and_display_attr (attr->attribute,
					  attr->form,
					  tags, cu_offset,
					  compunit.cu_pointer_size,
					  offset_size,
					  compunit.cu_version,
                                          &my_dwarf_entry,
                                          0); // parse tags but DO NOT harvest data

	  if (entry->children)
	    ++level;
	}
    }

  free_debug_str ();
  free_debug_loc ();

#ifdef SHOW_DEBUG
  FJALAR_DPRINTF ("Number of relevant entries: %u\n\n", num_relevant_entries);
#endif
  // PG - End dummy run code

  // Construct the global dwarf_entry array
  // Question - when do we destroy it???
  dwarf_entry_array_size = num_relevant_entries;
  initialize_dwarf_entry_array(num_relevant_entries);
  initialize_compile_unit_array(num_compile_units);

  // PG - Begin real code
#ifdef SHOW_DEBUG
  FJALAR_DPRINTF (_("The section %s contains:\n\n"), SECTION_NAME (section));
#endif

  load_debug_str (file);
  load_debug_loc (file);

  while (start < end)
    {
      DWARF2_Internal_CompUnit compunit;
      Elf_Internal_Shdr *relsec;
      unsigned char *hdrptr;
      unsigned char *cu_abbrev_offset_ptr;
      unsigned char *tags;
      unsigned int i;
      int level;
      unsigned long cu_offset;
      int offset_size;
      int initial_length_size;
      compile_unit* cur_comp_unit = NULL; //rudd

      hdrptr = start;

      compunit.cu_length = byte_get (hdrptr, 4);
      hdrptr += 4;

      if (compunit.cu_length == 0xffffffff)
	{
	  compunit.cu_length = byte_get (hdrptr, 8);
	  hdrptr += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      compunit.cu_version = byte_get (hdrptr, 2);
      hdrptr += 2;

      /* Apply addends of RELA relocations.  */
      for (relsec = section_headers;
	   relsec < section_headers + elf_header.e_shnum;
	   ++relsec)
	{
	  unsigned long nrelas;
	  Elf_Internal_Rela *rela, *rp;
	  Elf_Internal_Shdr *symsec;
	  Elf_Internal_Sym *symtab;
	  Elf_Internal_Sym *sym;

	  if (relsec->sh_type != SHT_RELA
	      || SECTION_HEADER (relsec->sh_info) != section
	      || relsec->sh_size == 0)
	    continue;

	  if (!slurp_rela_relocs (file, relsec->sh_offset, relsec->sh_size,
				  & rela, & nrelas))
	    return 0;

	  symsec = SECTION_HEADER (relsec->sh_link);
	  symtab = GET_ELF_SYMBOLS (file, symsec);

	  for (rp = rela; rp < rela + nrelas; ++rp)
	    {
	      unsigned char *loc;

	      if (rp->r_offset >= (bfd_vma) (hdrptr - section_begin)
		  && section->sh_size > (bfd_vma) offset_size
		  && rp->r_offset <= section->sh_size - offset_size)
		loc = section_begin + rp->r_offset;
	      else
		continue;

	      if (is_32bit_elf)
		{
		  sym = symtab + ELF32_R_SYM (rp->r_info);

		  if (ELF32_R_SYM (rp->r_info) != 0
		      && ELF32_ST_TYPE (sym->st_info) != STT_SECTION)
		    {
		      warn (_("Skipping unexpected symbol type %u\n"),
			    ELF32_ST_TYPE (sym->st_info));
		      continue;
		    }
		}
	      else
		{
		  sym = symtab + ELF64_R_SYM (rp->r_info);

		  if (ELF64_R_SYM (rp->r_info) != 0
		      && ELF64_ST_TYPE (sym->st_info) != STT_SECTION)
		    {
		      warn (_("Skipping unexpected symbol type %u\n"),
			    ELF64_ST_TYPE (sym->st_info));
		      continue;
		    }
		}

	      byte_put (loc, rp->r_addend, offset_size);
	    }

	  VG_(free) (rela);
	  break;
	}

      cu_abbrev_offset_ptr = hdrptr;
      compunit.cu_abbrev_offset = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;

      compunit.cu_pointer_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      tags = hdrptr;
      cu_offset = start - section_begin;
      start += compunit.cu_length + initial_length_size;

#ifdef SHOW_DEBUG
      FJALAR_DPRINTF (_("  Compilation Unit @ %lx:\n"), cu_offset);
      FJALAR_DPRINTF (_("   Length:        %ld\n"), compunit.cu_length);
      FJALAR_DPRINTF (_("   Version:       %d\n"), compunit.cu_version);
      FJALAR_DPRINTF (_("   Abbrev Offset: %ld\n"), compunit.cu_abbrev_offset);
      FJALAR_DPRINTF (_("   Pointer Size:  %d\n"), compunit.cu_pointer_size);
#endif

      if (compunit.cu_version != 2 && compunit.cu_version != 3)
	{
	  warn (_("Only version 2 and 3 DWARF debug information is currently supported.\n"));
	  continue;
	}

      free_abbrevs ();

      /* Read in the abbrevs used by this compilation unit.  */
      {
	Elf_Internal_Shdr *sec;
	unsigned char *begin;

	/* Locate the .debug_abbrev section and process it.  */
	for (i = 0, sec = section_headers;
	     i < elf_header.e_shnum;
	     i++, sec++)
	  if (VG_(strcmp) (SECTION_NAME (sec), ".debug_abbrev") == 0)
	    break;

	if (i == elf_header.e_shnum || sec->sh_size == 0)
	  {
	    warn (_("Unable to locate .debug_abbrev section!\n"));
	    return 0;
	  }

	begin = ((unsigned char *)
		 get_data (NULL, file, sec->sh_offset, sec->sh_size,
			   _("debug_abbrev section data")));
	if (!begin)
	  return 0;

	process_abbrev_section (begin + compunit.cu_abbrev_offset,
				begin + sec->sh_size);

	VG_(free) (begin);
      }

      level = 0;
      while (tags < start)
	{
	  int bytes_read;
	  unsigned long abbrev_number;
	  abbrev_entry *entry;
	  abbrev_attr *attr;
          char is_relevant_entry; // PG

	  abbrev_number = read_leb128 (tags, & bytes_read, 0);
	  tags += bytes_read;

	  /* A null DIE marks the end of a list of children.  */
	  if (abbrev_number == 0)
	    {
	      --level;
	      continue;
	    }

	  /* Scan through the abbreviation list until we reach the
	     correct entry.  */
	  for (entry = first_abbrev;
	       entry && entry->entry != abbrev_number;
	       entry = entry->next)
	    continue;

	  if (entry == NULL)
	    {
	      warn (_("Unable to locate entry %lu in the abbreviation table\n"),
		    abbrev_number);
	      return 0;
	    }

          is_relevant_entry = tag_is_relevant_entry(entry->tag);
          if (is_relevant_entry)
            // PG - This is where all the action takes place
            //     store the info. as a dwarf_entry struct in dwarf_entry_array
            {
              unsigned long temp_ID = (unsigned long) (tags - section_begin - bytes_read);
              unsigned long temp_tag_name = entry->tag;


              // Fill the ID and tag_name fields:
              dwarf_entry_array[idx].ID = temp_ID;
              dwarf_entry_array[idx].tag_name = temp_tag_name;

	      // Fill the level field:
	      dwarf_entry_array[idx].level = level;

              // Initialize the entry_ptr based on tag_name
              initialize_dwarf_entry_ptr(&dwarf_entry_array[idx]);

              if(tag_is_compile_unit(temp_tag_name)) {
                cur_comp_unit = dwarf_entry_array[idx].entry_ptr;
                add_comp_unit(cur_comp_unit);
              }
              dwarf_entry_array[idx].comp_unit = cur_comp_unit;
              FJALAR_DPRINTF("dwarf_entry_array[%lu].comp_unit = %p\n", idx, dwarf_entry_array[idx].comp_unit);

              if (print_results)
                {
                  FJALAR_DPRINTF (_(" <%d><%lx>: Abbrev Number: %lu (%s)\n"),
                          level,
                          temp_ID,
                          abbrev_number,
                          get_TAG_name (temp_tag_name));
                }

              for (attr = entry->first_attr; attr; attr = attr->next)
                tags = read_and_display_attr (attr->attribute,
                                              attr->form,
                                              tags, cu_offset,
                                              compunit.cu_pointer_size,
                                              offset_size,
                                              compunit.cu_version,
                                              &dwarf_entry_array[idx],
                                              1); // DO harvest

	      /* FJALAR_DPRINTF("Index=%lu, ID=%lx, tag_name=%s, level=%d\n", */
	      /*   	     idx, */
	      /*   	     dwarf_entry_array[idx].ID, */
	      /*   	     get_TAG_name(dwarf_entry_array[idx].tag_name), */
	      /*   	     dwarf_entry_array[idx].level); */

              if (entry->children)
                ++level;

              idx++;
            }
          else
            {
              for (attr = entry->first_attr; attr; attr = attr->next)
                tags = read_and_display_attr (attr->attribute,
                                              attr->form,
                                              tags, cu_offset,
                                              compunit.cu_pointer_size,
                                              offset_size,
                                              compunit.cu_version,
                                              0,
                                              0); // DO NOT harvest

              if (entry->children)
                ++level;
            }

	}
    }

  free_debug_str ();
  free_debug_loc ();

  // PG - Now that all of the entries are in the array, finish initializing
  //     it by creating various links and filling in all dwarf_entry fields
  finish_dwarf_entry_array_init();

  //  print_dwarf_entry_array();
  //  FJALAR_DPRINTF ("\n");

  return 1;
}

static int
display_debug_aranges (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned char *end = start + section->sh_size;

  FJALAR_DPRINTF (_("The section %s contains:\n\n"), SECTION_NAME (section));

  while (start < end)
    {
      unsigned char *hdrptr;
      DWARF2_Internal_ARange arange;
      unsigned char *ranges;
      unsigned long length;
      unsigned long address;
      int excess;
      int offset_size;
      int initial_length_size;

      hdrptr = start;

      arange.ar_length = byte_get (hdrptr, 4);
      hdrptr += 4;

      if (arange.ar_length == 0xffffffff)
	{
	  arange.ar_length = byte_get (hdrptr, 8);
	  hdrptr += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
        {
	  offset_size = 4;
	  initial_length_size = 4;
	}

      arange.ar_version = byte_get (hdrptr, 2);
      hdrptr += 2;

      arange.ar_info_offset = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;

      arange.ar_pointer_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      arange.ar_segment_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      if (arange.ar_version != 2 && arange.ar_version != 3)
	{
	  warn (_("Only DWARF 2 and 3 aranges are currently supported.\n"));
	  break;
	}

      FJALAR_DPRINTF (_("  Length:                   %ld\n"), arange.ar_length);
      FJALAR_DPRINTF (_("  Version:                  %d\n"), arange.ar_version);
      FJALAR_DPRINTF (_("  Offset into .debug_info:  %lx\n"), arange.ar_info_offset);
      FJALAR_DPRINTF (_("  Pointer Size:             %d\n"), arange.ar_pointer_size);
      FJALAR_DPRINTF (_("  Segment Size:             %d\n"), arange.ar_segment_size);

      FJALAR_DPRINTF (_("\n    Address  Length\n"));

      ranges = hdrptr;

      /* Must pad to an alignment boundary that is twice the pointer size.  */
      excess = (hdrptr - start) % (2 * arange.ar_pointer_size);
      if (excess)
	ranges += (2 * arange.ar_pointer_size) - excess;

      for (;;)
	{
	  address = byte_get (ranges, arange.ar_pointer_size);

	  ranges += arange.ar_pointer_size;

	  length  = byte_get (ranges, arange.ar_pointer_size);

	  ranges += arange.ar_pointer_size;

	  /* A pair of zeros marks the end of the list.  */
	  if (address == 0 && length == 0)
	    break;

	  FJALAR_DPRINTF ("    %8.8lx %lu\n", address, length);
	}

      start += arange.ar_length + initial_length_size;
    }

  FJALAR_DPRINTF ("\n");

  return 1;
}

typedef struct Frame_Chunk
{
  struct Frame_Chunk *next;
  unsigned char *chunk_start;
  int ncols;
  /* DW_CFA_{undefined,same_value,offset,register,unreferenced}  */
  short int *col_type;
  int *col_offset;
  char *augmentation;
  unsigned int code_factor;
  int data_factor;
  unsigned long pc_begin;
  unsigned long pc_range;
  int cfa_reg;
  int cfa_offset;
  int ra;
  unsigned char fde_encoding;
  unsigned char cfa_exp;
}
Frame_Chunk;

/* A marker for a col_type that means this column was never referenced
   in the frame info.  */
#define DW_CFA_unreferenced (-1)

static void frame_need_space PARAMS ((Frame_Chunk *, int));
static void frame_display_row PARAMS ((Frame_Chunk *, int *, int *));
static int size_of_encoded_value PARAMS ((int));

static void
frame_need_space (fc, reg)
     Frame_Chunk *fc;
     int reg;
{
  int prev = fc->ncols;

  if (reg < fc->ncols)
    return;

  fc->ncols = reg + 1;
  fc->col_type = (short int *) xrealloc (fc->col_type,
					 fc->ncols * sizeof (short int));
  fc->col_offset = (int *) xrealloc (fc->col_offset,
				     fc->ncols * sizeof (int));

  while (prev < fc->ncols)
    {
      fc->col_type[prev] = DW_CFA_unreferenced;
      fc->col_offset[prev] = 0;
      prev++;
    }
}

static void
frame_display_row (fc, need_col_headers, max_regs)
     Frame_Chunk *fc;
     int *need_col_headers;
     int *max_regs;
{
  int r;
  char tmp[100];

  if (*max_regs < fc->ncols)
    *max_regs = fc->ncols;

  if (*need_col_headers)
    {
      *need_col_headers = 0;

      FJALAR_DPRINTF ("   LOC   CFA      ");

      for (r = 0; r < *max_regs; r++)
	if (fc->col_type[r] != DW_CFA_unreferenced)
	  {
	    if (r == fc->ra)
	      FJALAR_DPRINTF ("ra   ");
	    else
	      FJALAR_DPRINTF ("r%-4d", r);
	  }

      FJALAR_DPRINTF ("\n");
    }

  FJALAR_DPRINTF ("%08lx ", fc->pc_begin);
  if (fc->cfa_exp)
    VG_(strcpy) (tmp, "exp");
  else
    sprintf (tmp, "r%d%+d", fc->cfa_reg, fc->cfa_offset);
  FJALAR_DPRINTF ("%-8s ", tmp);

  for (r = 0; r < fc->ncols; r++)
    {
      if (fc->col_type[r] != DW_CFA_unreferenced)
	{
	  switch (fc->col_type[r])
	    {
	    case DW_CFA_undefined:
	      VG_(strcpy) (tmp, "u");
	      break;
	    case DW_CFA_same_value:
	      VG_(strcpy) (tmp, "s");
	      break;
	    case DW_CFA_offset:
	      sprintf (tmp, "c%+d", fc->col_offset[r]);
	      break;
	    case DW_CFA_register:
	      sprintf (tmp, "r%d", fc->col_offset[r]);
	      break;
	    case DW_CFA_expression:
	      VG_(strcpy) (tmp, "exp");
	      break;
	    default:
	      VG_(strcpy) (tmp, "n/a");
	      break;
	    }
	  FJALAR_DPRINTF ("%-5s", tmp);
	}
    }
  FJALAR_DPRINTF ("\n");
}

static int
size_of_encoded_value (encoding)
     int encoding;
{
  switch (encoding & 0x7)
    {
    default:	/* ??? */
    case 0:	return is_32bit_elf ? 4 : 8;
    case 2:	return 2;
    case 3:	return 4;
    case 4:	return 8;
    }
}

#define GET(N)	byte_get (start, N); start += N
#define LEB()	read_leb128 (start, & length_return, 0); start += length_return
#define SLEB()	read_leb128 (start, & length_return, 1); start += length_return

static int
display_debug_frames (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned char *end = start + section->sh_size;
  unsigned char *section_start = start;
  Frame_Chunk *chunks = 0;
  Frame_Chunk *remembered_state = 0;
  Frame_Chunk *rs;
  int is_eh = (VG_(strcmp) (SECTION_NAME (section), ".eh_frame") == 0);
  int length_return;
  int max_regs = 0;
  int addr_size = is_32bit_elf ? 4 : 8;

  FJALAR_DPRINTF (_("The section %s contains:\n"), SECTION_NAME (section));

  while (start < end)
    {
      unsigned char *saved_start;
      unsigned char *block_end;
      unsigned long length;
      unsigned long cie_id;
      Frame_Chunk *fc;
      Frame_Chunk *cie;
      int need_col_headers = 1;
      unsigned char *augmentation_data = NULL;
      unsigned long augmentation_data_len = 0;
      int encoded_ptr_size = addr_size;
      int offset_size;
      int initial_length_size;

      saved_start = start;
      length = byte_get (start, 4); start += 4;

      if (length == 0)
	{
	  FJALAR_DPRINTF ("\n%08lx ZERO terminator\n\n",
		    (unsigned long)(saved_start - section_start));
	  return 1;
	}

      if (length == 0xffffffff)
	{
	  length = byte_get (start, 8);
	  start += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      block_end = saved_start + length + initial_length_size;
      cie_id = byte_get (start, offset_size); start += offset_size;

      if (is_eh ? (cie_id == 0) : (cie_id == DW_CIE_ID))
	{
	  int version;

	  fc = (Frame_Chunk *) xmalloc (sizeof (Frame_Chunk));
	  VG_(memset) (fc, 0, sizeof (Frame_Chunk));

	  fc->next = chunks;
	  chunks = fc;
	  fc->chunk_start = saved_start;
	  fc->ncols = 0;
	  fc->col_type = (short int *) xmalloc (sizeof (short int));
	  fc->col_offset = (int *) xmalloc (sizeof (int));
	  frame_need_space (fc, max_regs-1);

	  version = *start++;

	  fc->augmentation = start;
	  start = VG_(strchr) (start, '\0') + 1;

	  if (fc->augmentation[0] == 'z')
	    {
	      fc->code_factor = LEB ();
	      fc->data_factor = SLEB ();
	      fc->ra = byte_get (start, 1); start += 1;
	      augmentation_data_len = LEB ();
	      augmentation_data = start;
	      start += augmentation_data_len;
	    }
	  else if (VG_(strcmp) (fc->augmentation, "eh") == 0)
	    {
	      start += addr_size;
	      fc->code_factor = LEB ();
	      fc->data_factor = SLEB ();
	      fc->ra = byte_get (start, 1); start += 1;
	    }
	  else
	    {
	      fc->code_factor = LEB ();
	      fc->data_factor = SLEB ();
	      fc->ra = byte_get (start, 1); start += 1;
	    }
	  cie = fc;

	  if (do_debug_frames_interp)
	    FJALAR_DPRINTF ("\n%08lx %08lx %08lx CIE \"%s\" cf=%d df=%d ra=%d\n",
		    (unsigned long)(saved_start - section_start), length, cie_id,
		    fc->augmentation, fc->code_factor, fc->data_factor,
		    fc->ra);
	  else
	    {
	      FJALAR_DPRINTF ("\n%08lx %08lx %08lx CIE\n",
		      (unsigned long)(saved_start - section_start), length, cie_id);
	      FJALAR_DPRINTF ("  Version:               %d\n", version);
	      FJALAR_DPRINTF ("  Augmentation:          \"%s\"\n", fc->augmentation);
	      FJALAR_DPRINTF ("  Code alignment factor: %u\n", fc->code_factor);
	      FJALAR_DPRINTF ("  Data alignment factor: %d\n", fc->data_factor);
	      FJALAR_DPRINTF ("  Return address column: %d\n", fc->ra);

	      if (augmentation_data_len)
		{
		  unsigned long i;
		  FJALAR_DPRINTF ("  Augmentation data:    ");
		  for (i = 0; i < augmentation_data_len; ++i)
		    FJALAR_DPRINTF (" %02x", augmentation_data[i]);
		  putchar ('\n');
		}
	      putchar ('\n');
	    }

	  if (augmentation_data_len)
	    {
	      unsigned char *p, *q;
	      p = fc->augmentation + 1;
	      q = augmentation_data;

	      while (1)
		{
		  if (*p == 'L')
		    q++;
		  else if (*p == 'P')
		    q += 1 + size_of_encoded_value (*q);
		  else if (*p == 'R')
		    fc->fde_encoding = *q++;
		  else
		    break;
		  p++;
		}

	      if (fc->fde_encoding)
		encoded_ptr_size = size_of_encoded_value (fc->fde_encoding);
	    }

	  frame_need_space (fc, fc->ra);
	}
      else
	{
          debug_frame* df;
	  unsigned char *look_for;
	  static Frame_Chunk fde_fc;

	  fc = & fde_fc;
	  VG_(memset) (fc, 0, sizeof (Frame_Chunk));

	  look_for = is_eh ? start - 4 - cie_id : section_start + cie_id;

	  for (cie = chunks; cie ; cie = cie->next)
	    if (cie->chunk_start == look_for)
	      break;

	  if (!cie)
	    {
	      warn ("Invalid CIE pointer %08lx in FDE at %08lx\n",
		    cie_id, saved_start);
	      start = block_end;
	      fc->ncols = 0;
	      fc->col_type = (short int *) xmalloc (sizeof (short int));
	      fc->col_offset = (int *) xmalloc (sizeof (int));
	      frame_need_space (fc, max_regs - 1);
	      cie = fc;
	      fc->augmentation = "";
	      fc->fde_encoding = 0;
	    }
	  else
	    {
	      fc->ncols = cie->ncols;
	      fc->col_type = (short int *) xmalloc (fc->ncols * sizeof (short int));
	      fc->col_offset = (int *) xmalloc (fc->ncols * sizeof (int));
	      VG_(memcpy) (fc->col_type, cie->col_type, fc->ncols * sizeof (short int));
	      VG_(memcpy) (fc->col_offset, cie->col_offset, fc->ncols * sizeof (int));
	      fc->augmentation = cie->augmentation;
	      fc->code_factor = cie->code_factor;
	      fc->data_factor = cie->data_factor;
	      fc->cfa_reg = cie->cfa_reg;
	      fc->cfa_offset = cie->cfa_offset;
	      fc->ra = cie->ra;
	      frame_need_space (fc, max_regs-1);
	      fc->fde_encoding = cie->fde_encoding;
	    }

	  if (fc->fde_encoding)
	    encoded_ptr_size = size_of_encoded_value (fc->fde_encoding);

	  fc->pc_begin = byte_get (start, encoded_ptr_size);
	  if ((fc->fde_encoding & 0x70) == DW_EH_PE_pcrel)
	    fc->pc_begin += section->sh_addr + (start - section_start);
	  start += encoded_ptr_size;
	  fc->pc_range = byte_get (start, encoded_ptr_size);
	  start += encoded_ptr_size;

	  if (cie->augmentation[0] == 'z')
	    {
	      augmentation_data_len = LEB ();
	      augmentation_data = start;
	      start += augmentation_data_len;
	    }
	  FJALAR_DPRINTF (")\n");


	  // RUDD - Harvesting Debug_Frame data
          df = VG_(calloc)("readelf.c: display_debug_frame", sizeof(debug_frame), 1);
	  df->begin = fc->pc_begin;
	  df->end = fc->pc_begin + fc->pc_range;
	  df->next = 0;
	  harvest_debug_frame_entry(df);



	  FJALAR_DPRINTF ("\n%08lx %08lx %08lx FDE cie=%08lx pc=%08lx..%08lx\n",
		  (unsigned long)(saved_start - section_start), length, cie_id,
		  (unsigned long)(cie->chunk_start - section_start),
		  fc->pc_begin, fc->pc_begin + fc->pc_range);
	  if (! do_debug_frames_interp && augmentation_data_len)
	    {
	      unsigned long i;
	      FJALAR_DPRINTF ("  Augmentation data:    ");
	      for (i = 0; i < augmentation_data_len; ++i)
	        FJALAR_DPRINTF (" %02x", augmentation_data[i]);
	      putchar ('\n');
	      putchar ('\n');
	    }
	}

      /* At this point, fc is the current chunk, cie (if any) is set, and we're
	 about to interpret instructions for the chunk.  */

      if (do_debug_frames_interp)
	{
	  /* Start by making a pass over the chunk, allocating storage
	     and taking note of what registers are used.  */
	  unsigned char *tmp = start;

	  while (start < block_end)
	    {
	      unsigned op, opa;
	      unsigned long reg, temp;

	      op = *start++;
	      opa = op & 0x3f;
	      if (op & 0xc0)
		op &= 0xc0;

	      /* Warning: if you add any more cases to this switch, be
	         sure to add them to the corresponding switch below.  */
	      switch (op)
		{
		case DW_CFA_advance_loc:
		  break;
		case DW_CFA_offset:
		  LEB ();
		  frame_need_space (fc, opa);
		  fc->col_type[opa] = DW_CFA_undefined;
		  break;
		case DW_CFA_restore:
		  frame_need_space (fc, opa);
		  fc->col_type[opa] = DW_CFA_undefined;
		  break;
		case DW_CFA_set_loc:
		  start += encoded_ptr_size;
		  break;
		case DW_CFA_advance_loc1:
		  start += 1;
		  break;
		case DW_CFA_advance_loc2:
		  start += 2;
		  break;
		case DW_CFA_advance_loc4:
		  start += 4;
		  break;
		case DW_CFA_offset_extended:
		  reg = LEB (); LEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_restore_extended:
		  reg = LEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_undefined:
		  reg = LEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_same_value:
		  reg = LEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_register:
		  reg = LEB (); LEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_def_cfa:
		  LEB (); LEB ();
		  break;
		case DW_CFA_def_cfa_register:
		  LEB ();
		  break;
		case DW_CFA_def_cfa_offset:
		  LEB ();
		  break;
		case DW_CFA_def_cfa_expression:
		  temp = LEB ();
		  start += temp;
		  break;
		case DW_CFA_expression:
		  reg = LEB ();
		  temp = LEB ();
		  start += temp;
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_offset_extended_sf:
		  reg = LEB (); SLEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_def_cfa_sf:
		  LEB (); SLEB ();
		  break;
		case DW_CFA_def_cfa_offset_sf:
		  SLEB ();
		  break;
		case DW_CFA_MIPS_advance_loc8:
		  start += 8;
		  break;
		case DW_CFA_GNU_args_size:
		  LEB ();
		  break;
		case DW_CFA_GNU_negative_offset_extended:
		  reg = LEB (); LEB ();
		  frame_need_space (fc, reg);
		  fc->col_type[reg] = DW_CFA_undefined;

		default:
		  break;
		}
	    }
	  start = tmp;
	}

      /* Now we know what registers are used, make a second pass over
         the chunk, this time actually printing out the info.  */

      while (start < block_end)
	{
	  unsigned op, opa;
	  unsigned long ul, reg, roffs;
	  long l, ofs;
	  bfd_vma vma;

	  op = *start++;
	  opa = op & 0x3f;
	  if (op & 0xc0)
	    op &= 0xc0;

	  /* Warning: if you add any more cases to this switch, be
	     sure to add them to the corresponding switch above.  */
	  switch (op)
	    {
	    case DW_CFA_advance_loc:
	      if (do_debug_frames_interp)
		frame_display_row (fc, &need_col_headers, &max_regs);
	      else
	 FJALAR_DPRINTF ("  DW_CFA_advance_loc: %d to %08lx\n",
			opa * fc->code_factor,
			fc->pc_begin + opa * fc->code_factor);
	      fc->pc_begin += opa * fc->code_factor;
	      break;

	    case DW_CFA_offset:
	      roffs = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_offset: r%d at cfa%+ld\n",
			opa, roffs * fc->data_factor);
	      fc->col_type[opa] = DW_CFA_offset;
	      fc->col_offset[opa] = roffs * fc->data_factor;
	      break;

	    case DW_CFA_restore:
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_restore: r%d\n", opa);
	      fc->col_type[opa] = cie->col_type[opa];
	      fc->col_offset[opa] = cie->col_offset[opa];
	      break;

	    case DW_CFA_set_loc:
	      vma = byte_get (start, encoded_ptr_size);
	      if ((fc->fde_encoding & 0x70) == DW_EH_PE_pcrel)
		vma += section->sh_addr + (start - section_start);
	      start += encoded_ptr_size;
	      if (do_debug_frames_interp)
		frame_display_row (fc, &need_col_headers, &max_regs);
	      else
	 FJALAR_DPRINTF ("  DW_CFA_set_loc: %08lx\n", (unsigned long)vma);
	      fc->pc_begin = vma;
	      break;

	    case DW_CFA_advance_loc1:
	      ofs = byte_get (start, 1); start += 1;
	      if (do_debug_frames_interp)
		frame_display_row (fc, &need_col_headers, &max_regs);
	      else
	 FJALAR_DPRINTF ("  DW_CFA_advance_loc1: %ld to %08lx\n",
			ofs * fc->code_factor,
			fc->pc_begin + ofs * fc->code_factor);
	      fc->pc_begin += ofs * fc->code_factor;
	      break;

	    case DW_CFA_advance_loc2:
	      ofs = byte_get (start, 2); start += 2;
	      if (do_debug_frames_interp)
		frame_display_row (fc, &need_col_headers, &max_regs);
	      else
	 FJALAR_DPRINTF ("  DW_CFA_advance_loc2: %ld to %08lx\n",
			ofs * fc->code_factor,
			fc->pc_begin + ofs * fc->code_factor);
	      fc->pc_begin += ofs * fc->code_factor;
	      break;

	    case DW_CFA_advance_loc4:
	      ofs = byte_get (start, 4); start += 4;
	      if (do_debug_frames_interp)
		frame_display_row (fc, &need_col_headers, &max_regs);
	      else
	 FJALAR_DPRINTF ("  DW_CFA_advance_loc4: %ld to %08lx\n",
			ofs * fc->code_factor,
			fc->pc_begin + ofs * fc->code_factor);
	      fc->pc_begin += ofs * fc->code_factor;
	      break;

	    case DW_CFA_offset_extended:
	      reg = LEB ();
	      roffs = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_offset_extended: r%ld at cfa%+ld\n",
			reg, roffs * fc->data_factor);
	      fc->col_type[reg] = DW_CFA_offset;
	      fc->col_offset[reg] = roffs * fc->data_factor;
	      break;

	    case DW_CFA_restore_extended:
	      reg = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_restore_extended: r%ld\n", reg);
	      fc->col_type[reg] = cie->col_type[reg];
	      fc->col_offset[reg] = cie->col_offset[reg];
	      break;

	    case DW_CFA_undefined:
	      reg = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_undefined: r%ld\n", reg);
	      fc->col_type[reg] = DW_CFA_undefined;
	      fc->col_offset[reg] = 0;
	      break;

	    case DW_CFA_same_value:
	      reg = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_same_value: r%ld\n", reg);
	      fc->col_type[reg] = DW_CFA_same_value;
	      fc->col_offset[reg] = 0;
	      break;

	    case DW_CFA_register:
	      reg = LEB ();
	      roffs = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_register: r%ld\n", reg);
	      fc->col_type[reg] = DW_CFA_register;
	      fc->col_offset[reg] = roffs;
	      break;

	    case DW_CFA_remember_state:
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_remember_state\n");
	      rs = (Frame_Chunk *) xmalloc (sizeof (Frame_Chunk));
	      rs->ncols = fc->ncols;
	      rs->col_type = (short int *) xmalloc (rs->ncols * sizeof (short int));
	      rs->col_offset = (int *) xmalloc (rs->ncols * sizeof (int));
	      VG_(memcpy) (rs->col_type, fc->col_type, rs->ncols);
	      VG_(memcpy) (rs->col_offset, fc->col_offset, rs->ncols * sizeof (int));
	      rs->next = remembered_state;
	      remembered_state = rs;
	      break;

	    case DW_CFA_restore_state:
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_restore_state\n");
	      rs = remembered_state;
	      remembered_state = rs->next;
	      frame_need_space (fc, rs->ncols-1);
	      VG_(memcpy) (fc->col_type, rs->col_type, rs->ncols);
	      VG_(memcpy) (fc->col_offset, rs->col_offset, rs->ncols * sizeof (int));
	      VG_(free) (rs->col_type);
	      VG_(free) (rs->col_offset);
	      VG_(free) (rs);
	      break;

	    case DW_CFA_def_cfa:
	      fc->cfa_reg = LEB ();
	      fc->cfa_offset = LEB ();
	      fc->cfa_exp = 0;
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_def_cfa: r%d ofs %d\n",
			fc->cfa_reg, fc->cfa_offset);
	      break;

	    case DW_CFA_def_cfa_register:
	      fc->cfa_reg = LEB ();
	      fc->cfa_exp = 0;
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_def_cfa_reg: r%d\n", fc->cfa_reg);
	      break;

	    case DW_CFA_def_cfa_offset:
	      fc->cfa_offset = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_def_cfa_offset: %d\n", fc->cfa_offset);
	      break;

	    case DW_CFA_nop:
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_nop\n");
	      break;

	    case DW_CFA_def_cfa_expression:
	      ul = LEB ();
	      if (! do_debug_frames_interp)
		{
		  FJALAR_DPRINTF ("  DW_CFA_def_cfa_expression (");
		  decode_location_expression (start, addr_size, ul, 1, 0, 0 );
		  FJALAR_DPRINTF (")\n");
		}
	      fc->cfa_exp = 1;
	      start += ul;
	      break;

	    case DW_CFA_expression:
	      reg = LEB ();
	      ul = LEB ();
	      if (! do_debug_frames_interp)
		{
		  FJALAR_DPRINTF ("  DW_CFA_expression: r%ld (", reg);
		  decode_location_expression (start, addr_size, ul, 1, 0, 0);
		  FJALAR_DPRINTF (")\n");
		}
	      fc->col_type[reg] = DW_CFA_expression;
	      start += ul;
	      break;

	    case DW_CFA_offset_extended_sf:
	      reg = LEB ();
	      l = SLEB ();
	      frame_need_space (fc, reg);
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_offset_extended_sf: r%ld at cfa%+ld\n",
			reg, l * fc->data_factor);
	      fc->col_type[reg] = DW_CFA_offset;
	      fc->col_offset[reg] = l * fc->data_factor;
	      break;

	    case DW_CFA_def_cfa_sf:
	      fc->cfa_reg = LEB ();
	      fc->cfa_offset = SLEB ();
	      fc->cfa_exp = 0;
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_def_cfa_sf: r%d ofs %d\n",
			fc->cfa_reg, fc->cfa_offset);
	      break;

	    case DW_CFA_def_cfa_offset_sf:
	      fc->cfa_offset = SLEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_def_cfa_offset_sf: %d\n", fc->cfa_offset);
	      break;

	    case DW_CFA_MIPS_advance_loc8:
	      ofs = byte_get (start, 8); start += 8;
	      if (do_debug_frames_interp)
		frame_display_row (fc, &need_col_headers, &max_regs);
	      else
	 FJALAR_DPRINTF ("  DW_CFA_MIPS_advance_loc8: %ld to %08lx\n",
			ofs * fc->code_factor,
			fc->pc_begin + ofs * fc->code_factor);
	      fc->pc_begin += ofs * fc->code_factor;
	      break;

	    case DW_CFA_GNU_window_save:
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_GNU_window_save\n");
	      break;

	    case DW_CFA_GNU_args_size:
	      ul = LEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_GNU_args_size: %ld\n", ul);
	      break;

	    case DW_CFA_GNU_negative_offset_extended:
	      reg = LEB ();
	      l = - LEB ();
	      frame_need_space (fc, reg);
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_GNU_negative_offset_extended: r%ld at cfa%+ld\n",
			reg, l * fc->data_factor);
	      fc->col_type[reg] = DW_CFA_offset;
	      fc->col_offset[reg] = l * fc->data_factor;
	      break;

	    default:
	      fprintf (stderr, "unsupported or unknown DW_CFA_%d\n", op);
	      start = block_end;
	    }
	}

      if (do_debug_frames_interp)
	frame_display_row (fc, &need_col_headers, &max_regs);

      start = block_end;
    }

  FJALAR_DPRINTF ("\n");

  return 1;
}

#undef GET
#undef LEB
#undef SLEB

static int
display_debug_not_supported (section, start, file)
     Elf_Internal_Shdr *section;
     unsigned char *start ATTRIBUTE_UNUSED;
     FILE *file ATTRIBUTE_UNUSED;
{
  FJALAR_DPRINTF (_("Displaying the debug contents of section %s is not yet supported.\n"),
	    SECTION_NAME (section));

  return 1;
}

/* Pre-scan the .debug_info section to record the size of address.
   When dumping the .debug_line, we use that size information, assuming
   that all compilation units have the same address size.  */
static int
prescan_debug_info (section, start, file)
     Elf_Internal_Shdr *section ATTRIBUTE_UNUSED;
     unsigned char *start;
     FILE *file ATTRIBUTE_UNUSED;
{
  unsigned long length;

  /* Read the first 4 bytes.  For a 32-bit DWARF section, this will
     be the length.  For a 64-bit DWARF section, it'll be the escape
     code 0xffffffff followed by an 8 byte length.  For the purposes
     of this prescan, we don't care about the actual length, but the
     presence of the escape bytes does affect the location of the byte
     which describes the address size.  */
  length = byte_get (start, 4);

  if (length == 0xffffffff)
    {
      /* For 64-bit DWARF, the 1-byte address_size field is 22 bytes
         from the start of the section.  This is computed as follows:

	    unit_length:         12 bytes
	    version:              2 bytes
	    debug_abbrev_offset:  8 bytes
	    -----------------------------
	    Total:               22 bytes  */

      debug_line_pointer_size = byte_get (start + 22, 1);
    }
  else
    {
      /* For 32-bit DWARF, the 1-byte address_size field is 10 bytes from
         the start of the section:
	    unit_length:          4 bytes
	    version:              2 bytes
	    debug_abbrev_offset:  4 bytes
	    -----------------------------
	    Total:               10 bytes  */

      debug_line_pointer_size = byte_get (start + 10, 1);
    }
  return 0;
}

  /* A structure containing the name of a debug section and a pointer
     to a function that can decode it.  The third field is a prescan
     function to be run over the section before displaying any of the
     sections.  */
struct
{
  const char *const name;
  int (*display) PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
  int (*prescan) PARAMS ((Elf_Internal_Shdr *, unsigned char *, FILE *));
}
debug_displays[] =
{
  { ".debug_abbrev",		display_debug_abbrev, NULL },
  { ".debug_aranges",		display_debug_aranges, NULL },
  { ".debug_frame",		display_debug_frames, NULL },
  { ".debug_info",		display_debug_info, prescan_debug_info },
  { ".debug_line",		display_debug_lines, NULL },
  { ".debug_pubnames",		display_debug_pubnames, NULL },
  { ".eh_frame",		display_debug_frames, NULL },
  { ".debug_macinfo",		display_debug_macinfo, NULL },
  { ".debug_str",		display_debug_str, NULL },
  { ".debug_loc",		display_debug_loc, NULL },
  { ".debug_pubtypes",		display_debug_not_supported, NULL },
  { ".debug_ranges",		display_debug_not_supported, NULL },
  { ".debug_static_func",	display_debug_not_supported, NULL },
  { ".debug_static_vars",	display_debug_not_supported, NULL },
  { ".debug_types",		display_debug_not_supported, NULL },
  { ".debug_weaknames",		display_debug_not_supported, NULL }
};

static int
display_debug_section (section, file)
     Elf_Internal_Shdr *section;
     FILE *file;
{
  char *name = SECTION_NAME (section);
  bfd_size_type length;
  unsigned char *start;
  int i;

  length = section->sh_size;
  if (length == 0)
    {
      FJALAR_DPRINTF (_("\nSection '%s' has no debugging data.\n"), name);
      return 0;
    }

  start = (unsigned char *) get_data (NULL, file, section->sh_offset, length,
				      _("debug section data"));
  if (!start)
    return 0;

  /* See if we know how to display the contents of this section.  */
  if (VG_(strncmp) (name, ".gnu.linkonce.wi.", 17) == 0)
    name = ".debug_info";

  for (i = NUM_ELEM (debug_displays); i--;)
    if (VG_(strcmp) (debug_displays[i].name, name) == 0)
      {
	debug_displays[i].display (section, start, file);
	break;
      }

  if (i == -1)
    FJALAR_DPRINTF (_("Unrecognized debug section: %s\n"), name);

  VG_(free) (start);

  /* If we loaded in the abbrev section at some point,
     we must release it here.  */
  free_abbrevs ();

  return 1;
}

static int
process_section_contents (file)
     FILE *file;
{
  Elf_Internal_Shdr *section;
  unsigned int i;

  if (! do_dump)
    return 1;

  //  FJALAR_DPRINTF("process_section_contents() - before 1st for loop\n");

  /* Pre-scan the debug sections to find some debug information not
     present in some of them.  For the .debug_line, we must find out the
     size of address (specified in .debug_info and .debug_aranges).  */
  for (i = 0, section = section_headers;
       i < elf_header.e_shnum && i < num_dump_sects;
       i++, section++)
    {
      char *name = SECTION_NAME (section);
      int j;

      if (section->sh_size == 0)
	continue;

      /* See if there is some pre-scan operation for this section.  */
      for (j = NUM_ELEM (debug_displays); j--;)
	if (VG_(strcmp) (debug_displays[j].name, name) == 0)
	  {
	    if (debug_displays[j].prescan != NULL)
	      {
		bfd_size_type length;
		unsigned char *start;

		length = section->sh_size;
		start = ((unsigned char *)
			 get_data (NULL, file, section->sh_offset, length,
				   _("debug section data")));
		if (!start)
		  return 0;

		debug_displays[j].prescan (section, start, file);
		VG_(free) (start);
	      }

	    break;
	  }
    }

  //  FJALAR_DPRINTF("process_section_contents() - before 2nd for loop\n");

  for (i = 0, section = section_headers;
       i < elf_header.e_shnum && i < num_dump_sects;
       i++, section++)
    {
#ifdef SUPPORT_DISASSEMBLY
      if (dump_sects[i] & DISASS_DUMP)
	disassemble_section (section, file);
#endif
      if (dump_sects[i] & HEX_DUMP)
        {
          dump_section (section, file);
        }

      if (dump_sects[i] & DEBUG_DUMP)
        {
          display_debug_section (section, file);
        }
    }

  //  FJALAR_DPRINTF("process_section_contents() - after 2nd for loop\n");

  if (i < num_dump_sects)
    {
      warn (_("Some sections were not dumped because they do not exist!\n"));
    }

  return 1;
}

static int
process_mips_specific (file)
     FILE *file;
{
  (void)file; /* Quiet unused parameter warning */
  /* We have a lot of special sections.  Thanks SGI!  */
  if (dynamic_segment == NULL)
    /* No information available.  */
    return 0;
  return 1;
}

static int
process_gnu_liblist (file)
     FILE *file;
{
  (void)file; /* Quiet unused parameter warning */
  return 1;
}

static const char *
get_note_type (e_type)
     unsigned e_type;
{
  static char buff[64];

  switch (e_type)
    {
    case NT_PRSTATUS:	return _("NT_PRSTATUS (prstatus structure)");
    case NT_FPREGSET:	return _("NT_FPREGSET (floating point registers)");
    case NT_PRPSINFO:	return _("NT_PRPSINFO (prpsinfo structure)");
    case NT_TASKSTRUCT:	return _("NT_TASKSTRUCT (task structure)");
    case NT_PRXFPREG:	return _("NT_PRXFPREG (user_xfpregs structure)");
    case NT_PSTATUS:	return _("NT_PSTATUS (pstatus structure)");
    case NT_FPREGS:	return _("NT_FPREGS (floating point registers)");
    case NT_PSINFO:	return _("NT_PSINFO (psinfo structure)");
    case NT_LWPSTATUS:	return _("NT_LWPSTATUS (lwpstatus_t structure)");
    case NT_LWPSINFO:	return _("NT_LWPSINFO (lwpsinfo_t structure)");
    case NT_WIN32PSTATUS: return _("NT_WIN32PSTATUS (win32_pstatus structure)");
    default:
      sprintf (buff, _("Unknown note type: (0x%08x)"), e_type);
      return buff;
    }
}

static const char *
get_netbsd_elfcore_note_type (e_type)
     unsigned e_type;
{
  static char buff[64];

  if (e_type == NT_NETBSDCORE_PROCINFO)
    {
      /* NetBSD core "procinfo" structure.  */
      return _("NetBSD procinfo structure");
    }

  /* As of Jan 2002 there are no other machine-independent notes
     defined for NetBSD core files.  If the note type is less
     than the start of the machine-dependent note types, we don't
     understand it.  */

  if (e_type < NT_NETBSDCORE_FIRSTMACH)
    {
      sprintf (buff, _("Unknown note type: (0x%08x)"), e_type);
      return buff;
    }

  switch (elf_header.e_machine)
    {
    /* On the Alpha, SPARC (32-bit and 64-bit), PT_GETREGS == mach+0
       and PT_GETFPREGS == mach+2.  */

    case EM_OLD_ALPHA:
    case EM_ALPHA:
    case EM_SPARC:
    case EM_SPARC32PLUS:
    case EM_SPARCV9:
      switch (e_type)
	{
	case NT_NETBSDCORE_FIRSTMACH+0:
	  return _("PT_GETREGS (reg structure)");
	case NT_NETBSDCORE_FIRSTMACH+2:
	  return _("PT_GETFPREGS (fpreg structure)");
	default:
	  break;
	}
      break;

    /* On all other arch's, PT_GETREGS == mach+1 and
       PT_GETFPREGS == mach+3.  */
    default:
      switch (e_type)
	{
	case NT_NETBSDCORE_FIRSTMACH+1:
	  return _("PT_GETREGS (reg structure)");
	case NT_NETBSDCORE_FIRSTMACH+3:
	  return _("PT_GETFPREGS (fpreg structure)");
	default:
	  break;
	}
    }

  sprintf (buff, _("PT_FIRSTMACH+%d"), e_type - NT_NETBSDCORE_FIRSTMACH);
  return buff;
}

/* Note that by the ELF standard, the name field is already null byte
   terminated, and namesz includes the terminating null byte.
   I.E. the value of namesz for the name "FSF" is 4.

   If the value of namesz is zero, there is no name present.  */
static int
process_note (pnote)
     Elf_Internal_Note *pnote;
{
  const char *nt;

  if (pnote->namesz == 0)
    {
      /* If there is no note name, then use the default set of
	 note type strings.  */
      nt = get_note_type (pnote->type);
    }
  else if (VG_(strncmp) (pnote->namedata, "NetBSD-CORE", 11) == 0)
    {
      /* NetBSD-specific core file notes.  */
      nt = get_netbsd_elfcore_note_type (pnote->type);
    }
  else
    {
      /* Don't recognize this note name; just use the default set of
	 note type strings.  */
      nt = get_note_type (pnote->type);
    }

  FJALAR_DPRINTF ("  %s\t\t0x%08lx\t%s\n",
	  pnote->namesz ? pnote->namedata : "(NONE)",
	  pnote->descsz, nt);
  return 1;
}


static int
process_corefile_note_segment (file, offset, length)
     FILE *file;
     bfd_vma offset;
     bfd_vma length;
{
  Elf_External_Note *pnotes;
  Elf_External_Note *external;
  int res = 1;

  if (length <= 0)
    return 0;

  pnotes = (Elf_External_Note *) get_data (NULL, file, offset, length,
					   _("notes"));
  if (!pnotes)
    return 0;

  external = pnotes;

  FJALAR_DPRINTF (_("\nNotes at offset 0x%08lx with length 0x%08lx:\n"),
	  (unsigned long) offset, (unsigned long) length);
  FJALAR_DPRINTF (_("  Owner\t\tData size\tDescription\n"));

  while (external < (Elf_External_Note *)((char *) pnotes + length))
    {
      Elf_External_Note *next;
      Elf_Internal_Note inote;
      char *temp = NULL;

      inote.type     = BYTE_GET (external->type);
      inote.namesz   = BYTE_GET (external->namesz);
      inote.namedata = external->name;
      inote.descsz   = BYTE_GET (external->descsz);
      inote.descdata = inote.namedata + align_power (inote.namesz, 2);
      inote.descpos  = offset + (inote.descdata - (char *) pnotes);

      next = (Elf_External_Note *)(inote.descdata + align_power (inote.descsz, 2));

      if (((char *) next) > (((char *) pnotes) + length))
	{
	  warn (_("corrupt note found at offset %x into core notes\n"),
		((char *) external) - ((char *) pnotes));
	  warn (_(" type: %x, namesize: %08lx, descsize: %08lx\n"),
		inote.type, inote.namesz, inote.descsz);
	  break;
	}

      external = next;

      /* Verify that name is null terminated.  It appears that at least
	 one version of Linux (RedHat 6.0) generates corefiles that don't
	 comply with the ELF spec by failing to include the null byte in
	 namesz.  */
      if (inote.namedata[inote.namesz] != '\0')
	{
	  temp = VG_(malloc) ("readelf.c: proc_core", inote.namesz + 1);

	  if (temp == NULL)
	    {
	      error (_("Out of memory\n"));
	      res = 0;
	      break;
	    }

	  VG_(strncpy) (temp, inote.namedata, inote.namesz);
	  temp[inote.namesz] = 0;

	  /* warn (_("'%s' NOTE name not properly null terminated\n"), temp);  */
	  inote.namedata = temp;
	}

      res &= process_note (& inote);

      if (temp != NULL)
	{
	  VG_(free) (temp);
	  temp = NULL;
	}
    }

  VG_(free) (pnotes);

  return res;
}

static int
process_corefile_note_segments (file)
     FILE *file;
{
  Elf_Internal_Phdr *program_headers;
  Elf_Internal_Phdr *segment;
  unsigned int i;
  int res = 1;

  program_headers = (Elf_Internal_Phdr *) VG_(malloc)
    ("readelf.c: proc_corefile_note_seg", elf_header.e_phnum * sizeof (Elf_Internal_Phdr));

  if (program_headers == NULL)
    {
      error (_("Out of memory\n"));
      return 0;
    }

  if (is_32bit_elf)
    i = get_32bit_program_headers (file, program_headers);
  else
    i = get_64bit_program_headers (file, program_headers);

  if (i == 0)
    {
      VG_(free) (program_headers);
      return 0;
    }

  for (i = 0, segment = program_headers;
       i < elf_header.e_phnum;
       i++, segment++)
    {
      if (segment->p_type == PT_NOTE)
	res &= process_corefile_note_segment (file,
					      (bfd_vma) segment->p_offset,
					      (bfd_vma) segment->p_filesz);
    }

  VG_(free) (program_headers);

  return res;
}

static int
process_corefile_contents (file)
     FILE *file;
{
  /* If we have not been asked to display the notes then do nothing.  */
  if (! do_notes)
    return 1;

  /* If file is not a core file then exit.  */
  if (elf_header.e_type != ET_CORE)
    return 1;

  /* No program headers means no NOTE segment.  */
  if (elf_header.e_phnum == 0)
    {
      FJALAR_DPRINTF (_("No note segments present in the core file.\n"));
      return 1;
   }

  return process_corefile_note_segments (file);
}

static int
process_arch_specific (file)
     FILE *file;
{
  if (! do_arch)
    return 1;

  switch (elf_header.e_machine)
    {
    case EM_MIPS:
    case EM_MIPS_RS3_LE:
      return process_mips_specific (file);
      break;
    default:
      break;
    }
  return 1;
}

static int
get_file_header (file)
     FILE *file;
{
  /* Read in the identity array.  */
  if (fread (elf_header.e_ident, EI_NIDENT, 1, file) != 1)
    return 0;

  /* Determine how to read the rest of the header.  */
  switch (elf_header.e_ident[EI_DATA])
    {
    default: /* fall through */
    case ELFDATANONE: /* fall through */
    case ELFDATA2LSB:
      byte_get = byte_get_little_endian;
      byte_put = byte_put_little_endian;
      break;
    case ELFDATA2MSB:
      byte_get = byte_get_big_endian;
      byte_put = byte_put_big_endian;
      break;
    }

  /* For now we only support 32 bit and 64 bit ELF files.  */
  is_32bit_elf = (elf_header.e_ident[EI_CLASS] != ELFCLASS64);

  /* Read in the rest of the header.  */
  if (is_32bit_elf)
    {
      Elf32_External_Ehdr ehdr32;

      if (fread (ehdr32.e_type, sizeof (ehdr32) - EI_NIDENT, 1, file) != 1)
	return 0;

      elf_header.e_type      = BYTE_GET (ehdr32.e_type);
      elf_header.e_machine   = BYTE_GET (ehdr32.e_machine);
      elf_header.e_version   = BYTE_GET (ehdr32.e_version);
      elf_header.e_entry     = BYTE_GET (ehdr32.e_entry);
      elf_header.e_phoff     = BYTE_GET (ehdr32.e_phoff);
      elf_header.e_shoff     = BYTE_GET (ehdr32.e_shoff);
      elf_header.e_flags     = BYTE_GET (ehdr32.e_flags);
      elf_header.e_ehsize    = BYTE_GET (ehdr32.e_ehsize);
      elf_header.e_phentsize = BYTE_GET (ehdr32.e_phentsize);
      elf_header.e_phnum     = BYTE_GET (ehdr32.e_phnum);
      elf_header.e_shentsize = BYTE_GET (ehdr32.e_shentsize);
      elf_header.e_shnum     = BYTE_GET (ehdr32.e_shnum);
      elf_header.e_shstrndx  = BYTE_GET (ehdr32.e_shstrndx);
    }
  else
    {
      Elf64_External_Ehdr ehdr64;

      /* If we have been compiled with sizeof (bfd_vma) == 4, then
	 we will not be able to cope with the 64bit data found in
	 64 ELF files.  Detect this now and abort before we start
	 overwritting things.  */
      if (sizeof (bfd_vma) < 8)
	{
	  error (_("This instance of readelf has been built without support for a\n\
64 bit data type and so it cannot read 64 bit ELF files.\n"));
	  return 0;
	}

      if (fread (ehdr64.e_type, sizeof (ehdr64) - EI_NIDENT, 1, file) != 1)
	return 0;

      elf_header.e_type      = BYTE_GET (ehdr64.e_type);
      elf_header.e_machine   = BYTE_GET (ehdr64.e_machine);
      elf_header.e_version   = BYTE_GET (ehdr64.e_version);
      elf_header.e_entry     = BYTE_GET8 (ehdr64.e_entry);
      elf_header.e_phoff     = BYTE_GET8 (ehdr64.e_phoff);
      elf_header.e_shoff     = BYTE_GET8 (ehdr64.e_shoff);
      elf_header.e_flags     = BYTE_GET (ehdr64.e_flags);
      elf_header.e_ehsize    = BYTE_GET (ehdr64.e_ehsize);
      elf_header.e_phentsize = BYTE_GET (ehdr64.e_phentsize);
      elf_header.e_phnum     = BYTE_GET (ehdr64.e_phnum);
      elf_header.e_shentsize = BYTE_GET (ehdr64.e_shentsize);
      elf_header.e_shnum     = BYTE_GET (ehdr64.e_shnum);
      elf_header.e_shstrndx  = BYTE_GET (ehdr64.e_shstrndx);
    }

  if (elf_header.e_shoff)
    {
      /* There may be some extensions in the first section header.  Don't
	 bomb if we can't read it.  */
      if (is_32bit_elf)
	get_32bit_section_headers (file, 1);
      else
	get_64bit_section_headers (file, 1);
    }

  return 1;
}

static int
process_file (file_name)
     char *file_name;
{
  FILE *file;
  unsigned int i;

  file = fopen (file_name, "rb");
  if (file == NULL)
    {
      error (_("Input file %s not found.\n"), file_name);
      return 1;
    }

  if (! get_file_header (file))
    {
      error (_("%s: Failed to read file header\n"), file_name);
      fclose (file);
      return 1;
    }

  /* Initialise per file variables.  */
  for (i = NUM_ELEM (version_info); i--;)
    version_info[i] = 0;

  for (i = NUM_ELEM (dynamic_info); i--;)
    dynamic_info[i] = 0;

  /* Process the file.  */
#ifdef SHOW_DEBUG
  if (show_name)
    FJALAR_DPRINTF (_("\nFile: %s\n"), file_name);
#endif

  //printf("before process_file_header()\n"); // PG

  if (! process_file_header ())
    {
      //  FJALAR_DPRINTF("failed process_file_header()\n"); // PG
      fclose (file);
      return 1;
    }

  //    FJALAR_DPRINTF("before process_section_headers()\n"); // PG

  if (! process_section_headers (file))
    {
      //  FJALAR_DPRINTF("failed process_section_headers()\n"); // PG
      /* Without loaded section headers we
	 cannot process lots of things.  */
      do_unwind = do_version = do_dump = do_arch = 0;

      if (! do_using_dynamic)
	do_syms = do_reloc = 0;
    }

  //    FJALAR_DPRINTF("before process_program_headers()\n"); // PG

  if (process_program_headers (file))
    process_dynamic_segment (file);
  //    FJALAR_DPRINTF("before process_relocs()\n"); // PG
  process_relocs (file);
  //  FJALAR_DPRINTF("before process_unwind()\n"); // PG
  process_unwind (file);
  //    FJALAR_DPRINTF("before process_symbol_table()\n"); // PG
  process_symbol_table (file);
  //    FJALAR_DPRINTF("before process_syminfo()\n"); // PG
  process_syminfo (file);
  //   FJALAR_DPRINTF("before process_version_sections()\n"); // PG
  process_version_sections (file);
  //    FJALAR_DPRINTF("before process_section_contents()\n"); // PG
  process_section_contents (file);
  //    FJALAR_DPRINTF("before process_corefile_contents()\n"); // PG
  process_corefile_contents (file);
  //    FJALAR_DPRINTF("before process_gnu_liblist()\n"); // PG
  process_gnu_liblist (file);
  //    FJALAR_DPRINTF("before process_arch_specific()\n"); // PG
  process_arch_specific (file);

  fclose (file);

  if (section_headers)
    {
      VG_(free) (section_headers);
      section_headers = NULL;
    }

  if (string_table)
    {
      VG_(free) (string_table);
      string_table = NULL;
      string_table_length = 0;
    }

  if (dynamic_strings)
    {
      VG_(free) (dynamic_strings);
      dynamic_strings = NULL;
    }

  if (dynamic_symbols)
    {
      VG_(free) (dynamic_symbols);
      dynamic_symbols = NULL;
      num_dynamic_syms = 0;
    }

  if (dynamic_syminfo)
    {
      VG_(free) (dynamic_syminfo);
      dynamic_syminfo = NULL;
    }

  return 0;
}

#ifdef SUPPORT_DISASSEMBLY
/* Needed by the i386 disassembler.  For extra credit, someone could
   fix this so that we insert symbolic addresses here, esp for GOT/PLT
   symbols.  */

void
print_address (unsigned int addr, FILE *outfile)
{
  fprintf (outfile,"0x%8.8x", addr);
}

/* Needed by the i386 disassembler.  */
void
db_task_printsym (unsigned int addr)
{
  print_address (addr, stderr);
}
#endif

// PG insert a fake main which is a hacked copy that can be called
// with a filename argument

int process_elf_binary_data(char* filename)
{

  int err;
  char *cmdline_dump_sects = NULL;
  // FJALAR_DPRINTF("Entry: process_elf_binary_data\n"); RUDD

  do_syms++; /* -s */
  do_dump++;
  do_debug_info++;
  do_debug_lines++; /* --debug-dump=info,lines */
  do_debug_loc++;
  do_debug_frames++;
  show_name = 1;

  err = process_file (filename); // PG/SMcC - rather than argv[argc - 1]

  //  FJALAR_DPRINTF("AFTER process_file(0x%x)\n", filename);

  if (dump_sects != NULL) {
    VG_(free) (dump_sects);
    dump_sects = NULL;
    num_dump_sects = 0;
  }
  if (cmdline_dump_sects != NULL) {
    VG_(free) (cmdline_dump_sects);
    cmdline_dump_sects = NULL;
  }

  return err;
}

// End // PG

/*
int main PARAMS ((int, char **));

int
main (argc, argv)
     int argc;
     char **argv;
{
  int status = process_elf_binary_data(argv[argc-1]); // Past last argument, which should be target filename
  return status;
}
*/
