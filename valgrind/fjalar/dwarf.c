/* dwarf.c -- display DWARF contents of a BFD binary file
   Copyright 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012
   Free Software Foundation, Inc.

   This file is part of GNU Binutils.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

/* dwarf.c

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

   Fjalar changes are denoted by // PG or RUDD marks
*/

#include "my_libc.h"

#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"

#include "bfd.h"
#include "bucomm.h"
#include "elfcomm.h"
#include "fjalar_main.h"
#include "fjalar_dwarf.h"

#include "elf/common.h"
#include "elf/external.h"
#include "elf/internal.h"

#include "typedata.h" // PG

static const char *regname (unsigned int regno, int row);

static int need_base_address;

static unsigned int num_debug_info_entries = 0;
static debug_info *debug_information = NULL;
/* Special value for num_debug_info_entries to indicate
   that the .debug_info section could not be loaded/parsed.  */
#define DEBUG_INFO_UNAVAILABLE  (unsigned int) -1

// Symbolic constants for the display attribute routines (markro)
//   Second pass through attributes in process_debug_info?
#define PASS_1            0
#define PASS_2            1
//   OK for typedata to harvest this data?
#define DO_NOT_HARVEST    0
#define OK_TO_HARVEST     1
//   Are we displaying the DWARF debug information?
#define DO_NOT_PRINT      0
#define OK_TO_PRINT       1


char *string_table;
unsigned long string_table_length;
Elf_Internal_Ehdr elf_header;
Elf_Internal_Shdr *section_headers;

int do_debug_frames_interp;

int display_debug_abbrev(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_aranges(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_info(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_not_supported(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_lines(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_pubnames(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_frames(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_macinfo(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_str(Elf_Internal_Shdr *, unsigned char *, FILE *);
int display_debug_loc(Elf_Internal_Shdr *, unsigned char *, FILE *);
void free_abbrevs(void);
PTR get_data(PTR, FILE *, long, size_t, const char *);
int slurp_rela_relocs(FILE *, unsigned long, unsigned long, Elf_Internal_Rela **, unsigned long *);
int slurp_rel_relocs(FILE *, unsigned long, unsigned long, Elf_Internal_Rela **, unsigned long *);
Elf_Internal_Sym *get_32bit_elf_symbols(FILE *, Elf_Internal_Shdr *);
Elf_Internal_Sym *get_64bit_elf_symbols(FILE *, Elf_Internal_Shdr *);


/* Size of pointers in the .debug_line section.  This information is not
   really present in that section.  It's obtained before dumping the debug
   sections by doing some pre-scan of the .debug_info section.  */
int debug_line_pointer_size = 4;


// PG - begin custom libiberty.a functions

PTR
xmalloc (size_t size)
{
  return VG_(malloc)("dwarf.c: xmalloc", size);
}

PTR
xrealloc (PTR oldmem, size_t size)
{
  return VG_(realloc)("dwarf.c: xrealloc", oldmem, size);
}

// PG - end

static void
error VPARAMS ((const char *message, ...))
{
  VA_OPEN (args, message);
  VA_FIXEDARG (args, const char *, message);

  fprintf (stderr, _("%s: Error: "), "dwarf.c");
  vfprintf (stderr, message, args);
  VA_CLOSE (args);
}

static void
warn VPARAMS ((const char *message, ...))
{
  VA_OPEN (args, message);
  VA_FIXEDARG (args, const char *, message);

  fprintf (stderr, _("%s: Warning: "), "dwarf.c");
  vfprintf (stderr, message, args);
  VA_CLOSE (args);
}

static int
size_of_encoded_value (int encoding)
{
  switch (encoding & 0x7)
    {
    default:  /* ??? */
    case 0:   return eh_addr_size;
    case 2:   return 2;
    case 3:   return 4;
    case 4:   return 8;
    }
}

static dwarf_vma
get_encoded_value (unsigned char *data,
                   int encoding,
                   dwarf_vma section_addr,
                   unsigned char *section_start)
{
  int size = size_of_encoded_value (encoding);
  dwarf_vma val;

  if (encoding & DW_EH_PE_signed)
    val = byte_get_signed (data, size);
  else
    val = byte_get (data, size);

  if ((encoding & 0x70) == DW_EH_PE_pcrel)
    val += section_addr + (data - section_start);
  return val;
}

/* Print a dwarf_vma value (typically an address, offset or length) in
   hexadecimal format, followed by a space.  The length of the value (and
   hence the precision displayed) is determined by the byte_size parameter.  */

static const char *
print_dwarf_vma (dwarf_vma val, unsigned byte_size)
{
  static char buff[18];
  int offset = 0;

  /* Printf does not have a way of specifiying a maximum field width for an
     integer value, so we print the full value into a buffer and then select
     the precision we need.  */
#if __STDC_VERSION__ >= 199901L || (defined(__GNUC__) && __GNUC__ >= 2)
#ifndef __MINGW32__
  snprintf (buff, sizeof (buff), "%16.16llx ", val);
#else
  snprintf (buff, sizeof (buff), "%016I64x ", val);
#endif
#else
  snprintf (buff, sizeof (buff), "%16.16lx ", val);
#endif

  if (byte_size != 0)
    {
      if (byte_size > 0 && byte_size <= 8)
        offset = 16 - 2 * byte_size;
      else
        error (_("Wrong size in print_dwarf_vma"));
    }

  return (buff + offset);
}

#if __STDC_VERSION__ >= 199901L || (defined(__GNUC__) && __GNUC__ >= 2)
#ifndef __MINGW32__
#define  DWARF_VMA_FMT "ll"
#else
#define  DWARF_VMA_FMT "I64"
#endif
#else
#define  DWARF_VMA_FMT "l"
#endif

static const char *
dwarf_vmatoa (const char *fmtch, dwarf_vma value)
{
  /* As dwarf_vmatoa is used more then once in a printf call
     for output, we are cycling through an fixed array of pointers
     for return address.  */
  static int buf_pos = 0;
  static struct dwarf_vmatoa_buf
  {
    char place[64];
  } buf[16];
  char fmt[32];
  char *ret;

  sprintf (fmt, "%%%s%s", DWARF_VMA_FMT, fmtch);

  ret = buf[buf_pos++].place;
  buf_pos %= ARRAY_SIZE (buf);

  snprintf (ret, sizeof (buf[0].place), fmt, value);

  return ret;
}

/* Format a 64-bit value, given as two 32-bit values, in hex.
   For reentrancy, this uses a buffer provided by the caller.  */

static const char *
dwarf_vmatoa64 (dwarf_vma hvalue, dwarf_vma lvalue, char *buf,
                unsigned int buf_len)
{
  int len = 0;

  if (hvalue == 0)
    snprintf (buf, buf_len, "%" DWARF_VMA_FMT "x", lvalue);
  else
    {
      len = snprintf (buf, buf_len, "%" DWARF_VMA_FMT "x", hvalue);
      snprintf (buf + len, buf_len - len,
                "%08" DWARF_VMA_FMT "x", lvalue);
    }

  return buf;
}

static dwarf_vma
read_leb128 (unsigned char *data, unsigned int *length_return, int sign)
{
  dwarf_vma result = 0;
  unsigned int num_read = 0;
  unsigned int shift = 0;
  unsigned char byte;

  do
    {
      byte = *data++;
      num_read++;

      result |= ((dwarf_vma) (byte & 0x7f)) << shift;

      shift += 7;

    }
  while (byte & 0x80);

  if (length_return != NULL)
    *length_return = num_read;

  if (sign && (shift < 8 * sizeof (result)) && (byte & 0x40))
    result |= -1L << shift;

  return result;
}

static dwarf_vma
read_uleb128 (unsigned char *data, unsigned int *length_return)
{
  return read_leb128 (data, length_return, 0);
}

static dwarf_signed_vma
read_sleb128 (unsigned char *data, unsigned int *length_return)
{
  return (dwarf_signed_vma) read_leb128 (data, length_return, 1);
}

typedef struct State_Machine_Registers
{
  dwarf_vma address;
  unsigned long last_address; /* Added for Kvasir */
  unsigned int file;
  unsigned int line;
  unsigned int column;
  int is_stmt;
  int basic_block;
  unsigned char op_index;
  unsigned char end_sequence;
/* This variable hold the number of the last entry seen
   in the File Table.  */
  unsigned int last_file_entry;
} SMR;

static SMR state_machine_regs;

static void
reset_state_machine (int is_stmt)
{
  state_machine_regs.address = 0;
  state_machine_regs.op_index = 0;
  state_machine_regs.file = 1;
  state_machine_regs.line = 1;
  state_machine_regs.column = 0;
  state_machine_regs.is_stmt = is_stmt;
  state_machine_regs.basic_block = 0;
  state_machine_regs.end_sequence = 0;
  state_machine_regs.last_file_entry = 0;
}

/* Handled an extend line op.
   Returns the number of bytes read.  */

static int
process_extended_line_op (unsigned char *data, int is_stmt)
{
  unsigned char op_code;
  unsigned int bytes_read;
  unsigned int len;
  unsigned char *name;
  const char *temp;
  dwarf_vma adr;
  unsigned char *orig_data = data;

  len = read_uleb128 (data, & bytes_read);
  data += bytes_read;

  if (len == 0)
    {
      warn (_("badly formed extended line op encountered!\n"));
      return bytes_read;
    }

  len += bytes_read;
  op_code = *data++;

  if (fjalar_debug_dump)
      printf (_("  Extended opcode %d: "), op_code);

  switch (op_code)
    {
    case DW_LNE_end_sequence:
      if (fjalar_debug_dump)
          printf (_("End of Sequence\n\n"));
      reset_state_machine (is_stmt);
      break;

    case DW_LNE_set_address:
      adr = byte_get (data, len - bytes_read - 1);
      if (fjalar_debug_dump)
          printf (_("set Address to 0x%s\n"), dwarf_vmatoa ("x", adr));
      state_machine_regs.address = adr;
      state_machine_regs.op_index = 0;
      break;

    case DW_LNE_define_file:
      if (fjalar_debug_dump) {
          printf (_("define new File Table entry\n"));
          printf (_("  Entry\tDir\tTime\tSize\tName\n"));
      }

      state_machine_regs.last_file_entry++;
      if (fjalar_debug_dump)
          printf ("   %d\t", state_machine_regs.last_file_entry);
      name = data;
      data += VG_(strlen) ((char *) data) + 1;
      temp = dwarf_vmatoa ("u", read_uleb128 (data, & bytes_read));
      if (fjalar_debug_dump)
          printf ("%s\t", temp);
      data += bytes_read;
      temp = dwarf_vmatoa ("u", read_uleb128 (data, & bytes_read));
      if (fjalar_debug_dump)
          printf ("%s\t", temp);
      data += bytes_read;
      temp = dwarf_vmatoa ("u", read_uleb128 (data, & bytes_read));
      if (fjalar_debug_dump)
          printf ("%s\t", temp);
      data += bytes_read;
      if (fjalar_debug_dump) {
          printf ("%s", name);
          if ((unsigned int) (data - orig_data) != len)
              printf (_(" [Bad opcode length]"));
          printf ("\n\n");
      }
      break;

  case DW_LNE_set_discriminator:
      if (fjalar_debug_dump)
          printf (_("set Discriminator to %s\n"),
              dwarf_vmatoa ("u", read_uleb128 (data, & bytes_read)));
      break;

    default:
      {
        unsigned int rlen = len - bytes_read - 1;

        if (fjalar_debug_dump) {
          if (op_code >= DW_LNE_lo_user
            /* The test against DW_LNW_hi_user is redundant due to
               the limited range of the unsigned char data type used
               for op_code.  */
            /*&& op_code <= DW_LNE_hi_user*/)
            printf (_("user defined: "));
          else
            printf (_("UNKNOWN: "));
          printf (_("length %d ["), rlen);
          for (; rlen; rlen--)
            printf (" %02x", *data++);
          printf ("]\n");
        }
      }
      break;
    }

  return len;
}

static const char *debug_str_contents;
static bfd_vma debug_str_size;

static void
load_debug_str (FILE *file)
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

  debug_str_contents = ((char *) get_data (NULL, file, sec->sh_offset, sec->sh_size,
                                           _("debug_str section data")));
}

static void
free_debug_str (void)
{
  if (debug_str_contents == NULL)
    return;

  VG_(free) ((char *) debug_str_contents);
  debug_str_contents = NULL;
  debug_str_size = 0;
}

static const char *
fetch_indirect_string (dwarf_vma offset)
{
  if (debug_str_contents == NULL)
    return _("<no .debug_str section>");

  if (offset > debug_str_size)
    return _("<offset is too big>");

  return debug_str_contents + offset;
}

/* FIXME:  There are better and more efficient ways to handle
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

void
free_abbrevs (void)
{
  abbrev_entry *abbrv;

  for (abbrv = first_abbrev; abbrv;)
    {
      abbrev_entry *next_abbrev = abbrv->next;
      abbrev_attr *attr;

      for (attr = abbrv->first_attr; attr;)
      {
          abbrev_attr *next_attr = attr->next;

          VG_(free) (attr);
          attr = next_attr;
      }

      VG_(free) (abbrv);
      abbrv = next_abbrev;
    }

  last_abbrev = first_abbrev = NULL;
}

static void
add_abbrev (unsigned long number, unsigned long tag, int children)
{
  abbrev_entry *entry;

  entry = (abbrev_entry *) VG_(malloc) ("dwarf.c: add_abbrev", sizeof (*entry));
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
add_abbrev_attr (unsigned long attribute, unsigned long form)
{
  abbrev_attr *attr;

  attr = (abbrev_attr *) VG_(malloc) ("dwarf.c: add_abbrev_attr", sizeof (*attr));
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
process_abbrev_section (unsigned char *start, unsigned char *end)
{
  if (first_abbrev != NULL)
    return NULL;

  while (start < end)
    {
      unsigned int bytes_read;
      unsigned long entry;
      unsigned long tag;
      unsigned long attribute;
      int children;

      entry = read_uleb128 (start, & bytes_read);
      start += bytes_read;

      /* A single zero is supposed to end the section according
	 to the standard.  If there's more, then signal that to
	 the caller.  */
      if (entry == 0)
	return start == end ? NULL : start;

      tag = read_uleb128 (start, & bytes_read);
      start += bytes_read;

      children = *start++;

      add_abbrev (entry, tag, children);

      do
	{
	  unsigned long form;

	  attribute = read_uleb128 (start, & bytes_read);
	  start += bytes_read;

	  form = read_uleb128 (start, & bytes_read);
	  start += bytes_read;

	  if (attribute != 0)
	    add_abbrev_attr (attribute, form);
	}
      while (attribute != 0);
    }

  return NULL;
}

// PG don't make this static!
const char *
get_TAG_name (unsigned long tag)
{
  const char *name = get_DW_TAG_name ((unsigned int)tag);

  if (name == NULL)
      {
	static char buffer[100];

      snprintf (buffer, sizeof (buffer), _("Unknown TAG value: %lx"), tag);
	return buffer;
      }

  return name;
}

static const char *
get_FORM_name (unsigned long form)
{
  const char *name = get_DW_FORM_name (form);

  if (name == NULL)
      {
	static char buffer[100];

      snprintf (buffer, sizeof (buffer), _("Unknown FORM value: %lx"), form);
	return buffer;
      }

  return name;
}

static unsigned char *
display_block (unsigned char *data, unsigned long length, char ok_to_print)
{
  if (ok_to_print)
    printf (_(" %s byte block: "), dwarf_vmatoa ("u", length));

  while (length --)
    {
      unsigned long temp = (unsigned long) byte_get (data++, 1);
      if (ok_to_print)
        printf ("%lx ", temp);
    }

  return data;
}

static  void
decode_location_expression (unsigned char * data, 
                            unsigned int pointer_size, 
                            unsigned int offset_size, 
                            int dwarf_version,
                            dwarf_vma length,
                            dwarf_vma cu_offset,
                            char pass2, 
                            char ok_to_harvest,
                            dwarf_entry* entry, 
                            location_list* ll)
{
  unsigned op;
  int bytes_read;
  unsigned char *end = data + length;
  unsigned long addr;
  unsigned long uvalue;
  int ok_to_print = fjalar_debug_dump && pass2;

  while (data < end)
  {
    op = *data++;
    if(ll) {
      ll->atom = op;
    }
    switch (op)
    {
      long const_data;
      unsigned long uconst_data;

    case DW_OP_addr:
          addr = (unsigned long) byte_get (data, pointer_size);
          if (ok_to_harvest)
		     harvest_variable_addr_value(entry, addr);
          if (ok_to_print)
             printf ("DW_OP_addr: %s", dwarf_vmatoa ("x", addr));
          data += pointer_size;
	  break;

	case DW_OP_deref:
      if (ok_to_harvest) {
	     if (entry && tag_is_formal_parameter(entry->tag_name)) {
	        harvest_formal_param_location_atom(entry, op, 0);
	     }
      }
	  if (ok_to_print) {printf ("DW_OP_deref");}
	  break;

	case DW_OP_const1u:
	  uconst_data = byte_get (data, 1);
	  if (ok_to_print)
        printf ("DW_OP_const1u: %lu", uconst_data);
      data += 1;
	  break;

	case DW_OP_const1s:
	  const_data = (long) byte_get (data, 1);
	  if (ok_to_print)
        printf ("DW_OP_const1s: %ld", const_data);
      data += 1;
	  break;

	case DW_OP_const2u:
	  uconst_data = byte_get (data, 2);
      if (ok_to_harvest)
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
	      harvest_formal_param_location_atom(entry, op, uconst_data);
	      harvest_formal_param_location_offset(entry, uconst_data);
	    }
      if (ok_to_print)
        printf ("DW_OP_const2u: %lu", uconst_data);
      data += 2;
	  break;

	case DW_OP_const2s:
	  const_data =  (long) byte_get (data, 2);
      if (ok_to_harvest)
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
	      harvest_formal_param_location_atom(entry, op, const_data);
	      harvest_formal_param_location_offset(entry, const_data);
	    }
      if (ok_to_print)
        printf ("DW_OP_const2s: %ld", const_data);
      data += 2;
	  break;

	case DW_OP_const4u:
	  uconst_data =  byte_get (data, 4);
      if (ok_to_harvest)
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
	      harvest_formal_param_location_atom(entry, op, uconst_data);
	      harvest_formal_param_location_offset(entry, uconst_data);
	    }
      if (ok_to_print)
        printf ("DW_OP_const4u: %lu", uconst_data);
      data += 4;
	  break;

	case DW_OP_const4s:
	  const_data = (long) byte_get (data, 4);
      if (ok_to_harvest)
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
	      harvest_formal_param_location_atom(entry, op, const_data);
	      harvest_formal_param_location_offset(entry, const_data);
	    }
      if (ok_to_print)
        printf ("DW_OP_const4s: %ld", const_data);
      data += 4;
	  break;

	case DW_OP_const8u:
	  uconst_data =  byte_get (data, 4);
      if (ok_to_print) {
          printf ("DW_OP_const8u: %lu %lu", uconst_data, (long) byte_get (data + 4, 4));
      }
      else {
          byte_get (data + 4, 4);
      }
      data += 8;
	  break;

	case DW_OP_const8s:
	  const_data = (long) byte_get (data, 4);
      if (ok_to_print) {
          printf ("DW_OP_const8s: %ld %ld", const_data, (long) byte_get (data + 4, 4));
      }
      else {
          byte_get (data + 4, 4);
      }
      data += 8;
	  break;

	case DW_OP_constu:
	  uconst_data = read_uleb128 (data, &bytes_read);
      if (ok_to_harvest)
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
	      harvest_formal_param_location_atom(entry, op, uconst_data);
	      harvest_formal_param_location_offset(entry, uconst_data);
	    }
      if (ok_to_print)
        printf ("DW_OP_constu: %lu", uconst_data);
      data += bytes_read;
	  break;

	case DW_OP_consts:
	  const_data = read_sleb128 (data, &bytes_read);
      if (ok_to_harvest)
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
	      harvest_formal_param_location_atom(entry, op, const_data);
	      harvest_formal_param_location_offset(entry, const_data);
	    }
      if (ok_to_print)
        printf ("DW_OP_consts: %ld", const_data);
      data += bytes_read;
	  break;

	case DW_OP_dup:
	  if (ok_to_print) printf ("DW_OP_dup");
	  break;

	case DW_OP_drop:
	  if (ok_to_print) printf ("DW_OP_drop");
	  break;

	case DW_OP_over:
	  if (ok_to_print) printf ("DW_OP_over");
	  break;

	case DW_OP_pick:
	  const_data = (long) byte_get (data, 1);
	  if (ok_to_print)
          printf ("DW_OP_pick: %ld", const_data);
      data += 1;
	  break;

	case DW_OP_swap:
	  if (ok_to_print) printf ("DW_OP_swap");
	  break;

	case DW_OP_rot:
	  if (ok_to_print) printf ("DW_OP_rot");
	  break;

	case DW_OP_xderef:
	  if (ok_to_print) printf ("DW_OP_xderef");
	  break;

	case DW_OP_abs:
	  if (ok_to_print) printf ("DW_OP_abs");
	  break;

	case DW_OP_and:
	  if (ok_to_print) printf ("DW_OP_and");
	  break;

	case DW_OP_div:
	  if (ok_to_print) printf ("DW_OP_div");
	  break;

	case DW_OP_minus:
	  if (ok_to_print) printf ("DW_OP_minus");
	  break;

	case DW_OP_mod:
	  if (ok_to_print) printf ("DW_OP_mod");
	  break;

	case DW_OP_mul:
	  if (ok_to_print) printf ("DW_OP_mul");
	  break;

	case DW_OP_neg:
	  if (ok_to_print) printf ("DW_OP_neg");
	  break;

	case DW_OP_not:
	  if (ok_to_print) printf ("DW_OP_not");
	  break;

	case DW_OP_or:
	  if (ok_to_print) printf ("DW_OP_or");
	  break;

	case DW_OP_plus:
	  if (ok_to_print) printf ("DW_OP_plus");
	  break;

	case DW_OP_plus_uconst:
      uconst_data = read_uleb128 (data, &bytes_read);
	  if (ok_to_harvest)
      {
	    if (entry && tag_is_formal_parameter(entry->tag_name)) {
		  harvest_formal_param_location_atom(entry, op, (long)uconst_data);
		  harvest_formal_param_location_offset(entry, (long)uconst_data);
		}
        harvest_data_member_location(entry, uconst_data);
	  }
      if (ok_to_print)
          printf ("DW_OP_plus_uconst: %s", dwarf_vmatoa ("u", uconst_data));
      data += bytes_read;
	  break;

	case DW_OP_shl:
	  if (ok_to_print) printf ("DW_OP_shl");
	  break;

	case DW_OP_shr:
	  if (ok_to_print) printf ("DW_OP_shr");
	  break;

	case DW_OP_shra:
	  if (ok_to_print) printf ("DW_OP_shra");
	  break;

	case DW_OP_xor:
	  if (ok_to_print) printf ("DW_OP_xor");
	  break;

	case DW_OP_skip:
	  const_data = (long) byte_get (data, 2);
      if (ok_to_print)
          printf ("DW_OP_skip: %ld", const_data);
      data += 2;
	  break;

	case DW_OP_bra:
	  const_data = (long) byte_get (data, 2);
      if (ok_to_print)
          printf ("DW_OP_bra: %ld", const_data);
      data += 2;
	  break;

	case DW_OP_eq:
	  if (ok_to_print) printf ("DW_OP_eq");
	  break;

	case DW_OP_ge:
	  if (ok_to_print) printf ("DW_OP_ge");
	  break;

	case DW_OP_gt:
	  if (ok_to_print) printf ("DW_OP_gt");
	  break;

	case DW_OP_le:
	  if (ok_to_print) printf ("DW_OP_le");
	  break;

	case DW_OP_lt:
	  if (ok_to_print) printf ("DW_OP_lt");
	  break;

	case DW_OP_ne:
	  if (ok_to_print) printf ("DW_OP_ne");
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
	  if (ok_to_harvest)
          if (entry && (tag_is_formal_parameter(entry->tag_name))) {
	          harvest_formal_param_location_atom(entry, op, 0);
	      }
	  if (ok_to_print)
        printf ("DW_OP_lit%d", op - DW_OP_lit0);
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
	  if (ok_to_harvest)
          if (entry && (tag_is_formal_parameter(entry->tag_name))) {
	          harvest_formal_param_location_atom(entry, op, 0);
	      }
	  if (ok_to_print)
        printf ("DW_OP_reg%d (%s)", op - DW_OP_reg0, regname (op - DW_OP_reg0, 1));
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
          const_data = read_sleb128 (data, &bytes_read);
          //printf("=>DW_OP_breg: %s, %d, %p\n",dwarf_vmatoa("d",const_data),ok_to_harvest,ll);
          if (ok_to_harvest) {
              if(ll) {
                ll->atom_offset = const_data;
              }

	         if(entry) {
		       if (tag_is_variable(entry->tag_name)) {
		         harvest_local_var_offset(entry, const_data);
		       }
		       else if (tag_is_formal_parameter(entry->tag_name)) {
		         harvest_formal_param_location_atom(entry, op, const_data);
		         harvest_formal_param_location_offset(entry, const_data);
		       }
	         }
          }
          if (ok_to_print) {
              printf ("DW_OP_breg%d (%s): %s", op - DW_OP_breg0,
                        regname (op - DW_OP_breg0, 1),
                        dwarf_vmatoa ("d", const_data));
          }
          data += bytes_read;
	  break;

	case DW_OP_regx:
	  uconst_data = read_uleb128 (data, &bytes_read);
      if (ok_to_print)
          printf ("DW_OP_regx: %s (%s)", dwarf_vmatoa ("u", uconst_data), regname (uconst_data,1));
      data += bytes_read;
      break;

	case DW_OP_fbreg:
          const_data = read_sleb128 (data, &bytes_read);
          //printf("=>DW_OP_fbreg: %s, %d, %p\n",dwarf_vmatoa("d",const_data),ok_to_harvest,ll);
          if (ok_to_harvest) {
              if(ll) {
                ll->atom_offset = const_data;
              }

	          if(entry) {
		          if (tag_is_variable(entry->tag_name)) {
		            harvest_local_var_offset(entry, const_data);
		          }
		          else if (tag_is_formal_parameter(entry->tag_name)) {
		            harvest_formal_param_location_atom(entry, op, const_data);
		            harvest_formal_param_location_offset(entry, const_data);
		          }
	          }
          }
          if (ok_to_print) {
              printf ("DW_OP_fbreg: %s", dwarf_vmatoa ("d", const_data));
          }
          data += bytes_read;
	  break;

	case DW_OP_bregx:
          uconst_data = read_uleb128 (data, &bytes_read);
          data += bytes_read;
          if (ok_to_print) {
              printf ("DW_OP_bregx: %s (%s) %s",
                  dwarf_vmatoa ("u", uconst_data), regname (uconst_data, 1),
                  dwarf_vmatoa ("d", read_sleb128 (data, &bytes_read)));
              data += bytes_read;
          } else {
              read_sleb128 (data, &bytes_read);
              data += bytes_read;
          }
          break;

	case DW_OP_piece:
          uconst_data = read_uleb128 (data, &bytes_read);
          if (ok_to_print) {
              printf ("DW_OP_piece: %s", dwarf_vmatoa ("u", uconst_data));
          }
          data += bytes_read;
	  break;

	case DW_OP_deref_size:
	      const_data = (long) byte_get (data, 1);
          if (ok_to_print)
              printf ("DW_OP_deref_size: %ld", const_data);
          data += 1;
	  break;

	case DW_OP_xderef_size:
	      const_data = (long) byte_get (data, 1);
          if (ok_to_print)
              printf ("DW_OP_xderef_size: %ld", const_data);
          data += 1;
	  break;

	case DW_OP_nop:
	  if (ok_to_print) printf ("DW_OP_nop");
	  break;

	/* DWARF 3 extensions.  */

	case DW_OP_push_object_address:
	  if (ok_to_print) printf ("DW_OP_push_object_address");
	  break;

	case DW_OP_call2:
	      const_data = (long) byte_get (data, 2);
          if (ok_to_print)
              printf ("DW_OP_call2: <0x%s>", dwarf_vmatoa ("x", const_data + cu_offset));
          data += 2;
	  break;

	case DW_OP_call4:
	  /* XXX: Strictly speaking for 64-bit DWARF3 files
	     this ought to be an 8-byte wide computation.  */
	  const_data = (long) byte_get (data, 4);
      if (ok_to_print)
          printf ("DW_OP_call4: <0x%s>",dwarf_vmatoa ("x",  const_data + cu_offset));
      data += 4;
	  break;

	case DW_OP_call_ref:
 	  /* XXX: Strictly speaking for 64-bit DWARF3 files
	     this ought to be an 8-byte wide computation.  */
	  if (dwarf_version == -1) {
	      if (ok_to_print) printf (_("(DW_OP_call_ref in frame info)"));
	      /* No way to tell where the next op is, so just bail.  */
	      return;
	  }
	  if (dwarf_version == 2) {
          uconst_data = byte_get (data, pointer_size);
	      if (ok_to_print) printf ("DW_OP_call_ref: <0x%s>",
                                           dwarf_vmatoa ("x", uconst_data));
	      data += pointer_size;
	  } else {
          uconst_data = byte_get (data, offset_size);
	      if (ok_to_print) printf ("DW_OP_call_ref: <0x%s>",
                                           dwarf_vmatoa ("x", uconst_data));
	      data += offset_size;
	  }
	  break;

	case DW_OP_form_tls_address:
	  if (ok_to_print) printf ("DW_OP_form_tls_address");
	  break;

	case DW_OP_call_frame_cfa:
	  if (ok_to_print) printf ("DW_OP_call_frame_cfa");
	  break;

	case DW_OP_bit_piece:
      uconst_data = read_uleb128 (data, &bytes_read);
	  if (ok_to_print) {
          printf ("DW_OP_bit_piece: ");
     	  printf ("size: %s ", dwarf_vmatoa ("u", uconst_data));
      }
	  data += bytes_read;
      uconst_data = read_uleb128 (data, &bytes_read);
	  if (ok_to_print) {
          printf ("offset: %s ", dwarf_vmatoa ("u", uconst_data));
	  }
      data += bytes_read;
	  break;

	  /* DWARF 4 extensions.  */
	case DW_OP_stack_value:
	  if (ok_to_print) printf ("DW_OP_stack_value");
	  break;

	case DW_OP_implicit_value:
	  if (ok_to_print) printf ("DW_OP_implicit_value");
	  uvalue = read_uleb128 (data, &bytes_read);
	  data = display_block (data + bytes_read, uvalue, ok_to_print);
	  break;
      
	default:
	  if (op >= DW_OP_lo_user && op <= DW_OP_hi_user) {
	    if (ok_to_print) printf ("(User defined location op)");
	  } else
	    if (ok_to_print) printf ("(Unknown location op)");
	  /* No way to tell where the next op is, so just bail.  */
	  return;
	}

    /* Separate the ops.  */
    if (data < end) {
        if (ok_to_print) printf ("; ");
    }
  }
}

static unsigned char *
read_and_display_attr_value (unsigned long attribute,
                             unsigned long form,
                             unsigned char *data,
                             unsigned long cu_offset,
                             unsigned long pointer_size,
                             unsigned long offset_size,
                             int dwarf_version,
                             debug_info *debug_info_p,
                             dwarf_entry* entry,
                             char pass2,
                             Elf_Internal_Shdr *section,
                             unsigned char *section_begin)
{
  dwarf_vma uvalue = 0;
  unsigned char *block_start = NULL;
  unsigned char * orig_data = data;
  int bytes_read;
  int ok_to_print = pass2 && fjalar_debug_dump;
  int ok_to_harvest = pass2 && entry_is_listening_for_attribute(entry, attribute);  // false if entry is null

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
      else if (dwarf_version == 3 || dwarf_version == 4)
      {
        uvalue = byte_get (data, offset_size);
        data += offset_size;
      }
      else
        error (_("Internal error: DWARF version is not 2, 3 or 4.\n"));

      break;

    case DW_FORM_addr:
      uvalue = byte_get (data, pointer_size);
      data += pointer_size;
      break;

    case DW_FORM_strp:
    case DW_FORM_sec_offset:
    case DW_FORM_GNU_ref_alt:
    case DW_FORM_GNU_strp_alt:
      uvalue = byte_get (data, offset_size);
      data += offset_size;
      break;

    case DW_FORM_flag_present:
      uvalue = 1;
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
      uvalue = read_sleb128 (data, & bytes_read);
      data += bytes_read;
      break;

    case DW_FORM_GNU_str_index:
      uvalue = read_uleb128 (data, & bytes_read);
      data += bytes_read;
      break;

    case DW_FORM_ref_udata:
    case DW_FORM_udata:
      uvalue = read_uleb128 (data, & bytes_read);
      data += bytes_read;
      break;

    case DW_FORM_indirect:
      form = read_uleb128 (data, & bytes_read);
      data += bytes_read;
      if (ok_to_print)
        printf (" %s", get_FORM_name (form));
      return read_and_display_attr_value (attribute, form, data,
                                          cu_offset, pointer_size,
                                          offset_size, dwarf_version,
                                          debug_info_p, entry, pass2,
                                          section, section_begin);

    case DW_FORM_GNU_addr_index:
      uvalue = read_uleb128 (data, & bytes_read);
      data += bytes_read;
      break; 
    }

  switch (form)
    {
    case DW_FORM_ref_addr:
      if (ok_to_print) {printf (" <0x%s>", dwarf_vmatoa ("x",uvalue));}
      break;

    case DW_FORM_GNU_ref_alt:
      if (ok_to_print) {printf (" <alt 0x%s>", dwarf_vmatoa ("x",uvalue));}
      break;

    case DW_FORM_ref1:
    case DW_FORM_ref2:
    case DW_FORM_ref4:
    case DW_FORM_ref_udata:
      if (ok_to_harvest)
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
      }
      if (ok_to_print)
         printf (" <0x%s>", dwarf_vmatoa ("x", uvalue + cu_offset));
      break;

    case DW_FORM_data4:
    case DW_FORM_addr:
    case DW_FORM_sec_offset:
      if (ok_to_harvest)
         harvest_address_value(entry, attribute, uvalue);
      if (ok_to_print)
         printf (" 0x%s", dwarf_vmatoa ("x", uvalue));
      break;

    case DW_FORM_flag_present:
    case DW_FORM_flag:
    case DW_FORM_data1:
    case DW_FORM_data2:
    case DW_FORM_sdata:
    case DW_FORM_udata:
      if (ok_to_harvest)
         harvest_ordinary_unsigned_value(entry, attribute, uvalue);
      if (ok_to_print)
         printf (" %s", dwarf_vmatoa ("d", uvalue));
      break;

    case DW_FORM_ref8:
    case DW_FORM_data8:
      {
      dwarf_vma high_bits;
      char buf[64];

      byte_get_64 (data, &high_bits, &uvalue);
      if (ok_to_print)
         printf (" 0x%s", dwarf_vmatoa64 (high_bits, uvalue, buf, sizeof (buf)));
      }
      data += 8;
      break;

    // DW_AT_name/DW_AT_comp_dir can be a string, or an indirect string ... (see below)
    case DW_FORM_string:
      if (ok_to_harvest)
         harvest_string(entry, attribute, data);
      if (ok_to_print)
              printf (" %s", data);
      data += VG_(strlen) ((char *) data) + 1;
      break;

    case DW_FORM_block:
    case DW_FORM_exprloc:
      uvalue = read_uleb128 (data, & bytes_read);
      block_start = data + bytes_read;
      data = display_block (block_start, uvalue, ok_to_print);
      break;

    case DW_FORM_block1:
      uvalue = byte_get (data, 1);
      block_start = data + 1;
      data = display_block (block_start, uvalue, ok_to_print);
      break;

    case DW_FORM_block2:
      uvalue = byte_get (data, 2);
      block_start = data + 2;
      data = display_block (block_start, uvalue, ok_to_print);
      break;

    case DW_FORM_block4:
      uvalue = byte_get (data, 4);
      block_start = data + 4;
      data = display_block (block_start, uvalue, ok_to_print);
      break;

    // DW_AT_name/DW_AT_comp_dir can be an indirect string ... but it can also be a string (see above)
    case DW_FORM_strp:
      {
          const char* ind_str = fetch_indirect_string (uvalue);
          if (ok_to_harvest) {
              harvest_string(entry, attribute, ind_str);
          }
          if (ok_to_print)
              printf (_(" (indirect string, offset: 0x%s): %s"), dwarf_vmatoa ("x", uvalue), ind_str);
      }
      break;

    case DW_FORM_indirect:
      /* Handled above.  */
      break;

    default:
      warn (_("Unrecognized form: %lu\n"), form);
      break;
    }

  if (do_debug_loc
      && num_debug_info_entries == 0
      && debug_info_p != NULL)
    {
      switch (attribute)
	{
	case DW_AT_frame_base:
	  //have_frame_base = 1;
	case DW_AT_location:
	case DW_AT_string_length:
	case DW_AT_return_addr:
	case DW_AT_data_member_location:
	case DW_AT_vtable_elem_location:
	case DW_AT_segment:
	case DW_AT_static_link:
	case DW_AT_use_location:
	case DW_AT_GNU_call_site_value:
	case DW_AT_GNU_call_site_data_value:
	case DW_AT_GNU_call_site_target:
	case DW_AT_GNU_call_site_target_clobbered:
    	  if ((dwarf_version < 4
	       && (form == DW_FORM_data4 || form == DW_FORM_data8))
	      || form == DW_FORM_sec_offset)
	    {
	      /* Process location list.  */
#if 0
	      unsigned int lmax = debug_info_p->max_loc_offsets;
	      unsigned int num = debug_info_p->num_loc_offsets;
  
	      if (lmax == 0 || num >= lmax)
		{
		  lmax += 1024;
		  debug_info_p->loc_offsets = (dwarf_vma *)
                      xcrealloc (debug_info_p->loc_offsets,
				 lmax, sizeof (*debug_info_p->loc_offsets));
		  debug_info_p->have_frame_base = (int *)
                      xcrealloc (debug_info_p->have_frame_base,
				 lmax, sizeof (*debug_info_p->have_frame_base));
		  debug_info_p->max_loc_offsets = lmax;
		}
	      debug_info_p->loc_offsets [num] = uvalue;
	      debug_info_p->have_frame_base [num] = have_frame_base;
#endif
	      debug_info_p->num_loc_offsets++;
	    }
	  break;

	case DW_AT_low_pc:
	  if (need_base_address)
	    debug_info_p->base_address = uvalue;
	  break;

	case DW_AT_GNU_addr_base:
          debug_info_p->addr_base = uvalue;
	  break;

	case DW_AT_GNU_ranges_base:
          debug_info_p->ranges_base = uvalue;
	  break;

	case DW_AT_ranges:
    	  if ((dwarf_version < 4
	       && (form == DW_FORM_data4 || form == DW_FORM_data8))
	      || form == DW_FORM_sec_offset)
	    {
	      /* Process range list.  */
#if 0
	      unsigned int lmax = debug_info_p->max_range_lists;
	      unsigned int num = debug_info_p->num_range_lists;

	      if (lmax == 0 || num >= lmax)
		{
		  lmax += 1024;
		  debug_info_p->range_lists = (dwarf_vma *)
                      xcrealloc (debug_info_p->range_lists,
				 lmax, sizeof (*debug_info_p->range_lists));
		  debug_info_p->max_range_lists = lmax;
		}
	      debug_info_p->range_lists [num] = uvalue;
#endif
	      debug_info_p->num_range_lists++;
	    }
	  break;

	default:
	  break;
	}
    }

  /* For some attributes we can display further information.  */
    if (ok_to_print) {printf ("\t");}

  switch (attribute)
    {
    case DW_AT_inline:
      switch (uvalue)
	    {
	    case DW_INL_not_inlined:
          if (ok_to_print) {printf (_("(not inlined)"));}
	      break;
	    case DW_INL_inlined:
          if (ok_to_print) {printf (_("(inlined)"));}
	      break;
	    case DW_INL_declared_not_inlined:
          if (ok_to_print) {printf (_("(declared as inline but ignored)"));}
	      break;
	    case DW_INL_declared_inlined:
          if (ok_to_print) {printf (_("(declared as inline and inlined)"));}
	      break;
	    default:
          if (ok_to_print) {printf (_("  (Unknown inline attribute value: %s)"),
                                                  dwarf_vmatoa ("x", uvalue));}
	      break;
	    }
      break;

    case DW_AT_language:
      switch (uvalue)
	    {
	  /* Ordered by the numeric value of these constants.  */
	case DW_LANG_C89:		if (ok_to_print) {printf ("(ANSI C)");} break;
	case DW_LANG_C:			if (ok_to_print) {printf ("(non-ANSI C)");} break;
	case DW_LANG_Ada83:		if (ok_to_print) {printf ("(Ada)");} break;
	case DW_LANG_C_plus_plus:	if (ok_to_print) {printf ("(C++)");} break;
	case DW_LANG_Cobol74:		if (ok_to_print) {printf ("(Cobol 74)");} break;
	case DW_LANG_Cobol85:		if (ok_to_print) {printf ("(Cobol 85)");} break;
	case DW_LANG_Fortran77:		if (ok_to_print) {printf ("(FORTRAN 77)");} break;
	case DW_LANG_Fortran90:		if (ok_to_print) {printf ("(Fortran 90)");} break;
	case DW_LANG_Pascal83:		if (ok_to_print) {printf ("(ANSI Pascal)");} break;
	case DW_LANG_Modula2:		if (ok_to_print) {printf ("(Modula 2)");} break;
	  /* DWARF 2.1 values.	*/
	case DW_LANG_Java:		if (ok_to_print) {printf ("(Java)");} break;
	case DW_LANG_C99:		if (ok_to_print) {printf ("(ANSI C99)");} break;
	case DW_LANG_Ada95:		if (ok_to_print) {printf ("(ADA 95)");} break;
	case DW_LANG_Fortran95:		if (ok_to_print) {printf ("(Fortran 95)");} break;
   	  /* DWARF 3 values.  */
	case DW_LANG_PLI:		if (ok_to_print) {printf ("(PLI)");} break;
	case DW_LANG_ObjC:		if (ok_to_print) {printf ("(Objective C)");} break;
	case DW_LANG_ObjC_plus_plus:	if (ok_to_print) {printf ("(Objective C++)");} break;
	case DW_LANG_UPC:		if (ok_to_print) {printf ("(Unified Parallel C)");} break;
	case DW_LANG_D:			if (ok_to_print) {printf ("(D)");} break;
	  /* DWARF 4 values.  */
	case DW_LANG_Python:		if (ok_to_print) {printf ("(Python)");} break;
	  /* DWARF 5 values.  */
	case DW_LANG_Go:		if (ok_to_print) {printf ("(Go)");} break;
	  /* MIPS extension.  */
	    case DW_LANG_Mips_Assembler:	if (ok_to_print) {printf ("(MIPS assembler)");} break;
	  /* UPC extension.  */
	    case DW_LANG_Upc:		if (ok_to_print) {printf ("(Unified Parallel C)");} break;
	    default:
	      if (uvalue >= DW_LANG_lo_user && uvalue <= DW_LANG_hi_user) {
	        if (ok_to_print) printf ("(implementation defined: %s)",
		             dwarf_vmatoa ("x", uvalue));
	      } else
	        if (ok_to_print) printf ("(Unknown: %s)",
                                               dwarf_vmatoa ("x", uvalue));
	      break;
	    }
      break;

    case DW_AT_encoding:
      switch (uvalue)
	    {
	    case DW_ATE_void:	    	if (ok_to_print) {printf ("(void)");} break;
	    case DW_ATE_address:		if (ok_to_print) {printf ("(machine address)");} break;
	    case DW_ATE_boolean:		if (ok_to_print) {printf ("(boolean)");} break;
	    case DW_ATE_complex_float:	if (ok_to_print) {printf ("(complex float)");} break;
	    case DW_ATE_float:	    	if (ok_to_print) {printf ("(float)");} break;
	    case DW_ATE_signed:	    	if (ok_to_print) {printf ("(signed)");} break;
	    case DW_ATE_signed_char:	if (ok_to_print) {printf ("(signed char)");} break;
	    case DW_ATE_unsigned:		if (ok_to_print) {printf ("(unsigned)");} break;
	    case DW_ATE_unsigned_char:	if (ok_to_print) {printf ("(unsigned char)");} break;
	  /* DWARF 2.1 values:  */
	    case DW_ATE_imaginary_float:if (ok_to_print) {printf ("(imaginary float)");} break;
	    case DW_ATE_decimal_float:	if (ok_to_print) {printf ("(decimal float)");} break;
	  /* DWARF 3 values:  */
	    case DW_ATE_packed_decimal:	if (ok_to_print) {printf ("(packed_decimal)");} break;
	    case DW_ATE_numeric_string:	if (ok_to_print) {printf ("(numeric_string)");} break;
	    case DW_ATE_edited:	    	if (ok_to_print) {printf ("(edited)");} break;
	    case DW_ATE_signed_fixed:	if (ok_to_print) {printf ("(signed_fixed)");} break;
	    case DW_ATE_unsigned_fixed:	if (ok_to_print) {printf ("(unsigned_fixed)");} break;

        default:
	      if (uvalue >= DW_ATE_lo_user
	          && uvalue <= DW_ATE_hi_user)
          {
	        if (ok_to_print) {printf ("(user defined type)");}
          }
	      else
          {
	        if (ok_to_print) {printf ("(unknown type)");}
          }
	      break;
	    }
      break;

    case DW_AT_accessibility:
      switch (uvalue)
	    {
	    case DW_ACCESS_public:
          if (ok_to_print) printf ("(public)");
          if (ok_to_harvest) harvest_accessibility(entry, DW_ACCESS_public);
          break;
	    case DW_ACCESS_protected:
          if (ok_to_print) printf ("(protected)");
          if (ok_to_harvest) harvest_accessibility(entry, DW_ACCESS_protected);
          break;
	    case DW_ACCESS_private:
          if (ok_to_print) printf ("(private)");
          if (ok_to_harvest) harvest_accessibility(entry, DW_ACCESS_private);
          break;
	    default:
	      if (ok_to_print) printf ("(unknown accessibility)");
	      break;
	    }
      break;

    case DW_AT_visibility:
      switch (uvalue)
	    {
	    case DW_VIS_local:		if (ok_to_print) printf ("(local)"); break;
	    case DW_VIS_exported:		if (ok_to_print) printf ("(exported)"); break;
	    case DW_VIS_qualified:		if (ok_to_print) printf ("(qualified)"); break;
	    default:			if (ok_to_print) printf ("(unknown visibility)"); break;
	    }
      break;

    case DW_AT_virtuality:
      switch (uvalue)
	    {
	    case DW_VIRTUALITY_none:	if (ok_to_print) printf ("(none)"); break;
	    case DW_VIRTUALITY_virtual:	if (ok_to_print) printf ("(virtual)"); break;
	    case DW_VIRTUALITY_pure_virtual:if (ok_to_print) printf ("(pure_virtual)"); break;
	    default:			if (ok_to_print) printf ("(unknown virtuality)"); break;
	    }
      break;

    case DW_AT_identifier_case:
      switch (uvalue)
	    {
	    case DW_ID_case_sensitive:	if (ok_to_print) printf ("(case_sensitive)"); break;
	    case DW_ID_up_case:		if (ok_to_print) printf ("(up_case)"); break;
	    case DW_ID_down_case:		if (ok_to_print) printf ("(down_case)"); break;
	    case DW_ID_case_insensitive:	if (ok_to_print) printf ("(case_insensitive)"); break;
	    default:			if (ok_to_print) printf ("(unknown case)"); break;
	    }
      break;

    case DW_AT_calling_convention:
      switch (uvalue)
	    {
	    case DW_CC_normal:	if (ok_to_print) printf ("(normal)"); break;
	    case DW_CC_program:	if (ok_to_print) printf ("(program)"); break;
	    case DW_CC_nocall:	if (ok_to_print) printf ("(nocall)"); break;
	    default:
	      if (uvalue >= DW_CC_lo_user && uvalue <= DW_CC_hi_user) {
              if (ok_to_print) printf ("(user defined)");
          } else {
              if (ok_to_print) printf ("(unknown convention)");
          }
	    }
      break;

    case DW_AT_ordering:
      switch (uvalue)
	    {
	    case -1: if (ok_to_print) printf ("(undefined)"); break;
	    case 0:  if (ok_to_print) printf ("(row major)"); break;
	    case 1:  if (ok_to_print) printf ("(column major)"); break;
	    }
      break;

    // DW_AT_location, DW_AT_data_member_location return data in this form:
    case DW_AT_location:
    case DW_AT_data_member_location:
      if (block_start)
	  {
          if (ok_to_print) printf ("(");
	      decode_location_expression (block_start, pointer_size, offset_size, dwarf_version,
                                    uvalue, cu_offset, pass2, ok_to_harvest, entry, 0);
          if (ok_to_print) printf (")");
	  }
      else if (form == DW_FORM_data4 || form == DW_FORM_data8)
	  {
          if (ok_to_print) printf ("(");
          if (ok_to_print) printf ("location list");
          if (ok_to_print) printf (")");
	  }
      break;

    case DW_AT_frame_base:
    case DW_AT_string_length:
    case DW_AT_return_addr:
    case DW_AT_vtable_elem_location:
    case DW_AT_segment:
    case DW_AT_static_link:
    case DW_AT_use_location:
    case DW_AT_GNU_call_site_value:
    case DW_AT_GNU_call_site_data_value:
    case DW_AT_GNU_call_site_target:
    case DW_AT_GNU_call_site_target_clobbered:
    case DW_AT_allocated:
    case DW_AT_associated:
    case DW_AT_data_location:
    case DW_AT_stride:
    case DW_AT_upper_bound:
    case DW_AT_lower_bound:
      if (block_start)
	  {
          if (ok_to_print) printf ("(");
	      decode_location_expression (block_start, pointer_size, offset_size, dwarf_version,
                                    uvalue, cu_offset, pass2, ok_to_harvest, entry, 0);
          if (ok_to_print) printf (")");
	  }
      else if (form == DW_FORM_data4 || form == DW_FORM_data8)
	  {
          // RUDD
          if (ok_to_harvest)
              harvest_frame_base(entry, DW_OP_list, uvalue);
          if (ok_to_print) printf ("(");
          if (ok_to_print) printf ("location list");
          if (ok_to_print) printf (")");
	  }
      break;

    case DW_AT_stmt_list:
      harvest_stmt_list(entry, uvalue);
    
      break;

    case DW_AT_decl_file:
      harvest_decl_file(entry, uvalue);
      break;

case DW_AT_import:
      if (ok_to_print) {
	      if (form == DW_FORM_ref_sig8 || form == DW_FORM_GNU_ref_alt)
              break;

	      if (form == DW_FORM_ref1
	          || form == DW_FORM_ref2
	          || form == DW_FORM_ref4
	          || form == DW_FORM_ref_udata) {
	          uvalue += cu_offset;
          }
      
	      if (uvalue >= section->sh_size) {
	  warn (_("Offset %s used as value for DW_AT_import attribute of DIE at offset %lx is too big.\n"),
		      dwarf_vmatoa ("x", uvalue),
		      (unsigned long) (orig_data - section_begin));
	      } else {
	          unsigned long abbrev_number;
	          abbrev_entry * a_entry;
      
	          abbrev_number = read_leb128 (section_begin + uvalue, NULL, 0);
      
	          printf (_("[Abbrev Number: %ld"), abbrev_number);
	          /* Don't look up abbrev for DW_FORM_ref_addr, as it very often will
	             use different abbrev table, and we don't track .debug_info chunks
	             yet.  */
	          if (form != DW_FORM_ref_addr)
	            {
		      for (a_entry = first_abbrev; a_entry != NULL; a_entry = a_entry->next)
		        if (a_entry->entry == abbrev_number)
		          break;
		      if (a_entry != NULL)
		        printf (" (%s)", get_TAG_name (a_entry->tag));
	            }
	          printf ("]");
	        }
      }
      break;

    default:
      break;
    }

  return data;
}

static const char *
get_AT_name (unsigned long attribute)
{
  const char *name;

  /* One value is shared by the MIPS and HP extensions:  */
  if (attribute == DW_AT_MIPS_fde)
    return "DW_AT_MIPS_fde or DW_AT_HP_unmodifiable";

  name = get_DW_AT_name (attribute);

  if (name == NULL)
      {
	static char buffer[100];

      snprintf (buffer, sizeof (buffer), _("Unknown AT value: %lx"),
		attribute);
	return buffer;
      }

  return name;
}

static unsigned char *
read_and_display_attr (unsigned long attribute,
                       unsigned long form,
                       unsigned char *data,
                       unsigned long cu_offset,
                       unsigned long pointer_size,
                       unsigned long offset_size,
                       int dwarf_version,
                       debug_info *debug_info_p,
                       dwarf_entry* entry,
                       char pass2,
                       Elf_Internal_Shdr *section,
                       unsigned char *section_begin)
{
  if (fjalar_debug_dump && pass2)
    printf ("   %-18s:", get_AT_name (attribute));

  data = read_and_display_attr_value (attribute, form, data, cu_offset,
				                      pointer_size, offset_size,
                                      dwarf_version, debug_info_p, entry,
                                      pass2, section, section_begin);

  if (fjalar_debug_dump && pass2)
    printf ("\n");
  
  return data;
}

static int
process_debug_info (Elf_Internal_Shdr *section, unsigned char *start, FILE *file)
{
  unsigned char *end = start + section->sh_size;
  unsigned char *section_begin = start;
  unsigned int unit;
  unsigned int num_units = 0;

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

  //  printf (_("The section %s contains:\n\n"), SECTION_NAME (section_dummy));

  load_debug_str (file_dummy);
  //load_debug_loc (file_dummy);

  while (start_dummy < end_dummy)
    {
      DWARF2_Internal_CompUnit compunit;
      Elf_Internal_Shdr *relsec;
      unsigned char *hdrptr;
//    unsigned char *cu_abbrev_offset_ptr;
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

//    cu_abbrev_offset_ptr = hdrptr;
      compunit.cu_abbrev_offset = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;

      compunit.cu_pointer_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      tags = hdrptr;
      cu_offset = start_dummy - section_begin_dummy;
      start_dummy += compunit.cu_length + initial_length_size;
      
      num_units++;

      // UNDONE: some places check 3, some check 4.     (markro)
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

	  abbrev_number = read_uleb128 (tags, & bytes_read);
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
          if (tag_is_relevant_entry(entry->tag))
              num_relevant_entries++;

	  for (attr = entry->first_attr; attr; attr = attr->next)
	    tags = read_and_display_attr (attr->attribute,
					  attr->form,
					  tags, cu_offset,
					  compunit.cu_pointer_size,
					  offset_size,
					  compunit.cu_version,
                      NULL, DO_NOT_HARVEST,
                      DO_NOT_PRINT, section, section_begin);

	  if (entry->children)
	    ++level;
	}
    }

  free_debug_str ();
  //free_debug_loc ();

    if (num_units == 0) {
	  error (_("No comp units in %s section ?"), SECTION_NAME(section));
	  return 0;
	}

    /* Then allocate an array to hold the information.  */
    debug_information = (debug_info *)
                        VG_(malloc) ("dwarf.c: process_debug_info", num_units * sizeof (* debug_information));
    if (debug_information == NULL) {
	  error (_("Not enough memory for a debug info array of %u entries"), num_units);
	  return 0;
	}

    FJALAR_DPRINTF ("Number of relevant entries: %lu\n\n", num_relevant_entries);

  // PG - End dummy run code

  // Construct the global dwarf_entry array
  // Question - when do we destroy it???
  dwarf_entry_array_size = num_relevant_entries;
  initialize_dwarf_entry_array(num_relevant_entries);
  initialize_compile_unit_array(num_units);

  // PG - Begin real code

  if (fjalar_debug_dump) {
      printf (_("Contents of the %s section:\n\n"), SECTION_NAME (section));
  }

  load_debug_str (file);
  //load_debug_loc (file);

  unit = 0;
  while (start < end)
    {
      DWARF2_Internal_CompUnit compunit;
      Elf_Internal_Shdr *relsec;
      unsigned char *hdrptr;
//    unsigned char *cu_abbrev_offset_ptr;
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

//    cu_abbrev_offset_ptr = hdrptr;
      compunit.cu_abbrev_offset = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;

      compunit.cu_pointer_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      tags = hdrptr;
      cu_offset = start - section_begin;
      start += compunit.cu_length + initial_length_size;

	  debug_information [unit].cu_offset = cu_offset;
	  debug_information [unit].pointer_size = compunit.cu_pointer_size;
	  debug_information [unit].offset_size = offset_size;
	  debug_information [unit].dwarf_version = compunit.cu_version;
	  debug_information [unit].base_address = 0;
	  debug_information [unit].addr_base = DEBUG_INFO_UNAVAILABLE;
	  debug_information [unit].ranges_base = DEBUG_INFO_UNAVAILABLE;
	  debug_information [unit].loc_offsets = NULL;
	  debug_information [unit].have_frame_base = NULL;
	  debug_information [unit].max_loc_offsets = 0;
	  debug_information [unit].num_loc_offsets = 0;
	  debug_information [unit].range_lists = NULL;
	  debug_information [unit].max_range_lists= 0;
	  debug_information [unit].num_range_lists = 0;

      if (fjalar_debug_dump) {
         FJALAR_DPRINTF (_("  <before second pass> \n"));
         printf (_("  Compilation Unit @ offset 0x%s:\n"), dwarf_vmatoa ("x", cu_offset));
	     printf (_("   Length:        0x%s (%s)\n"), dwarf_vmatoa ("x", compunit.cu_length),
		           offset_size == 8 ? "64-bit" : "32-bit");
	     printf (_("   Version:       %d\n"), compunit.cu_version);
	     printf (_("   Abbrev Offset: 0x%s\n"), dwarf_vmatoa ("x", compunit.cu_abbrev_offset));
	     printf (_("   Pointer Size:  %d\n"), compunit.cu_pointer_size);
      }

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
      while (tags < start) {
	      int bytes_read;
	      unsigned long abbrev_number;
          unsigned long temp_ID;
          unsigned long temp_tag_name;
	      abbrev_entry *entry;
	      abbrev_attr *attr;
          dwarf_entry *dwarf_entry_item;

	      abbrev_number = read_uleb128 (tags, & bytes_read);
	      tags += bytes_read;

	      /* A null DIE marks the end of a list of siblings or it may also be
	         a section padding.  */
	      if (abbrev_number == 0) {
	          --level;
	          continue;
	      }
    
	      /* Scan through the abbreviation list until we reach the
	         correct entry.  */
	      for (entry = first_abbrev;
	           entry && entry->entry != abbrev_number;
	           entry = entry->next)
	        continue;

	      if (entry == NULL) {
	          warn (_("Unable to locate entry %lu in the abbreviation table\n"),
		        abbrev_number);
	          return 0;
	      }

          temp_ID = (unsigned long) (tags - section_begin - bytes_read);
          temp_tag_name = entry->tag;

          if (tag_is_relevant_entry(entry->tag)) {
              // PG - This is where all the action takes place
              //      store the info. as a dwarf_entry struct in dwarf_entry_array

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
              dwarf_entry_item = &dwarf_entry_array[idx];
              idx++;
          } else {
              dwarf_entry_item = NULL;
          }    

          if (fjalar_debug_dump) {
              printf (_(" <%d><%lx>: Abbrev Number: %lu (%s)\n"),
                      level,
                      temp_ID,
                      abbrev_number,
                      get_TAG_name (temp_tag_name));
          }

          for (attr = entry->first_attr; attr; attr = attr->next)
          {
	        debug_info *arg;
            if (fjalar_debug_dump) {
		      /* Show the offset from where the tag was extracted.  */
		      printf ("    <%lx>", (unsigned long)(tags - section_begin));
            }

	        arg = debug_information;
	        if (debug_information)
		      arg += unit;

            tags = read_and_display_attr (attr->attribute,
                                          attr->form,
                                          tags, cu_offset,
                                          compunit.cu_pointer_size,
                                          offset_size,
                                          compunit.cu_version,
                                          arg, dwarf_entry_item,
                                          OK_TO_PRINT, section, section_begin);
          }

          if (entry->children)
              ++level;
	   }
       unit++;
    }

    num_debug_info_entries = num_units;

  free_debug_str ();
  //free_debug_loc ();

  // PG - Now that all of the entries are in the array, finish initializing
  //     it by creating various links and filling in all dwarf_entry fields
  finish_dwarf_entry_array_init();

  // Print contents of array for help debugging
  // print_dwarf_entry_array();

  if (fjalar_debug_dump)
      printf ("\n");

  return 1;
}

static int
display_debug_lines_raw (Elf_Internal_Shdr *section, unsigned char *start, unsigned char* end)
{
  DWARF2_Internal_LineInfo linfo;
  unsigned char *standard_opcodes;
  unsigned char *data = start;
  unsigned char *end_of_sequence;
  unsigned char *hdrptr;
  unsigned long hdroff;
  int initial_length_size;
  int offset_size;
  int i;

  int dir_table_index;
  unsigned int cur_line_offset = 0;
  XArray* dir_table  = NULL;
  XArray* file_table = NULL;
  
  if (fjalar_debug_dump)
      printf (_("Raw dump of debug contents of section %s:\n\n"), SECTION_NAME (section));

  while (data < end)
    {
      cur_line_offset = data - start;
      
      dir_table = VG_(newXA) (VG_(malloc), "display_debug_lines.0", VG_(free), sizeof(char *));
      dir_table_index = 0;
      file_table = VG_(newXA) (VG_(malloc), "display_debug_lines.1", VG_(free), sizeof(char *));

      hdrptr = data;
      hdroff = hdrptr - start;

      /* Check the length of the block.  */
      linfo.li_length = byte_get (hdrptr, 4);
      hdrptr += 4;

      if (linfo.li_length == 0xffffffff)
	{
	  /* This section is 64-bit DWARF 3.  */
	  linfo.li_length = byte_get (hdrptr, 8);
	  hdrptr += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      if (linfo.li_length + initial_length_size > section->sh_size)
	{
	  warn
	    (_("The information in section %s appears to be corrupt - the section is too small\n"),
	     SECTION_NAME(section));
	  return 0;
	}

      /* Check its version number.  */
      linfo.li_version = byte_get (hdrptr, 2);
      hdrptr += 2;
      if (linfo.li_version != 2
	  && linfo.li_version != 3
	  && linfo.li_version != 4)
	{
	  warn (_("Only DWARF version 2, 3 and 4 line info is currently supported.\n"));
	  return 0;
	}

      linfo.li_prologue_length = byte_get (hdrptr, offset_size);
      hdrptr += offset_size;
      linfo.li_min_insn_length = byte_get (hdrptr, 1);
      hdrptr++;
      if (linfo.li_version >= 4)
	{
	  linfo.li_max_ops_per_insn = byte_get (hdrptr, 1);
      hdrptr++;
	  if (linfo.li_max_ops_per_insn == 0)
	    {
	      warn (_("Invalid maximum operations per insn.\n"));
	      return 0;
	    }
	}
      else
	linfo.li_max_ops_per_insn = 1;
      linfo.li_default_is_stmt = byte_get (hdrptr, 1);
      hdrptr++;
      linfo.li_line_base = byte_get (hdrptr, 1);
      hdrptr++;
      linfo.li_line_range = byte_get (hdrptr, 1);
      hdrptr++;
      linfo.li_opcode_base = byte_get (hdrptr, 1);
      hdrptr++;

      /* Sign extend the line base field.  */
      linfo.li_line_base <<= 24;
      linfo.li_line_base >>= 24;

      if (fjalar_debug_dump) {
          printf (_("  Offset:                      0x%lx\n"), hdroff);
          printf (_("  Length:                      %ld\n"), (long) linfo.li_length);
          printf (_("  DWARF Version:               %d\n"), linfo.li_version);
          printf (_("  Prologue Length:             %d\n"), linfo.li_prologue_length);
          printf (_("  Minimum Instruction Length:  %d\n"), linfo.li_min_insn_length);
      if (linfo.li_version >= 4)
          printf (_("  Maximum Ops per Instruction: %d\n"), linfo.li_max_ops_per_insn);
          printf (_("  Initial value of 'is_stmt':  %d\n"), linfo.li_default_is_stmt);
          printf (_("  Line Base:                   %d\n"), linfo.li_line_base);
          printf (_("  Line Range:                  %d\n"), linfo.li_line_range);
          printf (_("  Opcode Base:                 %d\n"), linfo.li_opcode_base);
      }

      end_of_sequence = data + linfo.li_length + initial_length_size;

      reset_state_machine (linfo.li_default_is_stmt);

      /* Display the contents of the Opcodes table.  */
      standard_opcodes = hdrptr;

      if (fjalar_debug_dump) {
          printf (_("\n Opcodes:\n"));

          for (i = 1; i < linfo.li_opcode_base; i++)
             printf (_("  Opcode %d has %d args\n"), i, standard_opcodes[i - 1]);
      }

      /* Display the contents of the Directory table.  */
      data = standard_opcodes + linfo.li_opcode_base - 1;
      
      if (*data == 0) {
          if (fjalar_debug_dump)
              printf (_("\n The Directory Table is empty.\n"));
      } else {
          if (fjalar_debug_dump)
	          printf (_("\n The Directory Table:\n"));

	    while (*data != 0)
	    {
          if (fjalar_debug_dump)
	          printf ("  %s\n", data);
          VG_(addToXA)(dir_table, &data);
	      data += VG_(strlen) ((char *) data) + 1;
          dir_table_index++;
	    }
	  }

      /* Skip the NUL at the end of the table.  */
      data++;

      /* Display the contents of the File Name table.  */
      if (*data == 0) {
          if (fjalar_debug_dump)
             printf (_("\n The File Name Table is empty.\n"));
      } else {
          if (fjalar_debug_dump) {
             printf (_("\n The File Name Table:\n"));
             printf (_("  Entry\tDir\tTime\tSize\tName\n"));
          }

	  while (*data != 0)
	    {
	      int bytes_read;
          unsigned long dir_index = 0;
          char* full_name = NULL;
	      char* file_name = NULL;
          char* dir_name  = NULL;
          unsigned int dir_name_len = 0;
          unsigned int full_name_len = 0;
          const char* temp;
              
	      state_machine_regs.last_file_entry++;
	      if (fjalar_debug_dump)
              printf ("  %d\t", state_machine_regs.last_file_entry);
	      file_name = data;
	      data += VG_(strlen) ((char *) data) + 1;

	      dir_index = read_uleb128(data, &bytes_read);
          if (fjalar_debug_dump)
              printf ("%s\t", dwarf_vmatoa ("u", dir_index));
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
              
              //              printf("Full_name: %s\n", full_name);
              VG_(addToXA)(file_table, &full_name);
              
              // Modification date and time
              temp = dwarf_vmatoa ("u", read_uleb128(data, & bytes_read));
	          if (fjalar_debug_dump)
                  printf ("%s\t", temp);
	          data += bytes_read;
              temp = dwarf_vmatoa ("u", read_uleb128(data, & bytes_read));
	          if (fjalar_debug_dump)
                  printf ("%s\t", temp);
	          data += bytes_read;
              if (fjalar_debug_dump)
                  printf ("%s\n", file_name);
	    }
	}

      harvest_file_name_table(cur_line_offset, file_table);

      /* Skip the NUL at the end of the table.  */
      data++;

      /* Now display the statements.  */
      if (fjalar_debug_dump)
          printf (_("\n Line Number Statements:\n"));

      /* This loop iterates through the Dwarf Line Number Program.  */
      while (data < end_of_sequence)
	{
	  unsigned char op_code;
	  dwarf_signed_vma adv;
	  dwarf_vma uladv;
      unsigned int bytes_read;
      const char* temp;

	  op_code = *data++;

	  if (op_code >= linfo.li_opcode_base)
	    {
	      op_code -= linfo.li_opcode_base;
	      uladv = (op_code / linfo.li_line_range);
	      if (linfo.li_max_ops_per_insn == 1)
		{
		  uladv *= linfo.li_min_insn_length;
		  state_machine_regs.address += uladv;
		  if (fjalar_debug_dump)
              printf (_("  Special opcode %d: "
			    "advance Address by %s to 0x%s"),
			  op_code, dwarf_vmatoa ("u", uladv),
			  dwarf_vmatoa ("x", state_machine_regs.address));
		}
	      else
		{
		  // VLIW machine
          state_machine_regs.address
		    += ((state_machine_regs.op_index + uladv)
			/ linfo.li_max_ops_per_insn)
		       * linfo.li_min_insn_length;
		  state_machine_regs.op_index
		    = (state_machine_regs.op_index + uladv)
		      % linfo.li_max_ops_per_insn;
		  if (fjalar_debug_dump)
              printf (_("  Special opcode %d: "
			    "advance Address by %s to 0x%s[%d]"),
			  op_code, dwarf_vmatoa ("u", uladv),
			  dwarf_vmatoa ("x", state_machine_regs.address),
			  state_machine_regs.op_index);
		}
          // we're in the middle of a print line, save value for print below
          // uladv = state_machine_regs.last_address;
          genputtable(next_line_addr,
			  (void *)(ptrdiff_t)state_machine_regs.last_address,
			  (void *)(ptrdiff_t)state_machine_regs.address);
	      state_machine_regs.last_address = state_machine_regs.address;
          adv = (op_code % linfo.li_line_range) + linfo.li_line_base;
	      state_machine_regs.line += adv;
          if (fjalar_debug_dump)
              printf (_(" and Line by %s to %d\n"),
		      dwarf_vmatoa ("d", adv), state_machine_regs.line);
		  // if (fjalar_debug_dump) printf (_("  call genputtable %p %s %s\n"), next_line_addr,
			  // dwarf_vmatoa ("x", uladv),
			  // dwarf_vmatoa ("x", state_machine_regs.address));
	    }
	  else switch (op_code)
	    {
	    case DW_LNS_extended_op:
	      data += process_extended_line_op (data, linfo.li_default_is_stmt);
	      break;

	    case DW_LNS_copy:
          if (fjalar_debug_dump)
              printf (_("  Copy\n"));

          // Copy means to add another row to the state table.
          // This means we need to add another entry to the next_line_addr collection.  (markro)

	      genputtable(next_line_addr,
              (void *)(ptrdiff_t)state_machine_regs.last_address,
			  (void *)(ptrdiff_t)state_machine_regs.address);
		  // if (fjalar_debug_dump) printf (_("  call genputtable %p %s %s\n"), next_line_addr,
			  // dwarf_vmatoa ("x", state_machine_regs.last_address),
			  // dwarf_vmatoa ("x", state_machine_regs.address));
	      state_machine_regs.last_address = state_machine_regs.address;
	      break;

	    case DW_LNS_advance_pc:
	      uladv = read_uleb128 (data, & bytes_read);
	      data += bytes_read;
	      if (linfo.li_max_ops_per_insn == 1)
		{
		  uladv *= linfo.li_min_insn_length;
		  state_machine_regs.address += uladv;
		  if (fjalar_debug_dump)
              printf (_("  Advance PC by %s to 0x%s\n"),
			  dwarf_vmatoa ("u", uladv),
			  dwarf_vmatoa ("x", state_machine_regs.address));
		}
	      else
		{
		  // VLIW machine
		  state_machine_regs.address
		    += ((state_machine_regs.op_index + uladv)
			/ linfo.li_max_ops_per_insn)
		       * linfo.li_min_insn_length;
		  state_machine_regs.op_index
		    = (state_machine_regs.op_index + uladv)
		      % linfo.li_max_ops_per_insn;
		  if (fjalar_debug_dump)
              printf (_("  Advance PC by %s to 0x%s[%d]\n"),
			  dwarf_vmatoa ("u", uladv),
			  dwarf_vmatoa ("x", state_machine_regs.address),
			  state_machine_regs.op_index);
		}
	      genputtable(next_line_addr,
              (void *)(ptrdiff_t)state_machine_regs.last_address,
			  (void *)(ptrdiff_t)state_machine_regs.address);
		  // if (fjalar_debug_dump) printf (_("  call genputtable %p %s %s\n"), next_line_addr,
			  // dwarf_vmatoa ("x", state_machine_regs.last_address),
			  // dwarf_vmatoa ("x", state_machine_regs.address));
	      state_machine_regs.last_address = state_machine_regs.address;
          break;

	    case DW_LNS_advance_line:
	      adv = read_sleb128 (data, & bytes_read);
	      data += bytes_read;
	      state_machine_regs.line += adv;
          if (fjalar_debug_dump)
              printf (_("  Advance Line by %s to %d\n"),
		        dwarf_vmatoa ("d", adv),
			state_machine_regs.line);
	      break;

	    case DW_LNS_set_file:
	      adv = read_uleb128 (data, & bytes_read);
	      data += bytes_read;
          if (fjalar_debug_dump)
              printf (_("  Set File Name to entry %s in the File Name Table\n"),
		      dwarf_vmatoa ("d", adv));
	      state_machine_regs.file = adv;
	      break;

	    case DW_LNS_set_column:
              uladv = read_uleb128 (data, & bytes_read);
	      data += bytes_read;
          if (fjalar_debug_dump)
              printf (_("  Set column to %s\n"),
		      dwarf_vmatoa ("u", uladv));
          state_machine_regs.column = uladv;
	      break;

	    case DW_LNS_negate_stmt:
	      adv = state_machine_regs.is_stmt;
	      adv = ! adv;
	      if (fjalar_debug_dump)
              printf (_("  Set is_stmt to %s\n"), dwarf_vmatoa ("d", adv));
	      state_machine_regs.is_stmt = adv;
	      break;

	    case DW_LNS_set_basic_block:
	      if (fjalar_debug_dump)
              printf (_("  Set basic block\n"));
	      state_machine_regs.basic_block = 1;
	      break;

	    case DW_LNS_const_add_pc:
	      uladv = ((255 - linfo.li_opcode_base) / linfo.li_line_range);
	      if (linfo.li_max_ops_per_insn)
		{
		  uladv *= linfo.li_min_insn_length;
	      state_machine_regs.address += uladv;
		  if (fjalar_debug_dump)
              printf (_("  Advance PC by constant %s to 0x%s\n"),
			  dwarf_vmatoa ("u", uladv),
			  dwarf_vmatoa ("x", state_machine_regs.address));
		}
	      else
		{
		  // VLIW machine
		  state_machine_regs.address
		    += ((state_machine_regs.op_index + uladv)
			/ linfo.li_max_ops_per_insn)
		       * linfo.li_min_insn_length;
		  state_machine_regs.op_index
		    = (state_machine_regs.op_index + uladv)
		      % linfo.li_max_ops_per_insn;
		  if (fjalar_debug_dump)
              printf (_("  Advance PC by constant %s to 0x%s[%d]\n"),
			  dwarf_vmatoa ("u", uladv),
			  dwarf_vmatoa ("x", state_machine_regs.address),
			  state_machine_regs.op_index);
		}
	      genputtable(next_line_addr,
			  (void *)(ptrdiff_t)state_machine_regs.last_address,
			  (void *)(ptrdiff_t)state_machine_regs.address);
		  // if (fjalar_debug_dump) printf (_("  call genputtable %p %s %s\n"), next_line_addr,
			  // dwarf_vmatoa ("x", state_machine_regs.last_address),
			  // dwarf_vmatoa ("x", state_machine_regs.address));
	      state_machine_regs.last_address = state_machine_regs.address;
          break;

	    case DW_LNS_fixed_advance_pc:
          uladv = byte_get (data, 2);
	      data += 2;
	      state_machine_regs.address += uladv;
	      state_machine_regs.op_index = 0;
	      if (fjalar_debug_dump)
              printf (_("  Advance PC by fixed size amount %s to 0x%s\n"),
		      dwarf_vmatoa ("u", uladv),
		      dwarf_vmatoa ("x", state_machine_regs.address));
	      genputtable(next_line_addr,
			  (void *)(ptrdiff_t)state_machine_regs.last_address,
			  (void *)(ptrdiff_t)state_machine_regs.address);
		  // if (fjalar_debug_dump) printf (_("  call genputtable %p %s %s\n"), next_line_addr,
			  // dwarf_vmatoa ("x", state_machine_regs.last_address),
			  // dwarf_vmatoa ("x", state_machine_regs.address));
	      state_machine_regs.last_address = state_machine_regs.address;
          break;

	    case DW_LNS_set_prologue_end:
	      if (fjalar_debug_dump)
              printf (_("  Set prologue_end to true\n"));
	      break;

	    case DW_LNS_set_epilogue_begin:
	      if (fjalar_debug_dump)
              printf (_("  Set epilogue_begin to true\n"));
	      break;

	    case DW_LNS_set_isa:
              uladv = read_uleb128 (data, & bytes_read);
	      data += bytes_read;
	      if (fjalar_debug_dump)
              printf (_("  Set ISA to %s\n"), dwarf_vmatoa ("u", uladv));
	      break;

	    default:
	      if (fjalar_debug_dump)
              printf (_("  Unknown opcode %d with operands: "), op_code);

	      for (i = standard_opcodes[op_code - 1]; i > 0 ; --i)
	      {
		      temp = dwarf_vmatoa ("x", read_uleb128 (data, &bytes_read));
		      if (fjalar_debug_dump)
                  printf ("0x%s%s", temp, i == 1 ? "" : ", ");
		      data += bytes_read;
		}
	      if (fjalar_debug_dump)
              printf ("\n");
	      break;
	    }
	}
	      if (fjalar_debug_dump)
              printf ("\n");
   	
      // We're not leaking the previous iteration's file_table. It's being passed to typedata.c
      // who will be in charge of it's deletion.
      VG_(deleteXA)(dir_table);
    }
  
  return 1;
}

int
display_debug_lines (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  unsigned char *end = start + section->sh_size;
  int retValRaw = 1;

  retValRaw = display_debug_lines_raw (section, start, end);

  if (!retValRaw)
    return 0;

  return 1;
}

static debug_info *
find_debug_info_for_offset (unsigned long offset)
{
  unsigned int i;

  if (num_debug_info_entries == DEBUG_INFO_UNAVAILABLE)
    return NULL;

  for (i = 0; i < num_debug_info_entries; i++)
    if (debug_information[i].cu_offset == offset)
      return debug_information + i;

  return NULL;
}

// We only call this function if fjalar_debug_dump is true
int
display_debug_pubnames (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  DWARF2_Internal_PubNames names;
  unsigned char *end;

  end = start + section->sh_size;

  printf (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

  while (start < end)
    {
      unsigned char *data;
      unsigned long offset;
      int offset_size, initial_length_size;

      data = start;

      names.pn_length = byte_get (data, 4);
      data += 4;
      if (names.pn_length == 0xffffffff)
	{
	  names.pn_length = byte_get (data, 8);
	  data += 8;
	  offset_size = 8;
	  initial_length_size = 12;
	}
      else
	{
	  offset_size = 4;
	  initial_length_size = 4;
	}

      names.pn_version = byte_get (data, 2);
      data += 2;

      names.pn_offset = byte_get (data, offset_size);
      data += offset_size;

      if (num_debug_info_entries != DEBUG_INFO_UNAVAILABLE
	  && num_debug_info_entries > 0
	  && find_debug_info_for_offset (names.pn_offset) == NULL)
	warn (_(".debug_info offset of 0x%lx in %s section does not point to a CU header.\n"),
	      (unsigned long) names.pn_offset, SECTION_NAME(section));

      names.pn_size = byte_get (data, offset_size);
      data += offset_size;

      start += names.pn_length + initial_length_size;

      if (names.pn_version != 2 && names.pn_version != 3)
	{
	  static int warned = 0;

	  if (! warned)
	    {
	      warn (_("Only DWARF 2 and 3 pubnames are currently supported\n"));
	      warned = 1;
	    }

	  continue;
	}

    printf (_("  Length:                              %ld\n"), (Word) names.pn_length);
    printf (_("  Version:                             %d\n"), names.pn_version);
    printf (_("  Offset into .debug_info section:     0x%lx\n"), (unsigned long) names.pn_offset);
    printf (_("  Size of area in .debug_info section: %ld\n"), (long) names.pn_size);
    printf (_("\n    Offset\tName\n"));

      do
	{
	  offset = byte_get (data, offset_size);

	  if (offset != 0)
	    {
	      data += offset_size;
	      printf ("    %-6lx\t%s\n", offset, data);
	      data += VG_(strlen) ((char *) data) + 1;
	    }
	}
      while (offset != 0);
    }

  printf ("\n");
  return 1;
}

// We only call this function if fjalar_debug_dump is true
int
display_debug_macinfo (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  unsigned char *end = start + section->sh_size;
  unsigned char *curr = start;
  unsigned int bytes_read;
  enum dwarf_macinfo_record_type op;

  printf (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

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

	    lineno = read_uleb128 (curr, & bytes_read);
	    curr += bytes_read;
	    filenum = read_uleb128 (curr, & bytes_read);
	    curr += bytes_read;

	    printf (_(" DW_MACINFO_start_file - lineno: %d filenum: %d\n"), lineno, filenum);
	  }
	  break;

	case DW_MACINFO_end_file:
	  printf (_(" DW_MACINFO_end_file\n"));
	  break;

	case DW_MACINFO_define:
	  lineno = read_uleb128 (curr, & bytes_read);
	  curr += bytes_read;
	  string = curr;
	  curr += VG_(strlen) (string) + 1;
	  printf (_(" DW_MACINFO_define - lineno : %d macro : %s\n"), lineno, string);
	  break;

	case DW_MACINFO_undef:
	  lineno = read_uleb128 (curr, & bytes_read);
	  curr += bytes_read;
	  string = curr;
	  curr += VG_(strlen) (string) + 1;
	  printf (_(" DW_MACINFO_undef - lineno : %d macro : %s\n"), lineno, string);
	  break;

	case DW_MACINFO_vendor_ext:
	  {
	    unsigned int constant;

	    constant = read_uleb128 (curr, & bytes_read);
	    curr += bytes_read;
	    string = curr;
	    curr += VG_(strlen) (string) + 1;
	    printf (_(" DW_MACINFO_vendor_ext - constant : %d string : %s\n"), constant, string);
	  }
	  break;
	}
    }

  return 1;
}

// We only call this function if fjalar_debug_dump is true
int
display_debug_abbrev (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  abbrev_entry *entry;
  unsigned char *original_start = start;
  unsigned char *end = start + section->sh_size;

  printf (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

  do
    {
      unsigned char *last;

      last = start;
      start = process_abbrev_section (start, end);

      if (first_abbrev == NULL)
	continue;

      printf (_("  Number TAG (0x%lx)\n"), (long) (last - original_start));

      for (entry = first_abbrev; entry; entry = entry->next)
	{
	  abbrev_attr *attr;

	  printf ("   %ld      %s    [%s]\n",
		  entry->entry,
		  get_TAG_name (entry->tag),
		  entry->children ? _("has children") : _("no children"));

	  for (attr = entry->first_attr; attr; attr = attr->next)
	    {
	      printf ("    %-18s %s\n",
		      get_AT_name (attr->attribute),
		      get_FORM_name (attr->form));
	    }
	}

      free_abbrevs ();
    }
  while (start);

  printf ("\n");

  return 1;
}

#if 0
static const char *debug_loc_contents;
static bfd_vma debug_loc_size;

static void
load_debug_loc (FILE *file)
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
free_debug_loc (void)
{
  if (debug_loc_contents == NULL)
    return;

  VG_(free) ((char *) debug_loc_contents);
  debug_loc_contents = NULL;
  debug_loc_size = 0;
}
#endif

/* Display a location list from a normal (ie, non-dwo) .debug_loc section.  */

static void
display_loc_list (Elf_Internal_Shdr *section,
                  unsigned char **start_ptr,
                  int debug_info_entry,
                  unsigned long offset,
                  unsigned long base_address,
                  unsigned char *section_begin)
{
  unsigned char *start = *start_ptr;
  unsigned char *section_end = section_begin + section->sh_size;
  unsigned long cu_offset = debug_information [debug_info_entry].cu_offset;
  unsigned int pointer_size = debug_information [debug_info_entry].pointer_size;
  unsigned int offset_size = debug_information [debug_info_entry].offset_size;
  int dwarf_version = debug_information [debug_info_entry].dwarf_version;

  dwarf_vma begin;
  dwarf_vma end;
  unsigned short length;
  
  while (1) {
      if (start + 2 * pointer_size > section_end) {
          warn (_("Location list starting at offset 0x%lx is not terminated.\n"),
                offset);
          break;
      }

      /* Note: we use sign extension here in order to be sure that we can detect
         the -1 escape value.  Sign extension into the top 32 bits of a 32-bit
         address will not affect the values that we display since we always show
         hex values, and always the bottom 32-bits.  */
      begin = byte_get_signed (start, pointer_size);
      start += pointer_size;
      end = byte_get_signed (start, pointer_size);
      start += pointer_size;

      if (fjalar_debug_dump)
          printf ("    %8.8lx ", offset);

      if (begin == 0 && end == 0) {
          if (fjalar_debug_dump)
              printf (_("<End of list>\n"));
          break;
      }

      /* Check base address specifiers.  */
      if (begin == (dwarf_vma) -1 && end != (dwarf_vma) -1) {
          base_address = end;
          if (fjalar_debug_dump) {
              printf ("%s", print_dwarf_vma (begin, pointer_size));
              printf ("%s", print_dwarf_vma (end, pointer_size));
              printf (_("(base address)\n"));
          }
          continue;
      }

      if (start + 2 > section_end) {
          warn (_("Location list starting at offset 0x%lx is not terminated.\n"),
                offset);
          break;
      }

      length = byte_get (start, 2);
      start += 2;

      if (start + length > section_end) {
          warn (_("Location list starting at offset 0x%lx is not terminated.\n"),
                offset);
          break;
      }

      if (fjalar_debug_dump) {
          printf ("%s", print_dwarf_vma (begin + base_address, pointer_size));
          printf ("%s", print_dwarf_vma (end + base_address, pointer_size));
      }

      location_list* ll = VG_(calloc)("dwarf.c: display_loc_list", sizeof(location_list), 1);

      ll->offset = offset;
      ll->begin = begin;
      ll->end = end;

      if (fjalar_debug_dump)
          printf ("(");
      decode_location_expression (start,
                                  pointer_size,
                                  offset_size,
                                  dwarf_version,
                                  length,
                                  cu_offset, PASS_2, OK_TO_HARVEST, 0, ll);

      if (fjalar_debug_dump)
          printf (")\n");

      harvest_location_list_entry(ll, offset);
      start += length;
  }
  *start_ptr = start;
}

int
display_debug_loc (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  unsigned long bytes;
  unsigned char *section_begin = start;
  unsigned char *section_end;
  unsigned int i;
  unsigned int j;

  bytes = section->sh_size;
  section_end = start + bytes;

  if (bytes == 0) {
      FJALAR_DPRINTF (_("\nThe .debug_loc section is empty.\n"));
      return 0;
  }

  if (fjalar_debug_dump) {
      printf (_("Contents of the .debug_loc section:\n\n"));
      printf (_("    Offset   Begin    End      Expression\n"));
  }

  // LOOK OUT!  We assume the loc lists are in ascending order.
  // The stand alone version of readelf goes to a lot of trouble to sort them
  // if necessary.  So far, we haven't seen a case that required that.  (markro)
  for (i = 0; start < section_end; i++) {
      unsigned long offset;
      unsigned long base_address = debug_information [i].base_address;

      for (j = 0; j < debug_information[i].num_loc_offsets; j++) {
          offset = start - section_begin;

          if (offset >= bytes) {
              warn (_("Offset 0x%lx is bigger than .debug_loc section size.\n"),
                offset);
              continue;
          }

          display_loc_list (section, &start, i, offset, base_address, section_begin);
      }
  }

  if (fjalar_debug_dump)
      printf ("\n");
  return 1;
}

// We only call this function if fjalar_debug_dump is true
int
display_debug_str (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  unsigned long bytes;
  bfd_vma addr;

  addr  = section->sh_addr;
  bytes = section->sh_size;

  if (bytes == 0)
    {
      printf (_("\nThe .debug_str section is empty.\n"));
      return 0;
    }

  printf (_("Contents of the .debug_str section:\n\n"));

  while (bytes)
    {
      int j;
      int k;
      int lbytes;

      lbytes = (bytes > 16 ? 16 : bytes);

      printf ("  0x%8.8lx ", (unsigned long) addr);

      for (j = 0; j < 16; j++)
    {
      if (j < lbytes)
        printf ("%2.2x", start[j]);
      else
        printf ("  ");

      if ((j & 3) == 3)
        printf (" ");
    }

      for (j = 0; j < lbytes; j++)
    {
	  k = start[j];
	  if (k >= ' ' && k < 0x80)
	    printf ("%c", k);
	  else
	    printf (".");
	}

	  printf ("\n");

      start += lbytes;
      addr  += lbytes;
      bytes -= lbytes;
    }

  printf ("\n");

  return 1;
}

int
display_debug_info (Elf_Internal_Shdr *section, unsigned char *start, FILE *file)
{
    return process_debug_info (section, start, file);
}

// We only call this function if fjalar_debug_dump is true
int
display_debug_aranges (Elf_Internal_Shdr *section, unsigned char *start, FILE *file ATTRIBUTE_UNUSED)
{
  unsigned char *end = start + section->sh_size;

  printf (_("Contents of the %s section:\n\n"), SECTION_NAME (section));

  while (start < end)
    {
      unsigned char *hdrptr;
      DWARF2_Internal_ARange arange;
      unsigned char *addr_ranges;
      dwarf_vma length;
      dwarf_vma address;
      unsigned char address_size;
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

      if (num_debug_info_entries != DEBUG_INFO_UNAVAILABLE
	  && num_debug_info_entries > 0
	  && find_debug_info_for_offset (arange.ar_info_offset) == NULL)
	warn (_(".debug_info offset of 0x%lx in %s section does not point to a CU header.\n"),
	      (unsigned long) arange.ar_info_offset, SECTION_NAME(section));

      arange.ar_pointer_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      arange.ar_segment_size = byte_get (hdrptr, 1);
      hdrptr += 1;

      if (arange.ar_version != 2 && arange.ar_version != 3)
	  {
	    warn (_("Only DWARF 2 and 3 aranges are currently supported.\n"));
	    break;
	  }

      printf (_("  Length:                   %ld\n"), (Word) arange.ar_length);
      printf (_("  Version:                  %d\n"), arange.ar_version);
      printf (_("  Offset into .debug_info:  0x%lx\n"), (UWord) arange.ar_info_offset);
      printf (_("  Pointer Size:             %d\n"), arange.ar_pointer_size);
      printf (_("  Segment Size:             %d\n"), arange.ar_segment_size);

      address_size = arange.ar_pointer_size + arange.ar_segment_size;
     
      if (address_size == 0)
	  {
	    error (_("Invalid address size in %s section!\n"), SECTION_NAME(section));
	    break;
	  }

      /* The DWARF spec does not require that the address size be a power
	  of two, but we do.  This will have to change if we ever encounter
	  an uneven architecture.  */
      if ((address_size & (address_size - 1)) != 0)
	  {
	    warn (_("Pointer size + Segment size is not a power of two.\n"));
	    break;
	  }

      if (address_size > 4)
	    printf (_("\n    Address            Length\n"));
      else
	    printf (_("\n    Address    Length\n"));

      addr_ranges = hdrptr;

      /* Must pad to an alignment boundary that is twice the address size.  */
      excess = (hdrptr - start) % (2 * address_size);
      if (excess)
	    addr_ranges += (2 * address_size) - excess;

      start += arange.ar_length + initial_length_size;

      while (addr_ranges + 2 * address_size <= start)
	  {
	    address = byte_get (addr_ranges, address_size);

	    addr_ranges += address_size;

	    length  = byte_get (addr_ranges, address_size);

	    addr_ranges += address_size;

	    printf ("    ");
	    printf ("%s", print_dwarf_vma (address, address_size));
	    printf ("%s", print_dwarf_vma (length, address_size));
	    printf ("\n");
	  }
    }

  printf ("\n");

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
  unsigned char ptr_size;
  unsigned char segment_size;
}
Frame_Chunk;

static const char *const *dwarf_regnames;
static unsigned int dwarf_regnames_count;

/* A marker for a col_type that means this column was never referenced
   in the frame info.  */
#define DW_CFA_unreferenced (-1)

/* Return 0 if not more space is needed, 1 if more space is needed,
   -1 for invalid reg.  */

static int
frame_need_space (Frame_Chunk *fc, unsigned int reg)
{
  int prev = fc->ncols;

  if (reg < (unsigned int) fc->ncols)
    return 0;

  if (dwarf_regnames_count
      && reg > dwarf_regnames_count)
    return -1;

  fc->ncols = reg + 1;
  fc->col_type = (short int *) xrealloc (fc->col_type, fc->ncols * sizeof (short int));
  fc->col_offset = (int *) xrealloc (fc->col_offset, fc->ncols * sizeof (int));

  while (prev < fc->ncols)
    {
      fc->col_type[prev] = DW_CFA_unreferenced;
      fc->col_offset[prev] = 0;
      prev++;
    }
  return 1;
}

static const char *const dwarf_regnames_i386[] =
{
  "eax", "ecx", "edx", "ebx",
  "esp", "ebp", "esi", "edi",
  "eip", "eflags", NULL,
  "st0", "st1", "st2", "st3",
  "st4", "st5", "st6", "st7",
  NULL, NULL,
  "xmm0", "xmm1", "xmm2", "xmm3",
  "xmm4", "xmm5", "xmm6", "xmm7",
  "mm0", "mm1", "mm2", "mm3",
  "mm4", "mm5", "mm6", "mm7",
  "fcw", "fsw", "mxcsr",
  "es", "cs", "ss", "ds", "fs", "gs", NULL, NULL,
  "tr", "ldtr"
};

void
init_dwarf_regnames_i386 (void)
{
  dwarf_regnames = dwarf_regnames_i386;
  dwarf_regnames_count = ARRAY_SIZE (dwarf_regnames_i386);
}

static const char *const dwarf_regnames_x86_64[] =
{
  "rax", "rdx", "rcx", "rbx",
  "rsi", "rdi", "rbp", "rsp",
  "r8",  "r9",  "r10", "r11",
  "r12", "r13", "r14", "r15",
  "rip",
  "xmm0",  "xmm1",  "xmm2",  "xmm3",
  "xmm4",  "xmm5",  "xmm6",  "xmm7",
  "xmm8",  "xmm9",  "xmm10", "xmm11",
  "xmm12", "xmm13", "xmm14", "xmm15",
  "st0", "st1", "st2", "st3",
  "st4", "st5", "st6", "st7",
  "mm0", "mm1", "mm2", "mm3",
  "mm4", "mm5", "mm6", "mm7",
  "rflags",
  "es", "cs", "ss", "ds", "fs", "gs", NULL, NULL,
  "fs.base", "gs.base", NULL, NULL,
  "tr", "ldtr",
  "mxcsr", "fcw", "fsw"
};

void
init_dwarf_regnames_x86_64 (void)
{
  dwarf_regnames = dwarf_regnames_x86_64;
  dwarf_regnames_count = ARRAY_SIZE (dwarf_regnames_x86_64);
}

void
init_dwarf_regnames (unsigned int e_machine)
{
  switch (e_machine)
    {
    case EM_386:
    case EM_486:
      init_dwarf_regnames_i386 ();
      break;

    case EM_X86_64:
    case EM_L1OM:
    case EM_K1OM:
      init_dwarf_regnames_x86_64 ();
      break;

    default:
      break;
    }
}

static const char *
regname (unsigned int regno, int row)
{
  static char reg[64];
  if (dwarf_regnames
      && regno < dwarf_regnames_count
      && dwarf_regnames [regno] != NULL)
    {
      if (row)
	return dwarf_regnames [regno];
      snprintf (reg, sizeof (reg), "r%d (%s)", regno,
		dwarf_regnames [regno]);
    }
  else
    snprintf (reg, sizeof (reg), "r%d", regno);
  return reg;
}

static void
frame_display_row (Frame_Chunk *fc, int *need_col_headers, int *max_regs)
{
  int r;
  char tmp[100];

  if (*max_regs < fc->ncols)
    *max_regs = fc->ncols;

  if (*need_col_headers)
    {
      static const char *sloc = "   LOC";

      *need_col_headers = 0;

      FJALAR_DPRINTF ("%-*s CFA      ", eh_addr_size * 2, sloc);

      for (r = 0; r < *max_regs; r++)
	if (fc->col_type[r] != DW_CFA_unreferenced)
	  {
	    if (r == fc->ra)
	      FJALAR_DPRINTF ("ra   ");
	    else
	      FJALAR_DPRINTF ("%-5s ", regname (r,1));
	  }

      FJALAR_DPRINTF ("\n");
    }

  FJALAR_DPRINTF ("%0*lx ", eh_addr_size * 2, fc->pc_begin);
  if (fc->cfa_exp)
    VG_(strcpy) (tmp, "exp");
  else
    sprintf (tmp, "%s%+d", regname (fc->cfa_reg, 1), fc->cfa_offset);
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
	    case DW_CFA_val_offset:
	      sprintf (tmp, "v%+d", fc->col_offset[r]);
	      break;
	    case DW_CFA_register:
	      sprintf (tmp, "%s", regname (fc->col_offset[r], 0));
	      break;
	    case DW_CFA_expression:
	      VG_(strcpy) (tmp, "exp");
	      break;
	    case DW_CFA_val_expression:
	      VG_(strcpy) (tmp, "vexp");
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

#define GET(N)  byte_get (start, N); start += N
#define ULEB()	read_uleb128 (start, & length_return); start += length_return
#define SLEB()	read_sleb128 (start, & length_return); start += length_return

int
display_debug_frames (Elf_Internal_Shdr *section, unsigned char *start,
              FILE *file ATTRIBUTE_UNUSED)
{
  unsigned char *end = start + section->sh_size;
  unsigned char *section_start = start;
  Frame_Chunk *chunks = 0;
  Frame_Chunk *remembered_state = 0;
  Frame_Chunk *rs;
  int is_eh = (VG_(strcmp) (SECTION_NAME (section), ".eh_frame") == 0);
  int length_return;
  int max_regs = 0;
  const char *bad_reg = _("bad register: ");
  int saved_eh_addr_size = eh_addr_size;

  FJALAR_DPRINTF (_("Contents of the %s section:\n"), SECTION_NAME (section));

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
      int encoded_ptr_size = saved_eh_addr_size;
      int offset_size;
      int initial_length_size;

      saved_start = start;
      length = byte_get (start, 4); start += 4;

      if (length == 0)
	{
	  FJALAR_DPRINTF ("\n%08lx ZERO terminator\n\n",
		    (unsigned long)(saved_start - section_start));
	  continue;
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
      if (block_end > end)
	{
	  warn ("Invalid length %#08lx in FDE at %#08lx\n",
		length, (unsigned long)(saved_start - section_start));
	  block_end = end;
	}
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

	  if (VG_(strcmp) (fc->augmentation, "eh") == 0)
	    start += eh_addr_size;

	  if (version >= 4)
	    {
	      fc->ptr_size = GET (1);
	      fc->segment_size = GET (1);
	      eh_addr_size = fc->ptr_size;
	    }
	  else
	    {
	      fc->ptr_size = eh_addr_size;
	      fc->segment_size = 0;
	    }
	  fc->code_factor = ULEB ();
	  fc->data_factor = SLEB ();
	  if (version == 1)
	    {
	      fc->ra = GET (1);
	    }
	  else
	    {
	      fc->ra = ULEB ();
	    }

	  if (fc->augmentation[0] == 'z')
	    {
	      augmentation_data_len = ULEB ();
	      augmentation_data = start;
	      start += augmentation_data_len;
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
	      if (version >= 4)
		{
		  FJALAR_DPRINTF ("  Pointer Size:          %u\n", fc->ptr_size);
		  FJALAR_DPRINTF ("  Segment Size:          %u\n", fc->segment_size);
		}
	      FJALAR_DPRINTF ("  Code alignment factor: %u\n", fc->code_factor);
	      FJALAR_DPRINTF ("  Data alignment factor: %d\n", fc->data_factor);
	      FJALAR_DPRINTF ("  Return address column: %d\n", fc->ra);

	      if (augmentation_data_len)
		{
		  unsigned long i;
		  FJALAR_DPRINTF ("  Augmentation data:    ");
		  for (i = 0; i < augmentation_data_len; ++i)
		    FJALAR_DPRINTF (" %02x", augmentation_data[i]);
	      FJALAR_DPRINTF ("\n");
		}
	      FJALAR_DPRINTF ("\n");
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
		  else if (*p == 'S')
		    ;
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
      unsigned long segment_selector;

	  fc = & fde_fc;
	  VG_(memset) (fc, 0, sizeof (Frame_Chunk));

	  look_for = is_eh ? start - 4 - cie_id : section_start + cie_id;

	  for (cie = chunks; cie ; cie = cie->next)
	    if (cie->chunk_start == look_for)
	      break;

	  if (!cie)
	    {
	      warn ("Invalid CIE pointer %#08lx in FDE at %#08lx\n",
		    cie_id, saved_start);
	      start = block_end;
	      fc->ncols = 0;
	      fc->col_type = (short int *) xmalloc (sizeof (short int));
	      fc->col_offset = (int *) xmalloc (sizeof (int));
	      frame_need_space (fc, max_regs - 1);
	      cie = fc;
	      fc->augmentation = "";
	      fc->fde_encoding = 0;
          fc->ptr_size = eh_addr_size;
          fc->segment_size = 0;
	    }
	  else
	    {
	      fc->ncols = cie->ncols;
	      fc->col_type = (short int *) xmalloc (fc->ncols * sizeof (short int));
	      fc->col_offset = (int *) xmalloc (fc->ncols * sizeof (int));
	      VG_(memcpy) (fc->col_type, cie->col_type, fc->ncols * sizeof (short int));
	      VG_(memcpy) (fc->col_offset, cie->col_offset, fc->ncols * sizeof (int));
	      fc->augmentation = cie->augmentation;
          fc->ptr_size = cie->ptr_size;
          eh_addr_size = cie->ptr_size;
          fc->segment_size = cie->segment_size;
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

	  segment_selector = 0;
	  if (fc->segment_size)
	    {
	      segment_selector = byte_get (start, fc->segment_size);
	      start += fc->segment_size;
	    }
	  fc->pc_begin = get_encoded_value (start, fc->fde_encoding, section->sh_addr, section_start);
	  start += encoded_ptr_size;
	  fc->pc_range = byte_get (start, encoded_ptr_size);
	  start += encoded_ptr_size;

	  if (cie->augmentation[0] == 'z')
	    {
	      augmentation_data_len = ULEB ();
	      augmentation_data = start;
	      start += augmentation_data_len;
	    }
	  FJALAR_DPRINTF (")\n");


	  // RUDD - Harvesting Debug_Frame data
          df = VG_(calloc)("dwarf.c: display_debug_frame", sizeof(debug_frame), 1);
	  df->begin = fc->pc_begin;
	  df->end = fc->pc_begin + fc->pc_range;
	  df->next = 0;
	  harvest_debug_frame_entry(df);



	  FJALAR_DPRINTF ("\n%08lx %08lx %08lx FDE cie=%08lx pc=",
		  (unsigned long)(saved_start - section_start), length, cie_id,
		  (unsigned long)(cie->chunk_start - section_start));
	  if (fc->segment_size)
	    FJALAR_DPRINTF ("%04lx:", segment_selector);
	  FJALAR_DPRINTF ("%08lx..%08lx\n", fc->pc_begin, fc->pc_begin + fc->pc_range);
	  if (! do_debug_frames_interp && augmentation_data_len)
	    {
	      unsigned long i;
	      FJALAR_DPRINTF ("  Augmentation data:    ");
	      for (i = 0; i < augmentation_data_len; ++i)
	        FJALAR_DPRINTF (" %02x", augmentation_data[i]);
	      FJALAR_DPRINTF ("\n");
	      FJALAR_DPRINTF ("\n");
	    }
	}

      /* At this point, fc is the current chunk, cie (if any) is set, and
	 we're about to interpret instructions for the chunk.  */
      /* ??? At present we need to do this always, since this sizes the
	 fc->col_type and fc->col_offset arrays, which we write into always.
	 We should probably split the interpreted and non-interpreted bits
	 into two different routines, since there's so much that doesn't
	 really overlap between them.  */
      if (1 || do_debug_frames_interp)
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
		  ULEB ();
		  if (frame_need_space (fc, opa) >= 0)
		    fc->col_type[opa] = DW_CFA_undefined;
		  break;
		case DW_CFA_restore:
		  if (frame_need_space (fc, opa) >= 0)
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
		case DW_CFA_val_offset:
		  reg = ULEB (); ULEB ();
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_restore_extended:
		  reg = ULEB ();
		  frame_need_space (fc, reg);
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_undefined:
		  reg = ULEB ();
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_same_value:
		  reg = ULEB ();
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_register:
		  reg = ULEB (); ULEB ();
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_def_cfa:
		  ULEB (); ULEB ();
		  break;
		case DW_CFA_def_cfa_register:
		  ULEB ();
		  break;
		case DW_CFA_def_cfa_offset:
		  ULEB ();
		  break;
		case DW_CFA_def_cfa_expression:
		  temp = ULEB ();
		  start += temp;
		  break;
		case DW_CFA_expression:
		case DW_CFA_val_expression:
		  reg = ULEB ();
		  temp = ULEB ();
		  start += temp;
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_offset_extended_sf:
		case DW_CFA_val_offset_sf:
		  reg = ULEB (); SLEB ();
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
		case DW_CFA_def_cfa_sf:
		  ULEB (); SLEB ();
		  break;
		case DW_CFA_def_cfa_offset_sf:
		  SLEB ();
		  break;
		case DW_CFA_MIPS_advance_loc8:
		  start += 8;
		  break;
		case DW_CFA_GNU_args_size:
		  ULEB ();
		  break;
		case DW_CFA_GNU_negative_offset_extended:
		  reg = ULEB (); ULEB ();
		  if (frame_need_space (fc, reg) >= 0)
		    fc->col_type[reg] = DW_CFA_undefined;
		  break;
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
	  dwarf_vma vma;
      const char *reg_prefix = "";

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
	      roffs = ULEB ();
	      if (opa >= (unsigned int) fc->ncols)
		    reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		    FJALAR_DPRINTF ("  DW_CFA_offset: %s%s at cfa%+ld\n",
			reg_prefix, regname (opa, 0),
	        roffs * fc->data_factor);
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[opa] = DW_CFA_offset;
	      fc->col_offset[opa] = roffs * fc->data_factor;
		}
	      break;

	    case DW_CFA_restore:
	      if (opa >= (unsigned int) cie->ncols
		  || opa >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_restore: %s%s\n",
			reg_prefix, regname (opa, 0));
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[opa] = cie->col_type[opa];
	      fc->col_offset[opa] = cie->col_offset[opa];
		  if (do_debug_frames_interp
		      && fc->col_type[opa] == DW_CFA_unreferenced)
		    fc->col_type[opa] = DW_CFA_undefined;
		}
	      break;

	    case DW_CFA_set_loc:
	      vma = get_encoded_value (start, fc->fde_encoding, section->sh_addr, section_start);
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
	      reg = ULEB ();
	      roffs = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_offset_extended: %s%s at cfa%+ld\n",
			reg_prefix, regname (reg, 0),
			roffs * fc->data_factor);
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[reg] = DW_CFA_offset;
	      fc->col_offset[reg] = roffs * fc->data_factor;
		}
	      break;

	    case DW_CFA_val_offset:
	      reg = ULEB ();
	      roffs = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		 reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_val_offset: %s%s at cfa%+ld\n",
			reg_prefix, regname (reg, 0),
			roffs * fc->data_factor);
	      if (*reg_prefix == '\0')
		{
		  fc->col_type[reg] = DW_CFA_val_offset;
		  fc->col_offset[reg] = roffs * fc->data_factor;
		}
	      break;

	    case DW_CFA_restore_extended:
	      reg = ULEB ();
	      if (reg >= (unsigned int) cie->ncols
		  || reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_restore_extended: %s%s\n",
			reg_prefix, regname (reg, 0));
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[reg] = cie->col_type[reg];
	      fc->col_offset[reg] = cie->col_offset[reg];
		}
	      break;

	    case DW_CFA_undefined:
	      reg = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_undefined: %s%s\n",
			reg_prefix, regname (reg, 0));
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[reg] = DW_CFA_undefined;
	      fc->col_offset[reg] = 0;
		}
	      break;

	    case DW_CFA_same_value:
	      reg = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_same_value: %s%s\n",
			reg_prefix, regname (reg, 0));
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[reg] = DW_CFA_same_value;
	      fc->col_offset[reg] = 0;
		}
	      break;

	    case DW_CFA_register:
	      reg = ULEB ();
	      roffs = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		{
		  FJALAR_DPRINTF ("  DW_CFA_register: %s%s in ",
			  reg_prefix, regname (reg, 0));
		  puts (regname (roffs, 0));
		}
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[reg] = DW_CFA_register;
	      fc->col_offset[reg] = roffs;
		}
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
	      if (rs)
		{
	      remembered_state = rs->next;
	      frame_need_space (fc, rs->ncols-1);
	      VG_(memcpy) (fc->col_type, rs->col_type, rs->ncols);
	      VG_(memcpy) (fc->col_offset, rs->col_offset, rs->ncols * sizeof (int));
	      VG_(free) (rs->col_type);
	      VG_(free) (rs->col_offset);
	      VG_(free) (rs);
         }
	      else if (do_debug_frames_interp)
		FJALAR_DPRINTF ("Mismatched DW_CFA_restore_state\n");
	      break;

	    case DW_CFA_def_cfa:
	      fc->cfa_reg = ULEB ();
	      fc->cfa_offset = ULEB ();
	      fc->cfa_exp = 0;
	      if (! do_debug_frames_interp)
		FJALAR_DPRINTF ("  DW_CFA_def_cfa: %s ofs %d\n",
			regname (fc->cfa_reg, 0), fc->cfa_offset);
	      break;

	    case DW_CFA_def_cfa_register:
	      fc->cfa_reg = ULEB ();
	      fc->cfa_exp = 0;
	      if (! do_debug_frames_interp)
		FJALAR_DPRINTF ("  DW_CFA_def_cfa_register: %s\n",
			regname (fc->cfa_reg, 0));
	      break;

	    case DW_CFA_def_cfa_offset:
	      fc->cfa_offset = ULEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_def_cfa_offset: %d\n", fc->cfa_offset);
	      break;

	    case DW_CFA_nop:
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_nop\n");
	      break;

	    case DW_CFA_def_cfa_expression:
	      ul = ULEB ();
	      if (! do_debug_frames_interp)
		{
		  FJALAR_DPRINTF ("  DW_CFA_def_cfa_expression (");
		  decode_location_expression (start, eh_addr_size, 0, -1, ul, 0, PASS_2, DO_NOT_HARVEST, 0, 0);
		  FJALAR_DPRINTF (")\n");
		}
	      fc->cfa_exp = 1;
	      start += ul;
	      break;

	    case DW_CFA_expression:
	      reg = ULEB ();
	      ul = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		{
		  FJALAR_DPRINTF ("  DW_CFA_expression: r%ld (", reg);
		  decode_location_expression (start, eh_addr_size, 0, -1, ul, 0, PASS_2, DO_NOT_HARVEST, 0, 0);
		  FJALAR_DPRINTF (")\n");
		}
	      if (*reg_prefix == '\0')
	      fc->col_type[reg] = DW_CFA_expression;
	      start += ul;
	      break;

	    case DW_CFA_val_expression:
	      reg = ULEB ();
	      ul = ULEB ();
	      if (reg >= (unsigned int) fc->ncols)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		{
		  FJALAR_DPRINTF ("  DW_CFA_val_expression: %s%s (",
			  reg_prefix, regname (reg, 0));
		  decode_location_expression (start, eh_addr_size, 0, -1, ul, 0, PASS_2, DO_NOT_HARVEST, 0, 0);
		  FJALAR_DPRINTF (")\n");
		}
	      if (*reg_prefix == '\0')
		fc->col_type[reg] = DW_CFA_val_expression;
	      start += ul;
	      break;

	    case DW_CFA_offset_extended_sf:
	      reg = ULEB ();
	      l = SLEB ();
	      if (frame_need_space (fc, reg) < 0)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_offset_extended_sf: %s%s at cfa%+ld\n",
			reg_prefix, regname (reg, 0),
			l * fc->data_factor);
          if (*reg_prefix == '\0')
          {    
	      fc->col_type[reg] = DW_CFA_offset;
	      fc->col_offset[reg] = l * fc->data_factor;
		  }
	      break;

	    case DW_CFA_val_offset_sf:
	      reg = ULEB ();
	      l = SLEB ();
	      if (frame_need_space (fc, reg) < 0)
		 reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_val_offset_sf: %s%s at cfa%+ld\n",
			reg_prefix, regname (reg, 0),
			l * fc->data_factor);
	      if (*reg_prefix == '\0')
		{
		  fc->col_type[reg] = DW_CFA_val_offset;
		  fc->col_offset[reg] = l * fc->data_factor;
		}
	      break;

	    case DW_CFA_def_cfa_sf:
	      fc->cfa_reg = ULEB ();
	      fc->cfa_offset = SLEB ();
	      fc->cfa_offset = fc->cfa_offset * fc->data_factor;
	      fc->cfa_exp = 0;
	      if (! do_debug_frames_interp)
		FJALAR_DPRINTF ("  DW_CFA_def_cfa_sf: %s ofs %d\n",
			regname (fc->cfa_reg, 0), fc->cfa_offset);
	      break;

	    case DW_CFA_def_cfa_offset_sf:
	      fc->cfa_offset = SLEB ();
	      fc->cfa_offset = fc->cfa_offset * fc->data_factor;
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
	      ul = ULEB ();
	      if (! do_debug_frames_interp)
	 FJALAR_DPRINTF ("  DW_CFA_GNU_args_size: %ld\n", ul);
	      break;

	    case DW_CFA_GNU_negative_offset_extended:
	      reg = ULEB ();
	      l = - ULEB ();
	      if (frame_need_space (fc, reg) < 0)
		reg_prefix = bad_reg;
	      if (! do_debug_frames_interp || *reg_prefix != '\0')
		FJALAR_DPRINTF ("  DW_CFA_GNU_negative_offset_extended: %s%s at cfa%+ld\n",
			reg_prefix, regname (reg, 0),
			l * fc->data_factor);
	      if (*reg_prefix == '\0')
		{
	      fc->col_type[reg] = DW_CFA_offset;
	      fc->col_offset[reg] = l * fc->data_factor;
		}
	      break;

	    default:
	      if (op >= DW_CFA_lo_user && op <= DW_CFA_hi_user)
		FJALAR_DPRINTF (_("  DW_CFA_??? (User defined call frame op: %#x)\n"), op);
	      else
		warn (_("unsupported or unknown Dwarf Call Frame Instruction number: %#x\n"), op);
	      start = block_end;
	    }
	}

      if (do_debug_frames_interp)
	frame_display_row (fc, &need_col_headers, &max_regs);

      start = block_end;
      eh_addr_size = saved_eh_addr_size;
    }

  FJALAR_DPRINTF ("\n");

  return 1;
}

#undef GET
#undef ULEB
#undef SLEB

int
display_debug_not_supported (Elf_Internal_Shdr *section, unsigned char *start ATTRIBUTE_UNUSED,
                             FILE *file ATTRIBUTE_UNUSED)
{
  FJALAR_DPRINTF (_("Displaying the debug contents of section %s is not yet supported.\n"),
	    SECTION_NAME (section));

  return 1;
}
