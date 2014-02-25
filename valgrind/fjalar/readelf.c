/* readelf.c -- display contents of an ELF format file
   Copyright 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007,
   2008, 2009, 2010, 2011, 2012
   Free Software Foundation, Inc.

   Originally developed by Eric Youngdale <eric@andante.jic.com>
   Modifications by Nick Clifton <nickc@redhat.com>

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

/* The following headers use the elf/reloc-macros.h file to
   automatically generate relocation recognition functions
   such as elf_mips_reloc_type()  */

#define RELOC_MACROS_GEN_FUNC

#include "elf/i386.h"
#include "elf/ia64.h"
#include "elf/x86-64.h"

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
static bfd_vma dynamic_info[DT_JMPREL + 1];
static bfd_vma version_info[16];
long loadaddr = 0;
Elf_Internal_Ehdr elf_header;
Elf_Internal_Shdr *section_headers;
Elf_Internal_Dyn *dynamic_section;
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

int eh_addr_size;
int is_32bit_elf;

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
int debug_line_pointer_size;
PTR get_data(PTR, FILE *, long, size_t, const char *);

/* Forward declarations for dumb compilers.  */

int slurp_rela_relocs(FILE *, unsigned long, unsigned long,
                      Elf_Internal_Rela **, unsigned long *);
int slurp_rel_relocs (FILE * file, unsigned long rel_offset, unsigned long rel_size,
                      Elf_Internal_Rela ** relsp, unsigned long * nrelsp);
Elf_Internal_Sym *get_32bit_elf_symbols(FILE *, Elf_Internal_Shdr *);
Elf_Internal_Sym *get_64bit_elf_symbols(FILE *, Elf_Internal_Shdr *);


/* Flag bits indicating particular types of dump.  */
#define HEX_DUMP	(1 << 0)
#define DISASS_DUMP	(1 << 1)
#define DEBUG_DUMP	(1 << 2)

typedef unsigned char dump_type;

/* A dynamic array of flags indicating which sections require dumping.  */
static dump_type *  dump_sects = NULL;
static unsigned int num_dump_sects = 0;


/* How to print a vma value.  */
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

#define UNKNOWN -1

#define DT_VERSIONTAGIDX(tag)	(DT_VERNEEDNUM - (tag))	/* Reverse order!  */

// PG - end

static void
error VPARAMS ((const char *message, ...))
{
  VA_OPEN (args, message);
  VA_FIXEDARG (args, const char *, message);

  fprintf (stderr, _("%s: Error: "), "readelf.c");
  vfprintf (stderr, message, args);
  VA_CLOSE (args);
}

static void
warn VPARAMS ((const char *message, ...))
{
  VA_OPEN (args, message);
  VA_FIXEDARG (args, const char *, message);

  fprintf (stderr, _("%s: Warning: "), "readelf.c");
  vfprintf (stderr, message, args);
  VA_CLOSE (args);
}

PTR
get_data (PTR var, FILE * file, long offset, size_t size, const char * reason)
{
  PTR mvar;

  if (size == 0)
    return NULL;

  if (fseek (file, offset, SEEK_SET))
    {
      error (_("Unable to seek to 0x%lx for %s\n"), offset, reason);
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

/* Print a VMA value.  */

static void
print_vma (bfd_vma vma, print_mode mode)
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

    case DEC_5:
      if (vma <= 99999) {
          FJALAR_DPRINTF ("%5" BFD_VMA_FMT "d", vma);
	      break;
      }
      /* drop through */

	case PREFIX_HEX:
	  FJALAR_DPRINTF ("0x");
	  /* drop through */

	case HEX:
      FJALAR_DPRINTF ("%" BFD_VMA_FMT "x", vma);
	  break;

	case DEC:
      FJALAR_DPRINTF ("%" BFD_VMA_FMT "d", vma);
	  break;

	case UNSIGNED:
      FJALAR_DPRINTF ("%" BFD_VMA_FMT "u", vma);
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
print_symbol (int width, const char * symbol)
{
  if (do_wide)
    FJALAR_DPRINTF ("%s", symbol);
  else if (width < 0)
    FJALAR_DPRINTF ("%-*.*s", width, width, symbol);
  else
    FJALAR_DPRINTF ("%-.*s", width, symbol);
}

/* Guess the relocation size commonly used by the specific machines.  */

static int
guess_is_rela (unsigned int e_machine)
{
  switch (e_machine)
    {
      /* Targets that use REL relocations.  */
    case EM_386:
    case EM_486:
    case EM_960:
    case EM_ARM:
    case EM_D10V:
    case EM_CYGNUS_D10V:
    case EM_DLX:
    case EM_MIPS:
    case EM_MIPS_RS3_LE:
    case EM_CYGNUS_M32R:
    case EM_OPENRISC:
    case EM_OR32:
    case EM_SCORE:
    case EM_XGATE:
      return FALSE;

      /* Targets that use RELA relocations.  */
    case EM_68K:
    case EM_860:
    case EM_AARCH64:
    case EM_ADAPTEVA_EPIPHANY:
    case EM_ALPHA:
    case EM_ALTERA_NIOS2:
    case EM_AVR:
    case EM_AVR_OLD:
    case EM_BLACKFIN:
    case EM_CR16:
    case EM_CRIS:
    case EM_CRX:
    case EM_D30V:
    case EM_CYGNUS_D30V:
    case EM_FR30:
    case EM_CYGNUS_FR30:
    case EM_CYGNUS_FRV:
    case EM_H8S:
    case EM_H8_300:
    case EM_H8_300H:
    case EM_IA_64:
    case EM_IP2K:
    case EM_IP2K_OLD:
    case EM_IQ2000:
    case EM_LATTICEMICO32:
    case EM_M32C_OLD:
    case EM_M32C:
    case EM_M32R:
    case EM_MCORE:
    case EM_CYGNUS_MEP:
    case EM_MMIX:
    case EM_MN10200:
    case EM_CYGNUS_MN10200:
    case EM_MN10300:
    case EM_CYGNUS_MN10300:
    case EM_MOXIE:
    case EM_MSP430:
    case EM_MSP430_OLD:
    case EM_MT:
    case EM_NIOS32:
    case EM_PPC64:
    case EM_PPC:
    case EM_RL78:
    case EM_RX:
    case EM_S390:
    case EM_S390_OLD:
    case EM_SH:
    case EM_SPARC:
    case EM_SPARC32PLUS:
    case EM_SPARCV9:
    case EM_SPU:
    case EM_TI_C6000:
    case EM_TILEGX:
    case EM_TILEPRO:
    case EM_V850:
    case EM_CYGNUS_V850:
    case EM_VAX:
    case EM_X86_64:
    case EM_L1OM:
    case EM_K1OM:
    case EM_XSTORMY16:
    case EM_XTENSA:
    case EM_XTENSA_OLD:
    case EM_MICROBLAZE:
    case EM_MICROBLAZE_OLD:
      return TRUE;

    case EM_68HC05:
    case EM_68HC08:
    case EM_68HC11:
    case EM_68HC16:
    case EM_FX66:
    case EM_ME16:
    case EM_MMA:
    case EM_NCPU:
    case EM_NDR1:
    case EM_PCP:
    case EM_ST100:
    case EM_ST19:
    case EM_ST7:
    case EM_ST9PLUS:
    case EM_STARCORE:
    case EM_SVX:
    case EM_TINYJ:
    default:
      warn (_("Don't know about relocations on this machine architecture\n"));
      return FALSE;
    }
}

int
slurp_rela_relocs (FILE * file, unsigned long rel_offset, unsigned long rel_size,
                   Elf_Internal_Rela ** relasp, unsigned long * nrelasp)
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
	  relas[i].r_offset = BYTE_GET (erelas[i].r_offset);
	  relas[i].r_info   = BYTE_GET (erelas[i].r_info);
	  relas[i].r_addend = BYTE_GET_SIGNED (erelas[i].r_addend);

	  /* The #ifdef BFD64 below is to prevent a compile time
	     warning.  We know that if we do not have a 64 bit data
	     type that we will never execute this code anyway.  */
#ifdef BFD64
	  if (elf_header.e_machine == EM_MIPS
	      && elf_header.e_ident[EI_DATA] != ELFDATA2MSB)
	    {
	      /* In little-endian objects, r_info isn't really a
		 64-bit little-endian value: it has a 32-bit
		 little-endian symbol index followed by four
		 individual byte fields.  Reorder INFO
		 accordingly.  */
	      bfd_vma inf = relas[i].r_info;
	      inf = (((inf & 0xffffffff) << 32)
		      | ((inf >> 56) & 0xff)
		      | ((inf >> 40) & 0xff00)
		      | ((inf >> 24) & 0xff0000)
		      | ((inf >> 8) & 0xff000000));
	      relas[i].r_info = inf;
	    }
#endif /* BFD64 */
	}

      VG_(free) (erelas);
    }
  *relasp = relas;
  *nrelasp = nrelas;
  return 1;
}

int
slurp_rel_relocs (FILE * file, unsigned long rel_offset, unsigned long rel_size,
                  Elf_Internal_Rela ** relsp, unsigned long * nrelsp)
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
	  error(_("out of memory parsing relocs\n"));
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
	  error(_("out of memory parsing relocs\n"));
	  return 0;
	}

      for (i = 0; i < nrels; i++)
	{
	  rels[i].r_offset = BYTE_GET (erels[i].r_offset);
	  rels[i].r_info   = BYTE_GET (erels[i].r_info);
	  rels[i].r_addend = 0;

	  /* The #ifdef BFD64 below is to prevent a compile time
	     warning.  We know that if we do not have a 64 bit data
	     type that we will never execute this code anyway.  */
#ifdef BFD64
	  if (elf_header.e_machine == EM_MIPS
	      && elf_header.e_ident[EI_DATA] != ELFDATA2MSB)
	    {
	      /* In little-endian objects, r_info isn't really a
		 64-bit little-endian value: it has a 32-bit
		 little-endian symbol index followed by four
		 individual byte fields.  Reorder INFO
		 accordingly.  */
	      bfd_vma inf = rels[i].r_info;
	      inf = (((inf & 0xffffffff) << 32)
		     | ((inf >> 56) & 0xff)
		     | ((inf >> 40) & 0xff00)
		     | ((inf >> 24) & 0xff0000)
		     | ((inf >> 8) & 0xff000000));
	      rels[i].r_info = inf;
	    }
#endif /* BFD64 */
	}

      VG_(free) (erels);
    }
  *relsp = rels;
  *nrelsp = nrels;
  return 1;
}

/* Display the contents of the relocation data found at the specified offset.  */

static void
dump_relocations (FILE * file, unsigned long rel_offset, unsigned long rel_size,
                  Elf_Internal_Sym * symtab, unsigned long nsyms, char * strtab, int is_rela)
{
  unsigned int i;
  Elf_Internal_Rela *rels;

  if (is_rela == UNKNOWN)
    is_rela = guess_is_rela (elf_header.e_machine);

  if (is_rela)
    {
      if (!slurp_rela_relocs (file, rel_offset, rel_size, &rels, &rel_size))
	return;
    }
  else
    {
      if (!slurp_rel_relocs (file, rel_offset, rel_size, &rels, &rel_size))
	return;
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
	  FJALAR_DPRINTF ("%8.8" BFD_VMA_FMT "x  %8.8" BFD_VMA_FMT "x ", offset, info);
	}
      else
	{
	  FJALAR_DPRINTF (do_wide
		  ? "%16.16" BFD_VMA_FMT "x  %16.16" BFD_VMA_FMT "x "
		  : "%12.12" BFD_VMA_FMT "x  %12.12" BFD_VMA_FMT "x ",
		  offset, info);
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

	case EM_X86_64:
	  rtype = elf_x86_64_reloc_type (type);
	  break;
	}

      if (rtype == NULL)
 FJALAR_DPRINTF (_("unrecognized: %-7" BFD_VMA_FMT "x"), type);
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
}

static const char *
get_dynamic_type (unsigned long type)
{
  static char buff[64];

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

    case DT_TLSDESC_GOT: return "TLSDESC_GOT";
    case DT_TLSDESC_PLT: return "TLSDESC_PLT";
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
    case DT_GNU_HASH:	return "GNU_HASH";

    default:
      if ((type >= DT_LOPROC) && (type <= DT_HIPROC))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  snprintf (buff, sizeof (buff), _("Processor Specific: %lx"), type);
	}
      else if (((type >= DT_LOOS) && (type <= DT_HIOS))
	       || (elf_header.e_machine == EM_PARISC
		   && (type >= OLD_DT_LOOS) && (type <= OLD_DT_HIOS)))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  snprintf (buff, sizeof (buff), _("Operating System specific: %lx"),
		    type);
	}
      else
	snprintf (buff, sizeof (buff), _("<unknown>: %lx"), type);

      return buff;
    }
}

static const char *
get_file_type (unsigned e_type)
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
	snprintf (buff, sizeof (buff), _("Processor Specific: (%x)"), e_type);
      else if ((e_type >= ET_LOOS) && (e_type <= ET_HIOS))
	snprintf (buff, sizeof (buff), _("OS Specific: (%x)"), e_type);
      else
	snprintf (buff, sizeof (buff), _("<unknown>: %x"), e_type);
      return buff;
    }
}

static const char *
get_machine_name (unsigned e_machine)
{
  static char buff[64]; /* XXX */

  switch (e_machine)
    {
    case EM_NONE:		return _("None");
    case EM_AARCH64:		return "AArch64";
    case EM_M32:		return "WE32100";
    case EM_SPARC:		return "Sparc";
    case EM_SPU:		return "SPU";
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
    case EM_ALPHA:		return "Alpha";
    case EM_CYGNUS_D10V:
    case EM_D10V:		return "d10v";
    case EM_CYGNUS_D30V:
    case EM_D30V:		return "d30v";
    case EM_CYGNUS_M32R:
    case EM_M32R:		return "Renesas M32R (formerly Mitsubishi M32r)";
    case EM_CYGNUS_V850:
    case EM_V850:		return "Renesas V850";
    case EM_CYGNUS_MN10300:
    case EM_MN10300:		return "mn10300";
    case EM_CYGNUS_MN10200:
    case EM_MN10200:		return "mn10200";
    case EM_MOXIE:		return "Moxie";
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
    case EM_PDSP:		return "Sony DSP processor";
    case EM_PDP10:		return "Digital Equipment Corp. PDP-10";
    case EM_PDP11:		return "Digital Equipment Corp. PDP-11";
    case EM_FX66:		return "Siemens FX66 microcontroller";
    case EM_ST9PLUS:		return "STMicroelectronics ST9+ 8/16 bit microcontroller";
    case EM_ST7:		return "STMicroelectronics ST7 8-bit microcontroller";
    case EM_68HC16:		return "Motorola MC68HC16 Microcontroller";
    case EM_68HC12:		return "Motorola MC68HC12 Microcontroller";
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
    case EM_L1OM:		return "Intel L1OM";
    case EM_K1OM:		return "Intel K1OM";
    case EM_S390_OLD:
    case EM_S390:		return "IBM S/390";
    case EM_SCORE:		return "SUNPLUS S+Core";
    case EM_XSTORMY16:		return "Sanyo XStormy16 CPU core";
    case EM_OPENRISC:
    case EM_OR32:		return "OpenRISC";
    case EM_ARC_A5:		return "ARC International ARCompact processor";
    case EM_CRX:		return "National Semiconductor CRX microprocessor";
    case EM_ADAPTEVA_EPIPHANY:	return "Adapteva EPIPHANY";
    case EM_DLX:		return "OpenDLX";
    case EM_IP2K_OLD:
    case EM_IP2K:		return "Ubicom IP2xxx 8-bit microcontrollers";
    case EM_IQ2000:       	return "Vitesse IQ2000";
    case EM_XTENSA_OLD:
    case EM_XTENSA:		return "Tensilica Xtensa Processor";
    case EM_VIDEOCORE:		return "Alphamosaic VideoCore processor";
    case EM_TMM_GPP:		return "Thompson Multimedia General Purpose Processor";
    case EM_NS32K:		return "National Semiconductor 32000 series";
    case EM_TPC:		return "Tenor Network TPC processor";
    case EM_ST200:		return "STMicroelectronics ST200 microcontroller";
    case EM_MAX:		return "MAX Processor";
    case EM_CR:			return "National Semiconductor CompactRISC";
    case EM_F2MC16:		return "Fujitsu F2MC16";
    case EM_MSP430:		return "Texas Instruments msp430 microcontroller";
    case EM_LATTICEMICO32:	return "Lattice Mico32";
    case EM_M32C_OLD:
    case EM_M32C:	        return "Renesas M32c";
    case EM_MT:                 return "Morpho Techologies MT processor";
    case EM_BLACKFIN:		return "Analog Devices Blackfin";
    case EM_SE_C33:		return "S1C33 Family of Seiko Epson processors";
    case EM_SEP:		return "Sharp embedded microprocessor";
    case EM_ARCA:		return "Arca RISC microprocessor";
    case EM_UNICORE:		return "Unicore";
    case EM_EXCESS:		return "eXcess 16/32/64-bit configurable embedded CPU";
    case EM_DXP:		return "Icera Semiconductor Inc. Deep Execution Processor";
    case EM_NIOS32:		return "Altera Nios";
    case EM_ALTERA_NIOS2:	return "Altera Nios II";
    case EM_C166:
    case EM_XC16X:		return "Infineon Technologies xc16x";
    case EM_M16C:		return "Renesas M16C series microprocessors";
    case EM_DSPIC30F:		return "Microchip Technology dsPIC30F Digital Signal Controller";
    case EM_CE:			return "Freescale Communication Engine RISC core";
    case EM_TSK3000:		return "Altium TSK3000 core";
    case EM_RS08:		return "Freescale RS08 embedded processor";
    case EM_ECOG2:		return "Cyan Technology eCOG2 microprocessor";
    case EM_DSP24:		return "New Japan Radio (NJR) 24-bit DSP Processor";
    case EM_VIDEOCORE3:		return "Broadcom VideoCore III processor";
    case EM_SE_C17:		return "Seiko Epson C17 family";
    case EM_TI_C6000:		return "Texas Instruments TMS320C6000 DSP family";
    case EM_TI_C2000:		return "Texas Instruments TMS320C2000 DSP family";
    case EM_TI_C5500:		return "Texas Instruments TMS320C55x DSP family";
    case EM_MMDSP_PLUS:		return "STMicroelectronics 64bit VLIW Data Signal Processor";
    case EM_CYPRESS_M8C:	return "Cypress M8C microprocessor";
    case EM_R32C:		return "Renesas R32C series microprocessors";
    case EM_TRIMEDIA:		return "NXP Semiconductors TriMedia architecture family";
    case EM_QDSP6:		return "QUALCOMM DSP6 Processor";
    case EM_8051:		return "Intel 8051 and variants";
    case EM_STXP7X:		return "STMicroelectronics STxP7x family";
    case EM_NDS32:		return "Andes Technology compact code size embedded RISC processor family";
    case EM_ECOG1X:		return "Cyan Technology eCOG1X family";
    case EM_MAXQ30:		return "Dallas Semiconductor MAXQ30 Core microcontrollers";
    case EM_XIMO16:		return "New Japan Radio (NJR) 16-bit DSP Processor";
    case EM_MANIK:		return "M2000 Reconfigurable RISC Microprocessor";
    case EM_CRAYNV2:		return "Cray Inc. NV2 vector architecture";
    case EM_CYGNUS_MEP:         return "Toshiba MeP Media Engine";
    case EM_CR16:
    case EM_MICROBLAZE:
    case EM_MICROBLAZE_OLD:	return "Xilinx MicroBlaze";
    case EM_RL78:		return "Renesas RL78";
    case EM_RX:			return "Renesas RX";
    case EM_METAG:		return "Imagination Technologies META processor architecture";
    case EM_MCST_ELBRUS:	return "MCST Elbrus general purpose hardware architecture";
    case EM_ECOG16:		return "Cyan Technology eCOG16 family";
    case EM_ETPU:		return "Freescale Extended Time Processing Unit";
    case EM_SLE9X:		return "Infineon Technologies SLE9X core";
    case EM_AVR32:		return "Atmel Corporation 32-bit microprocessor family";
    case EM_STM8:		return "STMicroeletronics STM8 8-bit microcontroller";
    case EM_TILE64:		return "Tilera TILE64 multicore architecture family";
    case EM_TILEPRO:		return "Tilera TILEPro multicore architecture family";
    case EM_TILEGX:		return "Tilera TILE-Gx multicore architecture family";
    case EM_CUDA:		return "NVIDIA CUDA architecture";
    case EM_XGATE:		return "Motorola XGATE embedded processor";
    default:
      snprintf (buff, sizeof (buff), _("<unknown>: 0x%x"), e_machine);
      return buff;
    }
}

static char *
get_machine_flags (unsigned e_flags, unsigned e_machine)
{
  static char buf[1024];

  (void)e_flags; (void)e_machine; /* Quiet unused variable warning */
  buf[0] = '\0';
  return buf;
}

static const char *
get_osabi_name (unsigned int osabi)
{
  static char buff[32];

  switch (osabi)
    {
    case ELFOSABI_NONE:		return "UNIX - System V";
    case ELFOSABI_HPUX:		return "UNIX - HP-UX";
    case ELFOSABI_NETBSD:	return "UNIX - NetBSD";
    case ELFOSABI_GNU:  	return "UNIX - GNU";
    case ELFOSABI_SOLARIS:	return "UNIX - Solaris";
    case ELFOSABI_AIX:		return "UNIX - AIX";
    case ELFOSABI_IRIX:		return "UNIX - IRIX";
    case ELFOSABI_FREEBSD:	return "UNIX - FreeBSD";
    case ELFOSABI_TRU64:	return "UNIX - TRU64";
    case ELFOSABI_MODESTO:	return "Novell - Modesto";
    case ELFOSABI_OPENBSD:	return "UNIX - OpenBSD";
    case ELFOSABI_OPENVMS:	return "VMS - OpenVMS";
    case ELFOSABI_NSK:		return "HP - Non-Stop Kernel";
    case ELFOSABI_AROS:		return "AROS";
    case ELFOSABI_FENIXOS:	return "FenixOS";
    default:
      if (osabi >= 64)
	switch (elf_header.e_machine)
	  {
	  default:
	    break;
	  }
      snprintf (buff, sizeof (buff), _("<unknown: %x>"), osabi);
      return buff;
    }
}

static const char *
get_segment_type (unsigned long p_type)
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
    case PT_GNU_STACK:	return "GNU_STACK";
    case PT_GNU_RELRO:  return "GNU_RELRO";

    default:
      if ((p_type >= PT_LOPROC) && (p_type <= PT_HIPROC))
	{
	  const char *result;

	  switch (elf_header.e_machine)
	    {
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
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	  sprintf (buff, "LOOS+%lx", p_type - PT_LOOS);
	}
      else
	snprintf (buff, sizeof (buff), _("<unknown>: %lx"), p_type);

      return buff;
    }
}

static const char *
get_x86_64_section_type_name (unsigned int sh_type)
{
  switch (sh_type)
    {
    case SHT_X86_64_UNWIND:	return "X86_64_UNWIND";
    default:
      break;
    }
  return NULL;
}

static const char *
get_section_type_name (unsigned int sh_type)
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
    case SHT_GNU_HASH:		return "GNU_HASH";
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
	    case EM_X86_64:
	      result = get_x86_64_section_type_name (sh_type);
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
	{
	  const char * result;

	  switch (elf_header.e_machine)
	    {
	    default:
	      result = NULL;
	      break;
	    }

	  if (result != NULL)
	    return result;

	sprintf (buff, "LOOS+%x", sh_type - SHT_LOOS);
	}
      else if ((sh_type >= SHT_LOUSER) && (sh_type <= SHT_HIUSER))
	sprintf (buff, "LOUSER+%x", sh_type - SHT_LOUSER);
      else
	/* This message is probably going to be displayed in a 15
	   character wide field, so put the hex value first.  */
	snprintf (buff, sizeof (buff), _("%08x: <unknown>"), sh_type);

      return buff;
    }
}

static void
request_dump_bynumber (unsigned int section, dump_type type)
{
  if (section >= num_dump_sects)
    {
      dump_type * new_dump_sects;

      new_dump_sects = (dump_type *) VG_(calloc) ("readelf.c: request_dump", section + 1,
                                                  sizeof (* dump_sects));

      if (new_dump_sects == NULL)
	error (_("Out of memory allocating dump request table.\n"));
      else
	{
	  /* Copy current flag settings.  */
	  VG_(memcpy) (new_dump_sects, dump_sects, num_dump_sects * sizeof (* dump_sects));

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
get_elf_class (unsigned int elf_class)
{
  static char buff[32];

  switch (elf_class)
    {
    case ELFCLASSNONE: return _("none");
    case ELFCLASS32:   return "ELF32";
    case ELFCLASS64:   return "ELF64";
    default:
      snprintf (buff, sizeof (buff), _("<unknown: %x>"), elf_class);
      return buff;
    }
}

static const char *
get_data_encoding (unsigned int encoding)
{
  static char buff[32];

  switch (encoding)
    {
    case ELFDATANONE: return _("none");
    case ELFDATA2LSB: return _("2's complement, little endian");
    case ELFDATA2MSB: return _("2's complement, big endian");
    default:
      snprintf (buff, sizeof (buff), _("<unknown: %x>"), encoding);
      return buff;
    }
}

/* Decode the data held in 'elf_header'.  */

static int
process_file_header (void)
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

    init_dwarf_regnames (elf_header.e_machine);

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
get_32bit_program_headers (FILE * file, Elf_Internal_Phdr * pheaders)
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

  for (i = 0, internal = pheaders, external = phdrs;
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
get_64bit_program_headers (FILE * file, Elf_Internal_Phdr * pheaders)
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

  for (i = 0, internal = pheaders, external = phdrs;
       i < elf_header.e_phnum;
       i++, internal++, external++)
    {
      internal->p_type   = BYTE_GET (external->p_type);
      internal->p_flags  = BYTE_GET (external->p_flags);
      internal->p_offset = BYTE_GET (external->p_offset);
      internal->p_vaddr  = BYTE_GET (external->p_vaddr);
      internal->p_paddr  = BYTE_GET (external->p_paddr);
      internal->p_filesz = BYTE_GET (external->p_filesz);
      internal->p_memsz  = BYTE_GET (external->p_memsz);
      internal->p_align  = BYTE_GET (external->p_align);
    }

  VG_(free) (phdrs);

  return 1;
}

/* Returns 1 if the program headers were loaded.  */

static int
process_program_headers (FILE * file)
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

	  /* By default, assume that the .dynamic section is the first
	     section in the DYNAMIC segment.  */
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
get_32bit_section_headers (FILE * file, unsigned int num)
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
get_64bit_section_headers (FILE * file, unsigned int num)
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
      internal->sh_flags     = BYTE_GET (shdrs[i].sh_flags);
      internal->sh_addr      = BYTE_GET (shdrs[i].sh_addr);
      internal->sh_size      = BYTE_GET (shdrs[i].sh_size);
      internal->sh_entsize   = BYTE_GET (shdrs[i].sh_entsize);
      internal->sh_link      = BYTE_GET (shdrs[i].sh_link);
      internal->sh_info      = BYTE_GET (shdrs[i].sh_info);
      internal->sh_offset    = BYTE_GET (shdrs[i].sh_offset);
      internal->sh_addralign = BYTE_GET (shdrs[i].sh_addralign);
    }

  VG_(free) (shdrs);

  return 1;
}

Elf_Internal_Sym *
get_32bit_elf_symbols (FILE * file, Elf_Internal_Shdr * section)
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

  for (j = 0, psym = isyms; j < number; j++, psym++)
    {
      psym->st_name  = BYTE_GET (esyms[j].st_name);
      psym->st_value = BYTE_GET (esyms[j].st_value);
      psym->st_size  = BYTE_GET (esyms[j].st_size);
      psym->st_shndx = BYTE_GET (esyms[j].st_shndx);
      if (psym->st_shndx == (SHN_XINDEX & 0xffff) && shndx != NULL)
	psym->st_shndx
	  = byte_get ((unsigned char *) &shndx[j], sizeof (shndx[j]));
      else if (psym->st_shndx >= (SHN_LORESERVE & 0xffff))
	psym->st_shndx += SHN_LORESERVE - (SHN_LORESERVE & 0xffff);
      psym->st_info  = BYTE_GET (esyms[j].st_info);
      psym->st_other = BYTE_GET (esyms[j].st_other);
    }

  if (shndx)
    VG_(free) (shndx);
  VG_(free) (esyms);

  return isyms;
}

Elf_Internal_Sym *
get_64bit_elf_symbols (FILE * file, Elf_Internal_Shdr * section)
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

  for (j = 0, psym = isyms; j < number; j++, psym++)
    {
      psym->st_name  = BYTE_GET (esyms[j].st_name);
      psym->st_info  = BYTE_GET (esyms[j].st_info);
      psym->st_other = BYTE_GET (esyms[j].st_other);
      psym->st_shndx = BYTE_GET (esyms[j].st_shndx);

      if (psym->st_shndx == (SHN_XINDEX & 0xffff) && shndx != NULL)
	psym->st_shndx
	  = byte_get ((unsigned char *) &shndx[j], sizeof (shndx[j]));
      else if (psym->st_shndx >= (SHN_LORESERVE & 0xffff))
	psym->st_shndx += SHN_LORESERVE - (SHN_LORESERVE & 0xffff);

      psym->st_value = BYTE_GET (esyms[j].st_value);
      psym->st_size  = BYTE_GET (esyms[j].st_size);
    }

  if (shndx)
    VG_(free) (shndx);
  VG_(free) (esyms);

  return isyms;
}

static const char *
get_elf_section_flags (bfd_vma sh_flags)
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
process_section_headers (FILE * file)
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

  eh_addr_size = is_32bit_elf ? 4 : 8;

  for (i = 0, section = section_headers;
       i < elf_header.e_shnum;
       i++, section++)
    {
      const char *name = SECTION_NAME (section);

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
	    request_dump_bynumber (i, DEBUG_DUMP);
	}
      /* linkonce section to be combined with .debug_info at link time.  */
      else if ((do_debugging || do_debug_info)
	       && VG_(strncmp) (name, ".gnu.linkonce.wi.", 17) == 0)
	request_dump_bynumber (i, DEBUG_DUMP);
      else if (do_debug_frames && VG_(strcmp) (name, ".eh_frame") == 0)
	request_dump_bynumber (i, DEBUG_DUMP);
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

	  FJALAR_DPRINTF ("%2u %3u ", section->sh_link, section->sh_info);

	  if ((unsigned long) section->sh_addralign == section->sh_addralign)
	    FJALAR_DPRINTF ("%2lu\n", (unsigned long) section->sh_addralign);
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

	  FJALAR_DPRINTF ("     %2u   %3u     %lu\n",
		  section->sh_link,
		  section->sh_info,
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
process_relocs (FILE * file)
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

/* An absolute address consists of a section and an offset.  If the
   section is NULL, the offset itself is the address, otherwise, the
   address equals to LOAD_ADDRESS(section) + offset.  */

struct absaddr
  {
    unsigned short section;
    bfd_vma offset;
  };

struct ia64_unw_table_entry
  {
	struct absaddr start;
	struct absaddr end;
	struct absaddr info;
  };

struct ia64_unw_aux_info
  {
    struct ia64_unw_table_entry *table;	/* Unwind table.  */
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

static void
dump_ia64_unwind (struct ia64_unw_aux_info * aux)
{
  (void)aux; /* Quiet unused variable warning */
}

static int
slurp_ia64_unwind_table (FILE * file, struct ia64_unw_aux_info * aux, Elf_Internal_Shdr * sec)
{
  unsigned long size, nrelas, i;
  Elf_Internal_Phdr *prog_hdrs, *seg;
  struct ia64_unw_table_entry *tep;
  Elf_Internal_Shdr *relsec;
  Elf_Internal_Rela *rela, *rp;
  unsigned char *table, *tp;
  Elf_Internal_Sym *sym;
  const char *relname;
  int result;

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
  table = (unsigned char *) get_data (NULL, file, sec->sh_offset,
			     size, _("unwind table"));
  if (!table)
    return 0;

  aux->table = xmalloc (size / (3 * eh_addr_size) * sizeof (aux->table[0]));
  tep = aux->table;
  for (tp = table; tp < table + size; ++tep)
    {
      tep->start.section = SHN_UNDEF;
      tep->end.section   = SHN_UNDEF;
      tep->info.section  = SHN_UNDEF;
	  tep->start.offset = byte_get (tp, eh_addr_size); tp += eh_addr_size;
	  tep->end.offset   = byte_get (tp, eh_addr_size); tp += eh_addr_size;
	  tep->info.offset  = byte_get (tp, eh_addr_size); tp += eh_addr_size;
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

	  i = rp->r_offset / (3 * eh_addr_size);

	  switch (rp->r_offset/eh_addr_size % 3)
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

  aux->table_len = size / (3 * eh_addr_size);
  return 1;
}

static int
process_unwind (FILE * file)
{
  Elf_Internal_Shdr *sec, *unwsec = NULL, *strsec;
  unsigned long i, unwcount = 0, unwstart = 0;
  struct ia64_unw_aux_info aux;

  if (!do_unwind)
    return 1;

  if (elf_header.e_machine != EM_IA_64)
    {
      FJALAR_DPRINTF (_("\nThere are no unwind sections in this file.\n"));
      return 1;
    }

// The remainder of this function corresponds to ia64_process_unwind in binutils readelf.c

  VG_(memset) (& aux, 0, sizeof (aux));

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
      const char *suffix;
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
	  aux.info = (unsigned char *) get_data (NULL, file, sec->sh_offset,
					aux.info_size, _("unwind info"));

	  FJALAR_DPRINTF (_("\nUnwind section "));

	  if (string_table == NULL)
	    FJALAR_DPRINTF ("%d", unwsec->sh_name);
	  else
	    FJALAR_DPRINTF (_("'%s'"), SECTION_NAME (unwsec));

	  FJALAR_DPRINTF (_(" at offset 0x%lx contains %lu entries:\n"),
		  (unsigned long) unwsec->sh_offset,
		  (unsigned long) (unwsec->sh_size / (3 * eh_addr_size)));

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

static int
get_32bit_dynamic_section (FILE * file)
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
  while (*(int *) edyn[dynamic_size++].d_tag != DT_NULL)
    ;

  dynamic_section = (Elf_Internal_Dyn *)
    VG_(malloc) ("readelf.c: get_32b_dynseg", dynamic_size * sizeof (Elf_Internal_Dyn));

  if (dynamic_section == NULL)
    {
      error (_("Out of memory\n"));
      VG_(free) (edyn);
      return 0;
    }

  for (i = 0, entry = dynamic_section;
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
get_64bit_dynamic_section (FILE * file)
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

  dynamic_section = (Elf_Internal_Dyn *)
    VG_(malloc) ("readelf.c: get_64b_dynseg", dynamic_size * sizeof (Elf_Internal_Dyn));

  if (dynamic_section == NULL)
    {
      error (_("Out of memory\n"));
      VG_(free) (edyn);
      return 0;
    }

  for (i = 0, entry = dynamic_section;
       i < dynamic_size;
       i++, entry++)
    {
      entry->d_tag      = BYTE_GET (edyn[i].d_tag);
      entry->d_un.d_val = BYTE_GET (edyn[i].d_un.d_val);
    }

  VG_(free) (edyn);

  return 1;
}

static void
print_dynamic_flags (bfd_vma flags)
{
  int first = 1;

  while (flags)
    {
      bfd_vma flag;

      flag = flags & - flags;
      flags &= ~ flag;

      if (first)
        first = 0;
      else
        putc (' ', stdout);  

      switch (flag)
	{
	case DF_ORIGIN:		fputs ("ORIGIN", stdout); break;
	case DF_SYMBOLIC:	fputs ("SYMBOLIC", stdout); break;
	case DF_TEXTREL:	fputs ("TEXTREL", stdout); break;
	case DF_BIND_NOW:	fputs ("BIND_NOW", stdout); break;
	case DF_STATIC_TLS:	fputs ("STATIC_TLS", stdout); break;
	default:		fputs (_("unknown"), stdout); break;
	}
    }
  puts ("");
}

/* Parse and display the contents of the dynamic section.  */

static int
process_dynamic_section (FILE * file)
{
  Elf_Internal_Dyn *entry;
  bfd_size_type i;

  if (dynamic_size == 0)
    {
      if (do_dynamic)
 FJALAR_DPRINTF (_("\nThere is no dynamic section in this file.\n"));

      return 1;
    }

  if (is_32bit_elf)
    {
      if (! get_32bit_dynamic_section (file))
	return 0;
    }
  else if (! get_64bit_dynamic_section (file))
    return 0;

  /* Find the appropriate symbol table.  */
  if (dynamic_symbols == NULL)
    {
      for (i = 0, entry = dynamic_section;
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
      for (i = 0, entry = dynamic_section;
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

      for (i = 0, entry = dynamic_section;
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
    FJALAR_DPRINTF (_("\nDynamic section at offset 0x%lx contains %ld entries:\n"),
	    dynamic_addr, (long) dynamic_size);
  if (do_dynamic)
    FJALAR_DPRINTF (_("  Tag        Type                         Name/Value\n"));

  for (i = 0, entry = dynamic_section;
       i < dynamic_size;
       i++, entry++)
    {
      if (do_dynamic)
	{
//	  const char *dtype;

	  putchar (' ');
	  print_vma (entry->d_tag, FULL_HEX);
//	  dtype = get_dynamic_type (entry->d_tag);
	}

      switch (entry->d_tag)
	{
	case DT_FLAGS:
	  if (do_dynamic)
	    print_dynamic_flags (entry->d_un.d_val);
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

	  break;
	}
    }

  return 1;
}

static const char *
get_ver_flags (unsigned int flags)
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
process_version_sections (FILE * file)
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
	       SECTION_NAME (section), (Word) section->sh_info);

	    FJALAR_DPRINTF (_("  Addr: 0x"));
	    printf_vma (section->sh_addr);
	    FJALAR_DPRINTF (_("  Offset: %#08lx  Link: %lx (%s)\n"),
		    (Word) section->sh_offset, (Word) section->sh_link,
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
		    SECTION_NAME (section), (Word) section->sh_info);

	    FJALAR_DPRINTF (_(" Addr: 0x"));
	    printf_vma (section->sh_addr);
	    FJALAR_DPRINTF (_("  Offset: %#08lx  Link to section: %ld (%s)\n"),
		    (Word) section->sh_offset, (Word) section->sh_link,
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
		    (UWord) section->sh_offset, (UWord) section->sh_link,
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
		const char *name;

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

				  if (ivna.vna_name >= string_sec->sh_size)
				    name = _("*invalid*");
				  else
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

			      if (ivda.vda_name >= string_sec->sh_size)
				name = _("*invalid*");
			      else
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

static bfd_vma *
get_dynamic_data (FILE * file, unsigned int number)
{
  unsigned char *e_data;
  bfd_vma * i_data;

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

  i_data = (bfd_vma *) VG_(malloc) ("readelf.c: get_dyndata.2", number * sizeof (*i_data));

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
process_symbol_table (FILE * file)
{
  Elf_Internal_Shdr *section;
  unsigned char nb[4];
  unsigned char nc[4];
  bfd_vma nbuckets = 0;
  bfd_vma nchains = 0;
  bfd_vma * buckets = NULL;
  bfd_vma * chains = NULL;

  //  printf("\n\nprocess_symbol_table - do_syms: %d do_histogram: %d\n\n",
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

	  //	  printf (_("'%s'\n"), SECTION_NAME (section));

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

          //	  printf (_("\nSymbol table '%s' contains %lu entries:\n"),
          //          		  SECTION_NAME (section),
          //          		  (unsigned long) (section->sh_size / section->sh_entsize));
          //          if (is_32bit_elf)
          //	    printf (_("   Num:    Value  Size Type    Bind   Vis      Ndx Name\n"));
          //          else
          //	    printf (_("   Num:    Value          Size Type    Bind   Vis      Ndx Name\n"));

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
						(void *)(ptrdiff_t)psym->st_value);
                }
                else if (STT_FUNC == ELF_ST_TYPE (psym->st_info)) {
                  insertIntoFunctionSymbolTable(symbol_name,
						(void *)(ptrdiff_t)psym->st_value);
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
      unsigned long * lengths;
      unsigned long * counts;
      unsigned long hn;
      bfd_vma si;
      unsigned long maxlength = 0;
      unsigned long nzero_counts = 0;
      unsigned long nsyms = 0;

      FJALAR_DPRINTF (_("\nHistogram for bucket list length (total of %lu buckets):\n"),
	      (unsigned long) nbuckets);
      FJALAR_DPRINTF (_(" Length  Number     %% of total  Coverage\n"));

      lengths = (unsigned long *) VG_(calloc) ("readelf.c: process_symbol_table.1", nbuckets, sizeof (*lengths));
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

      counts = (unsigned long *) VG_(calloc) ("readelf.c: process_symbol_table.2", maxlength + 1, sizeof (*counts));
      if (counts == NULL)
	{
	  error (_("Out of memory"));
	  return 0;
	}

      for (hn = 0; hn < nbuckets; ++hn)
	++counts[lengths[hn]];

      if (nbuckets > 0)
	{
      unsigned long j;
	  FJALAR_DPRINTF ("      0  %-10lu (%5.1f%%)\n",
		  counts[0], (counts[0] * 100.0) / nbuckets);
	  for (j = 1; j <= maxlength; ++j)
	    {
	      nzero_counts += counts[j] * j;
	      FJALAR_DPRINTF ("%7lu  %-10lu (%5.1f%%)    %5.1f%%\n",
		      j, counts[j], (counts[j] * 100.0) / nbuckets,
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
process_syminfo (FILE * file ATTRIBUTE_UNUSED)
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
    FJALAR_DPRINTF (_("\nDynamic info section at offset 0x%lx contains %d entries:\n"),
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
			    + (dynamic_section
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
disassemble_section (Elf_Internal_Shdr * section, FILE * file)
{
  FJALAR_DPRINTF (_("\nAssembly dump of section %s\n"),
	  SECTION_NAME (section));

  /* XXX -- to be done --- XXX */

  return 1;
}
#endif

static int
dump_section_as_bytes (Elf_Internal_Shdr * section, FILE * file)
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

   	  for (j = 0; j < 16; j++)
	    {
	      if (j < lbytes)
	 FJALAR_DPRINTF ("%2.2x", data[j]);
	      else
	 FJALAR_DPRINTF ("  ");

	      if ((j & 3) == 3)
	 FJALAR_DPRINTF (" ");
	 }

      for (j = 0; j < lbytes; j++)
	{
	  k = data[j];
	  if (k >= ' ' && k < 0x7f)
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

/* Pre-scan the .debug_info section to record the size of address.
   When dumping the .debug_line, we use that size information, assuming
   that all compilation units have the same address size.  */
static int
prescan_debug_info (unsigned char * start)
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
  int (*prescan) PARAMS ((unsigned char *));
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
display_debug_section (Elf_Internal_Shdr * section, FILE * file)
{
  const char *name = SECTION_NAME (section);
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

  for (i = ARRAY_SIZE (debug_displays); i--;)
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

static void
process_section_contents (FILE * file)
{
  Elf_Internal_Shdr *section;
  unsigned int i;

  if (! do_dump)
    return;

  //  FJALAR_DPRINTF("process_section_contents() - before 1st for loop\n");

  /* Pre-scan the debug sections to find some debug information not
     present in some of them.  For the .debug_line, we must find out the
     size of address (specified in .debug_info and .debug_aranges).  */
  for (i = 0, section = section_headers;
       i < elf_header.e_shnum && i < num_dump_sects;
       i++, section++)
    {
      const char *name = SECTION_NAME (section);
      int j;

      if (section->sh_size == 0)
	continue;

      /* See if there is some pre-scan operation for this section.  */
      for (j = ARRAY_SIZE (debug_displays); j--;)
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
		  return;

		debug_displays[j].prescan (start);
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
          dump_section_as_bytes (section, file);
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

  return;
}

static int
process_gnu_liblist (FILE * file)
{
  (void)file; /* Quiet unused parameter warning */
  return 1;
}

static const char *
get_note_type (unsigned e_type)
{
  static char buff[64];

  if (elf_header.e_type == ET_CORE)
  switch (e_type)
    {
      case NT_AUXV:
	return _("NT_AUXV (auxiliary vector)");
      case NT_PRSTATUS:
	return _("NT_PRSTATUS (prstatus structure)");
      case NT_FPREGSET:
	return _("NT_FPREGSET (floating point registers)");
      case NT_PRPSINFO:
	return _("NT_PRPSINFO (prpsinfo structure)");
      case NT_TASKSTRUCT:
	return _("NT_TASKSTRUCT (task structure)");
      case NT_PRXFPREG:
	return _("NT_PRXFPREG (user_xfpregs structure)");
      case NT_PPC_VMX:
	return _("NT_PPC_VMX (ppc Altivec registers)");
      case NT_PPC_VSX:
	return _("NT_PPC_VSX (ppc VSX registers)");
      case NT_X86_XSTATE:
	return _("NT_X86_XSTATE (x86 XSAVE extended state)");
      case NT_S390_HIGH_GPRS:
	return _("NT_S390_HIGH_GPRS (s390 upper register halves)");
      case NT_S390_TIMER:
	return _("NT_S390_TIMER (s390 timer register)");
      case NT_S390_TODCMP:
	return _("NT_S390_TODCMP (s390 TOD comparator register)");
      case NT_S390_TODPREG:
	return _("NT_S390_TODPREG (s390 TOD programmable register)");
      case NT_S390_CTRS:
	return _("NT_S390_CTRS (s390 control registers)");
      case NT_S390_PREFIX:
	return _("NT_S390_PREFIX (s390 prefix register)");
      case NT_ARM_VFP:
	return _("NT_ARM_VFP (arm VFP registers)");
      case NT_PSTATUS:
	return _("NT_PSTATUS (pstatus structure)");
      case NT_FPREGS:
	return _("NT_FPREGS (floating point registers)");
      case NT_PSINFO:
	return _("NT_PSINFO (psinfo structure)");
      case NT_LWPSTATUS:
	return _("NT_LWPSTATUS (lwpstatus_t structure)");
      case NT_LWPSINFO:
	return _("NT_LWPSINFO (lwpsinfo_t structure)");
      case NT_WIN32PSTATUS:
	return _("NT_WIN32PSTATUS (win32_pstatus structure)");
    default:
	break;
      }
  else
    switch (e_type)
      {
      case NT_VERSION:
	return _("NT_VERSION (version)");
      case NT_ARCH:
	return _("NT_ARCH (architecture)");
      default:
	break;
      }

  snprintf (buff, sizeof (buff), _("Unknown note type: (0x%08x)"), e_type);
      return buff;
}

static const char *
get_netbsd_elfcore_note_type (unsigned e_type)
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
      snprintf (buff, sizeof (buff), _("Unknown note type: (0x%08x)"), e_type);
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

  snprintf (buff, sizeof (buff), "PT_FIRSTMACH+%d",
	    e_type - NT_NETBSDCORE_FIRSTMACH);
  return buff;
}

/* Note that by the ELF standard, the name field is already null byte
   terminated, and namesz includes the terminating null byte.
   I.E. the value of namesz for the name "FSF" is 4.

   If the value of namesz is zero, there is no name present.  */
static int
process_note (Elf_Internal_Note * pnote)
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

  FJALAR_DPRINTF ("  %-20s 0x%08lx\t%s\n",
	  pnote->namesz ? pnote->namedata : "(NONE)",
	  pnote->descsz, nt);
  return 1;
}


static int
process_corefile_note_segment (FILE * file, bfd_vma offset, bfd_vma length)
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
process_corefile_note_segments (FILE * file)
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
process_note_sections (FILE * file)
{
  Elf_Internal_Shdr * section;
  unsigned long i;
  int res = 1;

  for (i = 0, section = section_headers;
       i < elf_header.e_shnum && section != NULL;
       i++, section++)
    if (section->sh_type == SHT_NOTE)
      res &= process_corefile_note_segment (file,
					    (bfd_vma) section->sh_offset,
					    (bfd_vma) section->sh_size);

  return res;
}

static int
process_notes (FILE * file)
{
  /* If we have not been asked to display the notes then do nothing.  */
  if (! do_notes)
    return 1;

  if (elf_header.e_type != ET_CORE)
    return process_note_sections (file);

  /* No program headers means no NOTE segment.  */
  if (elf_header.e_phnum > 0)
    return process_corefile_note_segments (file);

  FJALAR_DPRINTF (_("No note segments present in the core file.\n"));
  return 1;
}

static int
process_arch_specific (FILE * file)
{
  if (! do_arch)
    return 1;

  switch (elf_header.e_machine)
    {
    default:
      break;
    }
  return 1;
}

static int
get_file_header (FILE * file)
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
	 overwriting things.  */
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
      elf_header.e_entry     = BYTE_GET (ehdr64.e_entry);
      elf_header.e_phoff     = BYTE_GET (ehdr64.e_phoff);
      elf_header.e_shoff     = BYTE_GET (ehdr64.e_shoff);
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

/* Process one ELF object file according to the command line options.
   This file may actually be stored in an archive.  The file is
   positioned at the start of the ELF object.  */

static int
process_file (const char * file_name)
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
  for (i = ARRAY_SIZE (version_info); i--;)
    version_info[i] = 0;

  for (i = ARRAY_SIZE (dynamic_info); i--;)
    dynamic_info[i] = 0;

  /* Process the file.  */
  if (show_name)
    FJALAR_DPRINTF (_("\nFile: %s\n"), file_name);

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
    process_dynamic_section (file);
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
  //    FJALAR_DPRINTF("before process_notes()\n"); // PG
  process_notes (file);
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

  if (dynamic_section)
    {
      VG_(free) (dynamic_section);
      dynamic_section = NULL;
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

int
process_elf_binary_data (const HChar* filename)
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

  // These sections are not needed to harvest data for Fjalar/Kvasir,
  // but if the user asked for --fjalar-debug-dump, display them anyway.  (markro)
  if (fjalar_debug_dump) {
      do_debug_abbrevs++;
      do_debug_aranges++;
      do_debug_macinfo++;
      do_debug_pubnames++;
      do_debug_str++;
  }

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

