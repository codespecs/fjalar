
/*--------------------------------------------------------------------*/
/*--- Reading of syms & debug info from PDB-format files.         ---*/
/*---                                                   readpdb.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.
   Spring 2008:
      derived from readelf.c and valgrind-20031012-wine/vg_symtab2.c
      derived from wine-1.0/tools/winedump/pdb.c and msc.c

   Copyright (C) 2000-2008 Julian Seward
      jseward@acm.org
   Copyright 2006 Eric Pouech (winedump/pdb.c and msc.c)
      GNU Lesser General Public License version 2.1 or later applies.
   Copyright (C) 2008 BitWagon Software LLC

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_core_basics.h"
#include "pub_core_debuginfo.h"
#include "pub_core_vki.h"          // VKI_PAGE_SIZE
#include "pub_core_libcbase.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcprint.h"
#include "pub_core_options.h"      // VG_(clo_verbosity)
#include "pub_core_xarray.h"       // keeps priv_storage.h happy
#include "pub_core_redir.h"

#include "priv_misc.h"             /* dinfo_zalloc/free/strdup */
#include "priv_d3basics.h"
#include "priv_storage.h"
#include "priv_readpdb.h"          // self


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- Biasing                                              ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

/* JRS 2009-Apr-13: Mostly this PDB reader is straightforward.  But
   the biasing is incomprehensible, and I don't claim to understand it
   at all.  There are four places where biasing is required:

   - when reading symbol addresses (DEBUG_SnarfCodeView)
   - when reading old-style line number tables (DEBUG_SnarfLinetab)
   - when reading new-style line number tables (codeview_dump_linetab2)
   - when reading FPO (stack-unwind) tables (pdb_dump)

   To complicate matters further, Wine supplies us, via the
   VG_USERREQ__LOAD_PDB_DEBUGINFO client request that initiates PDB
   reading, a value 'reloc' which, if you read 'virtual.c' in the Wine
   sources, looks a lot like a text bias value.  Yet the code below
   ignores it.

   To make future experimentation with biasing easier, here are four
   macros which give the bias to use in each of the four cases.  Be
   warned, they can and do refer to local vars in the relevant
   functions. */

/* This is the biasing arrangement in John's original patch.  I don't
   see that is makes any sense for the FPO bias to be hardwired to
   zero, but perhaps that's OK when the reloc value is also zero.
   (iow, the FPO bias should actually be 'reloc' ?) */
#define BIAS_FOR_SYMBOLS   (di->rx_map_avma)
#define BIAS_FOR_LINETAB   (di->rx_map_avma)
#define BIAS_FOR_LINETAB2  (di->text_bias)
#define BIAS_FOR_FPO       0 /* no, really */

/* This module leaks space; enable m_main's calling of
   VG_(di_discard_ALL_debuginfo)() at shutdown and run with
   --profile-heap=yes to see.  The main culprit appears to be
   di.readpe.pdr.1.  I haven't bothered to chase it further. */


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- PE/PDB definitions                                   ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

typedef  UInt   DWORD;
typedef  UShort WORD;
typedef  UChar  BYTE;


/* the following DOS and WINDOWS structures, defines and PE/PDB
 * parsing code are copied or derived from the WINE
 * project - http://www.winehq.com/
 */

/*
 * File formats definitions
 */
#define   OFFSET_OF(__c,__f)   ((int)(((char*)&(((__c*)0)->__f))-((char*)0)))
#define   WIN32_PATH_MAX 256

#pragma pack(2)
typedef struct _IMAGE_DOS_HEADER {
    unsigned short  e_magic;      /* 00: MZ Header signature */
    unsigned short  e_cblp;       /* 02: Bytes on last page of file */
    unsigned short  e_cp;         /* 04: Pages in file */
    unsigned short  e_crlc;       /* 06: Relocations */
    unsigned short  e_cparhdr;    /* 08: Size of header in paragraphs */
    unsigned short  e_minalloc;   /* 0a: Minimum extra paragraphs needed */
    unsigned short  e_maxalloc;   /* 0c: Maximum extra paragraphs needed */
    unsigned short  e_ss;         /* 0e: Initial (relative) SS value */
    unsigned short  e_sp;         /* 10: Initial SP value */
    unsigned short  e_csum;       /* 12: Checksum */
    unsigned short  e_ip;         /* 14: Initial IP value */
    unsigned short  e_cs;         /* 16: Initial (relative) CS value */
    unsigned short  e_lfarlc;     /* 18: File address of relocation table */
    unsigned short  e_ovno;       /* 1a: Overlay number */
    unsigned short  e_res[4];     /* 1c: Reserved words */
    unsigned short  e_oemid;      /* 24: OEM identifier (for e_oeminfo) */
    unsigned short  e_oeminfo;    /* 26: OEM information; e_oemid specific */
    unsigned short  e_res2[10];   /* 28: Reserved words */
    unsigned long   e_lfanew;     /* 3c: Offset to extended header */
} IMAGE_DOS_HEADER, *PIMAGE_DOS_HEADER;

#define IMAGE_DOS_SIGNATURE    0x5A4D     /* MZ   */
#define IMAGE_OS2_SIGNATURE    0x454E     /* NE   */
#define IMAGE_OS2_SIGNATURE_LE 0x454C     /* LE   */
#define IMAGE_OS2_SIGNATURE_LX 0x584C     /* LX */
#define IMAGE_VXD_SIGNATURE    0x454C     /* LE   */
#define IMAGE_NT_SIGNATURE     0x00004550 /* PE00 */

/* Subsystem Values */

#define IMAGE_SUBSYSTEM_UNKNOWN     0
#define IMAGE_SUBSYSTEM_NATIVE      1
#define IMAGE_SUBSYSTEM_WINDOWS_GUI 2  /* Windows GUI subsystem */
#define IMAGE_SUBSYSTEM_WINDOWS_CUI 3  /* Windows character subsystem*/
#define IMAGE_SUBSYSTEM_OS2_CUI     5
#define IMAGE_SUBSYSTEM_POSIX_CUI   7

typedef struct _IMAGE_FILE_HEADER {
  unsigned short  Machine;
  unsigned short  NumberOfSections;
  unsigned long   TimeDateStamp;
  unsigned long   PointerToSymbolTable;
  unsigned long   NumberOfSymbols;
  unsigned short  SizeOfOptionalHeader;
  unsigned short  Characteristics;
} IMAGE_FILE_HEADER, *PIMAGE_FILE_HEADER;

typedef struct _IMAGE_DATA_DIRECTORY {
  unsigned long VirtualAddress;
  unsigned long Size;
} IMAGE_DATA_DIRECTORY, *PIMAGE_DATA_DIRECTORY;

#define IMAGE_NUMBEROF_DIRECTORY_ENTRIES 16

typedef struct _IMAGE_OPTIONAL_HEADER {

  /* Standard fields */

  unsigned short Magic; /* 0x10b or 0x107 */ /* 0x00 */
  unsigned char  MajorLinkerVersion;
  unsigned char  MinorLinkerVersion;
  unsigned long  SizeOfCode;
  unsigned long  SizeOfInitializedData;
  unsigned long  SizeOfUninitializedData;
  unsigned long  AddressOfEntryPoint;        /* 0x10 */
  unsigned long  BaseOfCode;
  unsigned long  BaseOfData;

  /* NT additional fields */

  unsigned long ImageBase;
  unsigned long SectionAlignment;            /* 0x20 */
  unsigned long FileAlignment;
  unsigned short MajorOperatingSystemVersion;
  unsigned short MinorOperatingSystemVersion;
  unsigned short MajorImageVersion;
  unsigned short MinorImageVersion;
  unsigned short MajorSubsystemVersion;      /* 0x30 */
  unsigned short MinorSubsystemVersion;
  unsigned long Win32VersionValue;
  unsigned long SizeOfImage;
  unsigned long SizeOfHeaders;
  unsigned long CheckSum;                    /* 0x40 */
  unsigned short Subsystem;
  unsigned short DllCharacteristics;
  unsigned long SizeOfStackReserve;
  unsigned long SizeOfStackCommit;
  unsigned long SizeOfHeapReserve;           /* 0x50 */
  unsigned long SizeOfHeapCommit;
  unsigned long LoaderFlags;
  unsigned long NumberOfRvaAndSizes;
  IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES]; /* 0x60 */
  /* 0xE0 */
} IMAGE_OPTIONAL_HEADER, *PIMAGE_OPTIONAL_HEADER;

typedef struct _IMAGE_NT_HEADERS {
  unsigned long Signature; /* "PE"\0\0 */       /* 0x00 */
  IMAGE_FILE_HEADER FileHeader;                 /* 0x04 */
  IMAGE_OPTIONAL_HEADER OptionalHeader;         /* 0x18 */
} IMAGE_NT_HEADERS, *PIMAGE_NT_HEADERS;

#define IMAGE_SIZEOF_SHORT_NAME 8

typedef struct _IMAGE_SECTION_HEADER {
  unsigned char Name[IMAGE_SIZEOF_SHORT_NAME];
  union {
    unsigned long PhysicalAddress;
    unsigned long VirtualSize;
  } Misc;
  unsigned long VirtualAddress;
  unsigned long SizeOfRawData;
  unsigned long PointerToRawData;
  unsigned long PointerToRelocations;
  unsigned long PointerToLinenumbers;
  unsigned short NumberOfRelocations;
  unsigned short NumberOfLinenumbers;
  unsigned long Characteristics;
} IMAGE_SECTION_HEADER, *PIMAGE_SECTION_HEADER;

#define	IMAGE_SIZEOF_SECTION_HEADER 40

#define IMAGE_FIRST_SECTION(ntheader) \
  ((PIMAGE_SECTION_HEADER)((LPunsigned char)&((PIMAGE_NT_HEADERS)(ntheader))->OptionalHeader + \
                           ((PIMAGE_NT_HEADERS)(ntheader))->FileHeader.SizeOfOptionalHeader))

/* These defines are for the Characteristics bitfield. */
/* #define IMAGE_SCN_TYPE_REG			0x00000000 - Reserved */
/* #define IMAGE_SCN_TYPE_DSECT			0x00000001 - Reserved */
/* #define IMAGE_SCN_TYPE_NOLOAD		0x00000002 - Reserved */
/* #define IMAGE_SCN_TYPE_GROUP			0x00000004 - Reserved */
/* #define IMAGE_SCN_TYPE_NO_PAD		0x00000008 - Reserved */
/* #define IMAGE_SCN_TYPE_COPY			0x00000010 - Reserved */

#define IMAGE_SCN_CNT_CODE			0x00000020
#define IMAGE_SCN_CNT_INITIALIZED_DATA		0x00000040
#define IMAGE_SCN_CNT_UNINITIALIZED_DATA	0x00000080

#define	IMAGE_SCN_LNK_OTHER			0x00000100
#define	IMAGE_SCN_LNK_INFO			0x00000200
/* #define	IMAGE_SCN_TYPE_OVER		0x00000400 - Reserved */
#define	IMAGE_SCN_LNK_REMOVE			0x00000800
#define	IMAGE_SCN_LNK_COMDAT			0x00001000

/* 						0x00002000 - Reserved */
/* #define IMAGE_SCN_MEM_PROTECTED 		0x00004000 - Obsolete */
#define	IMAGE_SCN_MEM_FARDATA			0x00008000

/* #define IMAGE_SCN_MEM_SYSHEAP		0x00010000 - Obsolete */
#define	IMAGE_SCN_MEM_PURGEABLE			0x00020000
#define	IMAGE_SCN_MEM_16BIT			0x00020000
#define	IMAGE_SCN_MEM_LOCKED			0x00040000
#define	IMAGE_SCN_MEM_PRELOAD			0x00080000

#define	IMAGE_SCN_ALIGN_1BYTES			0x00100000
#define	IMAGE_SCN_ALIGN_2BYTES			0x00200000
#define	IMAGE_SCN_ALIGN_4BYTES			0x00300000
#define	IMAGE_SCN_ALIGN_8BYTES			0x00400000
#define	IMAGE_SCN_ALIGN_16BYTES			0x00500000  /* Default */
#define IMAGE_SCN_ALIGN_32BYTES			0x00600000
#define IMAGE_SCN_ALIGN_64BYTES			0x00700000
/* 						0x00800000 - Unused */

#define IMAGE_SCN_LNK_NRELOC_OVFL		0x01000000


#define IMAGE_SCN_MEM_DISCARDABLE		0x02000000
#define IMAGE_SCN_MEM_NOT_CACHED		0x04000000
#define IMAGE_SCN_MEM_NOT_PAGED			0x08000000
#define IMAGE_SCN_MEM_SHARED			0x10000000
#define IMAGE_SCN_MEM_EXECUTE			0x20000000
#define IMAGE_SCN_MEM_READ			0x40000000
#define IMAGE_SCN_MEM_WRITE			0x80000000

#pragma pack()

typedef struct _GUID  /* 16 bytes */
{
    unsigned int   Data1;
    unsigned short Data2;
    unsigned short Data3;
    unsigned char  Data4[ 8 ];
} GUID;

/*========================================================================
 * Process PDB file.
 */

#pragma pack(1)
typedef struct _PDB_FILE
{
    unsigned long size;
    unsigned long unknown;

} PDB_FILE, *PPDB_FILE;

// A .pdb file begins with a variable-length one-line text string
// that ends in "\r\n\032".  This is followed by a 4-byte "signature"
// ("DS\0\0" for newer files, "JG\0\0" for older files), then
// aligned up to a 4-byte boundary, then the struct below:
struct PDB_JG_HEADER
{
    //char ident[40];  // "Microsoft C/C++ program database 2.00\r\n\032"
    //unsigned long  signature;  // "JG\0\0"
    unsigned int   blocksize;  // 0x400 typical; also 0x800, 0x1000
    unsigned short freelist;
    unsigned short total_alloc;
    PDB_FILE toc;
    unsigned short toc_block[ 1 ];
};

struct PDB_DS_HEADER
{
    //char   signature[32];  // "Microsoft C/C++ MSF 7.00\r\n\032DS\0\0"
    unsigned int  block_size;
    unsigned int unknown1;
    unsigned int num_pages;
    unsigned int toc_size;
    unsigned int unknown2;
    unsigned int toc_page;
};

struct PDB_JG_TOC
{
    unsigned int  nFiles;
    PDB_FILE file[ 1 ];

};

struct PDB_DS_TOC
{
    unsigned int num_files;
    unsigned int file_size[1];
};

struct PDB_JG_ROOT
{
    unsigned int  version;
    unsigned int  TimeDateStamp;
    unsigned int  age;
    unsigned int  cbNames;
    char names[ 1 ];
};

struct PDB_DS_ROOT
{
    unsigned int version;
    unsigned int TimeDateStamp;
    unsigned int age;
    GUID guid;
    unsigned int cbNames;
    char names[1];
};

typedef struct _PDB_TYPES_OLD
{
    unsigned long  version;
    unsigned short first_index;
    unsigned short last_index;
    unsigned long  type_size;
    unsigned short file;
    unsigned short pad;

} PDB_TYPES_OLD, *PPDB_TYPES_OLD;

typedef struct _PDB_TYPES
{
    unsigned long  version;
    unsigned long  type_offset;
    unsigned long  first_index;
    unsigned long  last_index;
    unsigned long  type_size;
    unsigned short file;
    unsigned short pad;
    unsigned long  hash_size;
    unsigned long  hash_base;
    unsigned long  hash_offset;
    unsigned long  hash_len;
    unsigned long  search_offset;
    unsigned long  search_len;
    unsigned long  unknown_offset;
    unsigned long  unknown_len;

} PDB_TYPES, *PPDB_TYPES;

typedef struct _PDB_SYMBOL_RANGE
{
    unsigned short segment;
    unsigned short pad1;
    unsigned long  offset;
    unsigned long  size;
    unsigned long  characteristics;
    unsigned short index;
    unsigned short pad2;

} PDB_SYMBOL_RANGE, *PPDB_SYMBOL_RANGE;

typedef struct _PDB_SYMBOL_RANGE_EX
{
    unsigned short segment;
    unsigned short pad1;
    unsigned long  offset;
    unsigned long  size;
    unsigned long  characteristics;
    unsigned short index;
    unsigned short pad2;
    unsigned long  timestamp;
    unsigned long  unknown;

} PDB_SYMBOL_RANGE_EX, *PPDB_SYMBOL_RANGE_EX;

typedef struct _PDB_SYMBOL_FILE
{
    unsigned long  unknown1;
    PDB_SYMBOL_RANGE range;
    unsigned short flag;
    unsigned short file;
    unsigned long  symbol_size;
    unsigned long  lineno_size;
    unsigned long  unknown2;
    unsigned long  nSrcFiles;
    unsigned long  attribute;
    char filename[ 1 ];

} PDB_SYMBOL_FILE, *PPDB_SYMBOL_FILE;

typedef struct _PDB_SYMBOL_FILE_EX
{
    unsigned long  unknown1;
    PDB_SYMBOL_RANGE_EX range;
    unsigned short flag;
    unsigned short file;
    unsigned long  symbol_size;
    unsigned long  lineno_size;
    unsigned long  unknown2;
    unsigned long  nSrcFiles;
    unsigned long  attribute;
    unsigned long  reserved[ 2 ];
    char filename[ 1 ];

} PDB_SYMBOL_FILE_EX, *PPDB_SYMBOL_FILE_EX;

typedef struct _PDB_SYMBOL_SOURCE
{
    unsigned short nModules;
    unsigned short nSrcFiles;
    unsigned short table[ 1 ];

} PDB_SYMBOL_SOURCE, *PPDB_SYMBOL_SOURCE;

typedef struct _PDB_SYMBOL_IMPORT
{
    unsigned long unknown1;
    unsigned long unknown2;
    unsigned long TimeDateStamp;
    unsigned long nRequests;
    char filename[ 1 ];

} PDB_SYMBOL_IMPORT, *PPDB_SYMBOL_IMPORT;

typedef struct _PDB_SYMBOLS_OLD
{
    unsigned short hash1_file;
    unsigned short hash2_file;
    unsigned short gsym_file;
    unsigned short pad;
    unsigned long  module_size;
    unsigned long  offset_size;
    unsigned long  hash_size;
    unsigned long  srcmodule_size;

} PDB_SYMBOLS_OLD, *PPDB_SYMBOLS_OLD;

typedef struct _PDB_SYMBOLS
{
    unsigned long  signature;
    unsigned long  version;
    unsigned long  unknown;
    unsigned long  hash1_file;
    unsigned long  hash2_file;
    unsigned long  gsym_file;
    unsigned long  module_size;
    unsigned long  offset_size;
    unsigned long  hash_size;
    unsigned long  srcmodule_size;
    unsigned long  pdbimport_size;
    unsigned long  resvd[ 5 ];

} PDB_SYMBOLS, *PPDB_SYMBOLS;
#pragma pack()

/*========================================================================
 * Process CodeView symbol information.
 */

/* from wine-1.0/include/wine/mscvpdb.h */

struct p_string  /* "Pascal string": prefixed by byte containing length */
{
    unsigned char               namelen;
    char                        name[1];
};
/* The other kind of "char name[1]" is a "C++ string" terminated by '\0'.
 * "Name mangling" to encode type information often exceeds 255 bytes.
 * Instead of using a 2-byte explicit length, they save one byte of space
 * but incur a strlen().  This is justified by other code that wants
 * a "C string" [terminated by '\0'] anyway.
 */

union codeview_symbol
{
    struct
    {
        short int	        len;
        short int	        id;
    } generic;

    struct
    {
	short int	        len;
	short int	        id;
	unsigned int	        offset;
	unsigned short	        segment;
	unsigned short	        symtype;
        struct p_string         p_name;
    } data_v1;

    struct
    {
	short int	        len;
	short int	        id;
	unsigned int	        symtype;
	unsigned int	        offset;
	unsigned short	        segment;
        struct p_string         p_name;
    } data_v2;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            symtype;
        unsigned int            offset;
        unsigned short          segment;
        char                    name[1];  /* terminated by '\0' */
    } data_v3;

    struct
    {
	short int	        len;
	short int	        id;
	unsigned int	        pparent;
	unsigned int	        pend;
	unsigned int	        next;
	unsigned int	        offset;
	unsigned short	        segment;
	unsigned short	        thunk_len;
	unsigned char	        thtype;
        struct p_string         p_name;
    } thunk_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            pparent;
        unsigned int            pend;
        unsigned int            next;
        unsigned int            offset;
        unsigned short          segment;
        unsigned short          thunk_len;
        unsigned char           thtype;
        char                    name[1];  /* terminated by '\0' */
    } thunk_v3;

    struct
    {
	short int	        len;
	short int	        id;
	unsigned int	        pparent;
	unsigned int	        pend;
	unsigned int	        next;
	unsigned int	        proc_len;
	unsigned int	        debug_start;
	unsigned int	        debug_end;
	unsigned int	        offset;
	unsigned short	        segment;
	unsigned short	        proctype;
	unsigned char	        flags;
        struct p_string         p_name;
    } proc_v1;

    struct
    {
	short int	        len;
	short int	        id;
	unsigned int	        pparent;
	unsigned int	        pend;
	unsigned int	        next;
	unsigned int	        proc_len;
	unsigned int	        debug_start;
	unsigned int	        debug_end;
	unsigned int	        proctype;
	unsigned int	        offset;
	unsigned short	        segment;
	unsigned char	        flags;
        struct p_string         p_name;
    } proc_v2;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            pparent;
        unsigned int            pend;
        unsigned int            next;
        unsigned int            proc_len;
        unsigned int            debug_start;
        unsigned int            debug_end;
        unsigned int            proctype;
        unsigned int            offset;
        unsigned short          segment;
        unsigned char           flags;
        char                    name[1];  /* terminated by '\0' */
    } proc_v3;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            symtype;
        unsigned int            offset;
        unsigned short          segment;
        struct p_string         p_name;
    } public_v2;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            symtype;
        unsigned int            offset;
        unsigned short          segment;
        char                    name[1];  /* terminated by '\0' */
    } public_v3;

    struct
    {
	short int	        len;	        /* Total length of this entry */
	short int	        id;		/* Always S_BPREL_V1 */
	unsigned int	        offset;	        /* Stack offset relative to BP */
	unsigned short	        symtype;
        struct p_string         p_name;
    } stack_v1;

    struct
    {
	short int	        len;	        /* Total length of this entry */
	short int	        id;		/* Always S_BPREL_V2 */
	unsigned int	        offset;	        /* Stack offset relative to EBP */
	unsigned int	        symtype;
        struct p_string         p_name;
    } stack_v2;

    struct
    {
        short int               len;            /* Total length of this entry */
        short int               id;             /* Always S_BPREL_V3 */
        int                     offset;         /* Stack offset relative to BP */
        unsigned int            symtype;
        char                    name[1];  /* terminated by '\0' */
    } stack_v3;

    struct
    {
        short int               len;            /* Total length of this entry */
        short int               id;             /* Always S_BPREL_V3 */
        int                     offset;         /* Stack offset relative to BP */
        unsigned int            symtype;
        unsigned short          unknown;
        char                    name[1];  /* terminated by '\0' */
    } stack_xxxx_v3;

    struct
    {
	short int	        len;	        /* Total length of this entry */
	short int	        id;		/* Always S_REGISTER */
        unsigned short          type;
        unsigned short          reg;
        struct p_string         p_name;
        /* don't handle register tracking */
    } register_v1;

    struct
    {
	short int	        len;	        /* Total length of this entry */
	short int	        id;		/* Always S_REGISTER_V2 */
        unsigned int            type;           /* check whether type & reg are correct */
        unsigned short          reg;
        struct p_string         p_name;
        /* don't handle register tracking */
    } register_v2;

    struct
    {
	short int	        len;	        /* Total length of this entry */
	short int	        id;		/* Always S_REGISTER_V3 */
        unsigned int            type;           /* check whether type & reg are correct */
        unsigned short          reg;
        char                    name[1];  /* terminated by '\0' */
        /* don't handle register tracking */
    } register_v3;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            parent;
        unsigned int            end;
        unsigned int            length;
        unsigned int            offset;
        unsigned short          segment;
        struct p_string         p_name;
    } block_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            parent;
        unsigned int            end;
        unsigned int            length;
        unsigned int            offset;
        unsigned short          segment;
        char                    name[1];  /* terminated by '\0' */
    } block_v3;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            offset;
        unsigned short          segment;
        unsigned char           flags;
        struct p_string         p_name;
    } label_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            offset;
        unsigned short          segment;
        unsigned char           flags;
        char                    name[1];  /* terminated by '\0' */
    } label_v3;

    struct
    {
        short int               len;
        short int               id;
        unsigned short          type;
        unsigned short          cvalue;         /* numeric leaf */
#if 0
        struct p_string         p_name;
#endif
    } constant_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned                type;
        unsigned short          cvalue;         /* numeric leaf */
#if 0
        struct p_string         p_name;
#endif
    } constant_v2;

    struct
    {
        short int               len;
        short int               id;
        unsigned                type;
        unsigned short          cvalue;
#if 0
        char                    name[1];  /* terminated by '\0' */
#endif
    } constant_v3;

    struct
    {
        short int               len;
        short int               id;
        unsigned short          type;
        struct p_string         p_name;
    } udt_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned                type;
        struct p_string         p_name;
    } udt_v2;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            type;
        char                    name[1];  /* terminated by '\0' */
    } udt_v3;

    struct
    {
        short int               len;
        short int               id;
        char                    signature[4];
        struct p_string         p_name;
    } objname_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            unknown;
        struct p_string         p_name;
    } compiland_v1;

    struct
    {
        short int               len;
        short int               id;
        unsigned                unknown1[4];
        unsigned short          unknown2;
        struct p_string         p_name;
    } compiland_v2;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            unknown;
        char                    name[1];  /* terminated by '\0' */
    } compiland_v3;

    struct
    {
        short int               len;
        short int               id;
        unsigned int            offset;
        unsigned short          segment;
    } ssearch_v1;
};

#define S_COMPILAND_V1  0x0001
#define S_REGISTER_V1   0x0002
#define S_CONSTANT_V1   0x0003
#define S_UDT_V1        0x0004
#define S_SSEARCH_V1    0x0005
#define S_END_V1        0x0006
#define S_SKIP_V1       0x0007
#define S_CVRESERVE_V1  0x0008
#define S_OBJNAME_V1    0x0009
#define S_ENDARG_V1     0x000a
#define S_COBOLUDT_V1   0x000b
#define S_MANYREG_V1    0x000c
#define S_RETURN_V1     0x000d
#define S_ENTRYTHIS_V1  0x000e

#define S_BPREL_V1      0x0200
#define S_LDATA_V1      0x0201
#define S_GDATA_V1      0x0202
#define S_PUB_V1        0x0203
#define S_LPROC_V1      0x0204
#define S_GPROC_V1      0x0205
#define S_THUNK_V1      0x0206
#define S_BLOCK_V1      0x0207
#define S_WITH_V1       0x0208
#define S_LABEL_V1      0x0209
#define S_CEXMODEL_V1   0x020a
#define S_VFTPATH_V1    0x020b
#define S_REGREL_V1     0x020c
#define S_LTHREAD_V1    0x020d
#define S_GTHREAD_V1    0x020e

#define S_PROCREF_V1    0x0400
#define S_DATAREF_V1    0x0401
#define S_ALIGN_V1      0x0402
#define S_LPROCREF_V1   0x0403

#define S_REGISTER_V2   0x1001 /* Variants with new 32-bit type indices */
#define S_CONSTANT_V2   0x1002
#define S_UDT_V2        0x1003
#define S_COBOLUDT_V2   0x1004
#define S_MANYREG_V2    0x1005
#define S_BPREL_V2      0x1006
#define S_LDATA_V2      0x1007
#define S_GDATA_V2      0x1008
#define S_PUB_V2        0x1009
#define S_LPROC_V2      0x100a
#define S_GPROC_V2      0x100b
#define S_VFTTABLE_V2   0x100c
#define S_REGREL_V2     0x100d
#define S_LTHREAD_V2    0x100e
#define S_GTHREAD_V2    0x100f
#if 0
#define S_XXXXXXXXX_32  0x1012  /* seems linked to a function, content unknown */
#endif
#define S_COMPILAND_V2  0x1013

#define S_COMPILAND_V3  0x1101
#define S_THUNK_V3      0x1102
#define S_BLOCK_V3      0x1103
#define S_LABEL_V3      0x1105
#define S_REGISTER_V3   0x1106
#define S_CONSTANT_V3   0x1107
#define S_UDT_V3        0x1108
#define S_BPREL_V3      0x110B
#define S_LDATA_V3      0x110C
#define S_GDATA_V3      0x110D
#define S_PUB_V3        0x110E
#define S_LPROC_V3      0x110F
#define S_GPROC_V3      0x1110
#define S_BPREL_XXXX_V3 0x1111  /* not really understood, but looks like bprel... */
#define S_MSTOOL_V3     0x1116  /* compiler command line options and build information */
#define S_PUB_FUNC1_V3  0x1125  /* didn't get the difference between the two */
#define S_PUB_FUNC2_V3  0x1127


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- pdb-reading: bits and pieces                         ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

struct pdb_reader
{
   void* (*read_file)(struct pdb_reader*, unsigned, unsigned *);
   // JRS 2009-Apr-8: .uu_n_pdbimage is never used.
   UChar* pdbimage;      // image address
   SizeT  uu_n_pdbimage; // size
   union {
      struct {
         struct PDB_JG_HEADER* header;
         struct PDB_JG_TOC* toc;
      } jg;
      struct {
         struct PDB_DS_HEADER* header;
         struct PDB_DS_TOC* toc;
      } ds;
   } u;
};


static void* pdb_ds_read( struct pdb_reader* pdb,
                          unsigned* block_list,
                          unsigned  size )
{
   unsigned  blocksize, nBlocks;
   UChar* buffer;
   UInt i;

   if (!size) return NULL;

   blocksize = pdb->u.ds.header->block_size;
   nBlocks   = (size + blocksize - 1) / blocksize;
   buffer    = ML_(dinfo_zalloc)("di.readpe.pdr.1", nBlocks * blocksize);
   for (i = 0; i < nBlocks; i++)
      VG_(memcpy)( buffer + i * blocksize,
                   pdb->pdbimage + block_list[i] * blocksize,
                   blocksize );
   return buffer;
}


static void* pdb_jg_read( struct pdb_reader* pdb,
                          unsigned short* block_list,
                          int size )
{
   unsigned  blocksize, nBlocks;
   UChar* buffer;
   UInt i;
   //VG_(printf)("pdb_read %p %p %d\n", pdb, block_list, size);
   if ( !size ) return NULL;

   blocksize = pdb->u.jg.header->blocksize;
   nBlocks = (size + blocksize-1) / blocksize;
   buffer = ML_(dinfo_zalloc)("di.readpe.pjr.1", nBlocks * blocksize);
   for ( i = 0; i < nBlocks; i++ )
      VG_(memcpy)( buffer + i*blocksize,
                   pdb->pdbimage + block_list[i]*blocksize, blocksize );
   return buffer;
}


static void* find_pdb_header( UChar* pdbimage,
                              unsigned* signature )
{
   static char pdbtxt[]= "Microsoft C/C++";
   UChar* txteof = (UChar*)VG_(strchr)(pdbimage, '\032');
   if (! txteof)
      return NULL;
   if (0!=VG_(strncmp)(pdbimage, pdbtxt, -1+ sizeof(pdbtxt)))
      return NULL;

   *signature = *(unsigned*)(1+ txteof);
   return (void*)((~3& (3+ (4+ 1+ (txteof - pdbimage)))) + pdbimage);
}


static void* pdb_ds_read_file( struct pdb_reader* reader,
                               unsigned  file_number,
                               unsigned* plength )
{
   unsigned i, *block_list;
   if (!reader->u.ds.toc || file_number >= reader->u.ds.toc->num_files)
      return NULL;
   if (reader->u.ds.toc->file_size[file_number] == 0
       || reader->u.ds.toc->file_size[file_number] == 0xFFFFFFFF)
      return NULL;

   block_list
      = reader->u.ds.toc->file_size + reader->u.ds.toc->num_files;
   for (i = 0; i < file_number; i++)
      block_list += (reader->u.ds.toc->file_size[i] 
                     + reader->u.ds.header->block_size - 1)
                    /
                    reader->u.ds.header->block_size;
   if (plength)
      *plength = reader->u.ds.toc->file_size[file_number];
   return pdb_ds_read( reader, block_list,
                       reader->u.ds.toc->file_size[file_number]);
}


static void* pdb_jg_read_file( struct pdb_reader* pdb,
                               unsigned fileNr,
                               unsigned *plength )
{
   //VG_(printf)("pdb_read_file %p %d\n", pdb, fileNr);
   unsigned blocksize = pdb->u.jg.header->blocksize;
   struct PDB_JG_TOC* toc = pdb->u.jg.toc;
   unsigned i;
   unsigned short* block_list;

   if ( !toc || fileNr >= toc->nFiles )
       return NULL;

   block_list
      = (unsigned short *) &toc->file[ toc->nFiles ];
   for ( i = 0; i < fileNr; i++ )
      block_list += (toc->file[i].size + blocksize-1) / blocksize;

   if (plength)
      *plength = toc->file[fileNr].size;
   return pdb_jg_read( pdb, block_list, toc->file[fileNr].size );
}


static void pdb_ds_init( struct pdb_reader * reader,
                         UChar* pdbimage,
                         SizeT  n_pdbimage )
{
   reader->read_file     = pdb_ds_read_file;
   reader->pdbimage      = pdbimage;
   reader->uu_n_pdbimage = n_pdbimage;
   reader->u.ds.toc
      = pdb_ds_read(
           reader,
           (unsigned*)(reader->u.ds.header->block_size 
                       * reader->u.ds.header->toc_page 
                       + reader->pdbimage),
           reader->u.ds.header->toc_size
        );
}


static void pdb_jg_init( struct pdb_reader* reader,
                         char* pdbimage,
                         unsigned n_pdbimage )
{
   reader->read_file     = pdb_jg_read_file;
   reader->pdbimage      = pdbimage;
   reader->uu_n_pdbimage = n_pdbimage;
   reader->u.jg.toc = pdb_jg_read(reader,
                                  reader->u.jg.header->toc_block,
                                  reader->u.jg.header->toc.size);
}




static 
void pdb_check_root_version_and_timestamp( char* pdbname,
                                           ULong  pdbmtime,
                                           unsigned  version,
                                           UInt TimeDateStamp )
{
   switch ( version ) {
      case 19950623:      /* VC 4.0 */
      case 19950814:
      case 19960307:      /* VC 5.0 */
      case 19970604:      /* VC 6.0 */
      case 20000404:      /* VC 7.0  FIXME?? */
         break;
      default:
         if (VG_(clo_verbosity) > 1)
            VG_(message)(Vg_UserMsg,
                         "Unknown .pdb root block version %d\n", version );
   }
   if ( TimeDateStamp != pdbmtime ) {
      if (VG_(clo_verbosity) > 1)
         VG_(message)(Vg_UserMsg, 
                     "Wrong time stamp of .PDB file %s (0x%08x, 0x%08llx)\n",
                      pdbname, TimeDateStamp, pdbmtime );
   }
}


static DWORD pdb_get_file_size( struct pdb_reader* reader, unsigned idx )
{
   if (reader->read_file == pdb_jg_read_file)
      return reader->u.jg.toc->file[idx].size;
   else
      return reader->u.ds.toc->file_size[idx];
}


static void pdb_convert_types_header( PDB_TYPES *types, char* image )
{
   VG_(memset)( types, 0, sizeof(PDB_TYPES) );
   if ( !image )
      return;
   if ( *(unsigned long *)image < 19960000 ) {  /* FIXME: correct version? */
      /* Old version of the types record header */
      PDB_TYPES_OLD *old = (PDB_TYPES_OLD *)image;
      types->version     = old->version;
      types->type_offset = sizeof(PDB_TYPES_OLD);
      types->type_size   = old->type_size;
      types->first_index = old->first_index;
      types->last_index  = old->last_index;
      types->file        = old->file;
   } else {
      /* New version of the types record header */
      *types = *(PDB_TYPES *)image;
   }
}


static void pdb_convert_symbols_header( PDB_SYMBOLS *symbols,
                                        int *header_size, char* image )
{
   VG_(memset)( symbols, 0, sizeof(PDB_SYMBOLS) );
   if ( !image )
      return;
   if ( *(unsigned long *)image != 0xffffffff ) {
      /* Old version of the symbols record header */
      PDB_SYMBOLS_OLD *old     = (PDB_SYMBOLS_OLD *)image;
      symbols->version         = 0;
      symbols->module_size     = old->module_size;
      symbols->offset_size     = old->offset_size;
      symbols->hash_size       = old->hash_size;
      symbols->srcmodule_size  = old->srcmodule_size;
      symbols->pdbimport_size  = 0;
      symbols->hash1_file      = old->hash1_file;
      symbols->hash2_file      = old->hash2_file;
      symbols->gsym_file       = old->gsym_file;
      *header_size = sizeof(PDB_SYMBOLS_OLD);
   } else {
      /* New version of the symbols record header */
      *symbols = *(PDB_SYMBOLS *)image;
      *header_size = sizeof(PDB_SYMBOLS);
   }
}


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- Main stuff: reading of symbol addresses              ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

static Bool debug = False; // JRS: fixme

static ULong DEBUG_SnarfCodeView(
                DebugInfo* di,
                IMAGE_SECTION_HEADER* sectp,
                void* root, /* FIXME: better name */
                Int offset,
                Int size
             )
{
   Int    i, length;
   DiSym  vsym;
   UChar* nmstr;
   Char   symname[4096 /*WIN32_PATH_MAX*/];

   Addr  bias = BIAS_FOR_SYMBOLS;
   ULong n_syms_read = 0;

   if (debug)
      VG_(message)(Vg_UserMsg, "SnarfCodeView addr=%p offset=%d length=%d", 
                               root, offset, size );

   VG_(memset)(&vsym, 0, sizeof(vsym));  /* avoid holes */
   /*
    * Loop over the different types of records and whenever we
    * find something we are interested in, record it and move on.
    */
   for ( i = offset; i < size; i += length )
   {
      union codeview_symbol *sym = (union codeview_symbol *)((char *)root + i);

      length = sym->generic.len + 2;

      //VG_(printf)("id=%x  len=%d\n", sym->generic.id, length);
      switch ( sym->generic.id ) {

      default:
         if (0) {
            VG_(printf)("unknown id 0x%x len=0x%x at %p\n",
                        sym->generic.id, sym->generic.len, sym);
            VG_(printf)("  %8x  %8x  %8x  %8x\n", 
                        ((int *)sym)[1],((int *)sym)[2],
                        ((int *)sym)[3],((int *)sym)[4]);
            VG_(printf)("  %8x  %8x  %8x  %8x\n",
                        ((int *)sym)[5],((int *)sym)[6],
                        ((int *)sym)[7],((int *)sym)[8]);
         }
         break;
      /*
       * Global and local data symbols.  We don't associate these
       * with any given source file.
       */
      case S_GDATA_V1:
      case S_LDATA_V1:
      case S_PUB_V1:
         VG_(memcpy)(symname, sym->data_v1.p_name.name,
                              sym->data_v1.p_name.namelen);
         symname[sym->data_v1.p_name.namelen] = '\0';

         if (debug)
            VG_(message)(Vg_UserMsg, "Data %s", symname );

         if (0 /*VG_(needs).data_syms*/) {
            nmstr = ML_(addStr)(di, symname, sym->data_v1.p_name.namelen);

            vsym.addr = bias + sectp[sym->data_v1.segment-1].VirtualAddress
                             + sym->data_v1.offset;
            vsym.name = nmstr;
            vsym.size = sym->data_v1.p_name.namelen;
                      // FIXME: .namelen is sizeof(.data) including .name[]
            vsym.isText = (sym->generic.id == S_PUB_V1);
            ML_(addSym)( di, &vsym );
            n_syms_read++;
         }
         break;
      case S_GDATA_V2:
      case S_LDATA_V2:
      case S_PUB_V2: {
         Int const k = sym->data_v2.p_name.namelen;
         VG_(memcpy)(symname, sym->data_v2.p_name.name, k);
         symname[k] = '\0';

         if (debug)
            VG_(message)(Vg_UserMsg,
                         "S_GDATA_V2/S_LDATA_V2/S_PUB_V2 %s", symname );

         if (sym->generic.id==S_PUB_V2 /*VG_(needs).data_syms*/) {
            nmstr = ML_(addStr)(di, symname, k);

            vsym.addr = bias + sectp[sym->data_v2.segment-1].VirtualAddress
                             + sym->data_v2.offset;
            vsym.name = nmstr;
            vsym.size = 4000;
                        // FIXME: data_v2.len is sizeof(.data),
                        // not size of function!
            vsym.isText = !!(IMAGE_SCN_CNT_CODE 
                             & sectp[sym->data_v2.segment-1].Characteristics);
            ML_(addSym)( di, &vsym );
            n_syms_read++;
         }
         break;
      }
      case S_PUB_V3:
      /* not completely sure of those two anyway */
      case S_PUB_FUNC1_V3:
      case S_PUB_FUNC2_V3: {
         Int k = sym->public_v3.len - (-1+ sizeof(sym->public_v3));
         if ((-1+ sizeof(symname)) < k)
            k = -1+ sizeof(symname);
         VG_(memcpy)(symname, sym->public_v3.name, k);
         symname[k] = '\0';

         if (debug)
            VG_(message)(Vg_UserMsg,
                         "S_PUB_FUNC1_V3/S_PUB_FUNC2_V3/S_PUB_V3 %s", symname );

         if (1  /*sym->generic.id==S_PUB_FUNC1_V3 
                  || sym->generic.id==S_PUB_FUNC2_V3*/) {
            nmstr = ML_(addStr)(di, symname, k);

            vsym.addr = bias + sectp[sym->public_v3.segment-1].VirtualAddress
                             + sym->public_v3.offset;
            vsym.name = nmstr;
            vsym.size = 4000;
                        // FIXME: public_v3.len is not length of the
                        // .text of the function
            vsym.isText = !!(IMAGE_SCN_CNT_CODE
                             & sectp[sym->data_v2.segment-1].Characteristics);
            ML_(addSym)( di, &vsym );
            n_syms_read++;
         }
         break;
      }

      /*
       * Sort of like a global function, but it just points
       * to a thunk, which is a stupid name for what amounts to
       * a PLT slot in the normal jargon that everyone else uses.
       */
      case S_THUNK_V3:
      case S_THUNK_V1:
         /* valgrind ignores PLTs */ /* JRS: it does? */
         break;

      /*
       * Global and static functions.
       */
      case S_GPROC_V1:
      case S_LPROC_V1:
         VG_(memcpy)(symname, sym->proc_v1.p_name.name,
                              sym->proc_v1.p_name.namelen);
         symname[sym->proc_v1.p_name.namelen] = '\0';
         nmstr = ML_(addStr)(di, symname, sym->proc_v1.p_name.namelen);

         vsym.addr = bias + sectp[sym->proc_v1.segment-1].VirtualAddress
                          + sym->proc_v1.offset;
         vsym.name = nmstr;
         vsym.size = sym->proc_v1.proc_len;
         vsym.isText = True;
         if (debug)
             VG_(message)(Vg_UserMsg, "Adding function %s addr=%#lx length=%d",
                                      symname, vsym.addr, vsym.size );
         ML_(addSym)( di, &vsym );
         n_syms_read++;
         break;

      case S_GPROC_V2:
      case S_LPROC_V2:
         VG_(memcpy)(symname, sym->proc_v2.p_name.name,
                              sym->proc_v2.p_name.namelen);
         symname[sym->proc_v2.p_name.namelen] = '\0';
         nmstr = ML_(addStr)(di, symname, sym->proc_v2.p_name.namelen);

         vsym.addr = bias + sectp[sym->proc_v2.segment-1].VirtualAddress
                          + sym->proc_v2.offset;
         vsym.name = nmstr;
         vsym.size = sym->proc_v2.proc_len;
         vsym.isText = True;
         if (debug)
            VG_(message)(Vg_UserMsg, "Adding function %s addr=%#lx length=%d",
                                     symname, vsym.addr, vsym.size );
         ML_(addSym)( di, &vsym );
         n_syms_read++;
         break;
      case S_LPROC_V3:
      case S_GPROC_V3: {
         if (debug)
            VG_(message)(Vg_UserMsg,
                         "S_LPROC_V3/S_GPROC_V3 %s", sym->proc_v3.name );

         if (1) {
            nmstr = ML_(addStr)(di, sym->proc_v3.name,
                                    VG_(strlen)(sym->proc_v3.name));

            vsym.addr = bias + sectp[sym->proc_v3.segment-1].VirtualAddress
                             + sym->proc_v3.offset;
            vsym.name = nmstr;
            vsym.size  = sym->proc_v3.proc_len;
            vsym.isText = 1;
            ML_(addSym)( di, &vsym );
            n_syms_read++;
         }
         break;
      }
      /* JRS: how is flow supposed to arrive at commented out code below? */
      //if (nest_block)
      //{
      //   printf(">>> prev func '%s' still has nest_block %u count\n",
      //          curr_func, nest_block);
      //   nest_block = 0;
      //}
      //curr_func = strdup(sym->proc_v3.name);
      /* EPP  unsigned int    pparent; */
      /* EPP  unsigned int    pend; */
      /* EPP  unsigned int    next; */
      /* EPP  unsigned int    debug_start; */
      /* EPP  unsigned int    debug_end; */
      /* EPP  unsigned char   flags; */
      // break;


      /*
       * Function parameters and stack variables.
       */
      case S_BPREL_XXXX_V3:
      case S_BPREL_V3:
      case S_BPREL_V2:
      case S_BPREL_V1:
         /* ignored */
         break;

      case S_LABEL_V3:  // FIXME
      case S_LABEL_V1:
         break;

      case S_SSEARCH_V1:
      case S_ALIGN_V1:
      case S_MSTOOL_V3:
      case S_UDT_V3:
      case S_UDT_V2:
      case S_UDT_V1:
      case S_CONSTANT_V3:
      case S_CONSTANT_V1:
      case S_OBJNAME_V1:
      case S_END_V1:
      case S_COMPILAND_V3:
      case S_COMPILAND_V2:
      case S_COMPILAND_V1:
      case S_BLOCK_V3:
      case S_BLOCK_V1:
      case S_REGISTER_V3:
      case S_REGISTER_V2:
      case S_REGISTER_V1:
         /* ignored */
         break;

      /*
       * These are special, in that they are always followed by an
       * additional length-prefixed string which is *not* included
       * into the symbol length count.  We need to skip it.
       */
      case S_PROCREF_V1:
      case S_DATAREF_V1:
      case S_LPROCREF_V1: {
         unsigned char *name = (unsigned char *)sym + length;
         length += (*name + 1 + 3) & ~3;
         break;
      }
      } /* switch ( sym->generic.id ) */

   } /* for ( i = offset; i < size; i += length ) */

   return n_syms_read;
}


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- Main stuff: reading of line number tables            ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

union any_size
{
          char const *c;
         short const *s;
           int const *i;
  unsigned int const *ui;
};

struct startend
{
  unsigned int          start;
  unsigned int          end;
};

static ULong DEBUG_SnarfLinetab(
          DebugInfo* di,
          IMAGE_SECTION_HEADER* sectp,
          Char* linetab,
          Int size
       )
{
   //VG_(printf)("DEBUG_SnarfLinetab %p %p %p %d\n", di, sectp, linetab, size);
   Int                file_segcount;
   Char               filename[WIN32_PATH_MAX];
   UInt               * filetab;
   UChar              * fn;
   Int                i;
   Int                k;
   UInt               * lt_ptr;
   Int                nfile;
   Int                nseg;
   union any_size     pnt;
   union any_size     pnt2;
   struct startend    * start;
   Int                this_seg;

   Addr  bias = BIAS_FOR_LINETAB;
   ULong n_lines_read = 0;

   /*
    * Now get the important bits.
    */
   pnt.c = linetab;
   nfile = *pnt.s++;
   nseg  = *pnt.s++;

   filetab = (unsigned int *) pnt.c;

   /*
    * Now count up the number of segments in the file.
    */
   nseg = 0;
   for (i = 0; i < nfile; i++) {
      pnt2.c = linetab + filetab[i];
      nseg += *pnt2.s;
   }

   this_seg = 0;
   for (i = 0; i < nfile; i++) {
      UChar *fnmstr;
      UChar *dirstr;

      /*
       * Get the pointer into the segment information.
       */
      pnt2.c = linetab + filetab[i];
      file_segcount = *pnt2.s;

      pnt2.ui++;
      lt_ptr = (unsigned int *) pnt2.c;
      start = (struct startend *) (lt_ptr + file_segcount);

      /*
       * Now snarf the filename for all of the segments for this file.
       */
      fn = (UChar*) (start + file_segcount);
      /* fn now points at a Pascal-style string, that is, the first
         byte is the length, and the remaining up to 255 (presumably)
         are the contents. */
      vg_assert(WIN32_PATH_MAX >= 256);
      VG_(memset)(filename, 0, sizeof(filename));
      VG_(memcpy)(filename, fn + 1, *fn);
      vg_assert(filename[ sizeof(filename)-1 ] == 0);
      filename[(Int)*fn] = 0;
      fnmstr = VG_(strrchr)(filename, '\\');
      if (fnmstr == NULL)
         fnmstr = filename;
      else 
         ++fnmstr;
      k = VG_(strlen)(fnmstr);
      dirstr = ML_(addStr)(di, filename, *fn - k);
      fnmstr = ML_(addStr)(di, fnmstr, k);

      for (k = 0; k < file_segcount; k++, this_seg++) {
         Int linecount;
         Int segno;

         pnt2.c = linetab + lt_ptr[k];

         segno = *pnt2.s++;
         linecount = *pnt2.s++;

         if ( linecount > 0 ) {
            UInt j;

            if (debug)
               VG_(message)(Vg_UserMsg,
                  "Adding %d lines for file %s segment %d addr=%#x end=%#x",
                  linecount, filename, segno, start[k].start, start[k].end );

            for ( j = 0; j < linecount; j++ ) {
               Addr startaddr = bias + sectp[segno-1].VirtualAddress
                                     + pnt2.ui[j];
               Addr endaddr   = bias + sectp[segno-1].VirtualAddress
                                     + ((j < (linecount - 1))
                                           ? pnt2.ui[j+1] 
                                           : start[k].end);
               if (debug)
                  VG_(message)(Vg_UserMsg,
                     "Adding line %d addr=%#lx end=%#lx", 
                        ((unsigned short *)(pnt2.ui + linecount))[j],
                        startaddr, endaddr );
                  ML_(addLineInfo)(
                     di, fnmstr, dirstr, startaddr, endaddr,
                     ((unsigned short *)(pnt2.ui + linecount))[j], j );
                  n_lines_read++;
               }
            }
        }
    }

    return n_lines_read;
}



/* there's a new line tab structure from MS Studio 2005 and after
 * it's made of:
 * DWORD        000000f4
 * DWORD        lineblk_offset (counting bytes after this field)
 * an array of codeview_linetab2_file structures
 * an array (starting at <lineblk_offset>) of codeview_linetab2_block structures
 */

struct codeview_linetab2_file
{
    DWORD       offset;         /* offset in string table for filename */
    WORD        unk;            /* always 0x0110... type of following
                                   information ??? */
    BYTE        md5[16];        /* MD5 signature of file (signature on
                                   file's content or name ???) */
    WORD        pad0;           /* always 0 */
};

struct codeview_linetab2_block
{
    DWORD       header;         /* 0x000000f2 */
    DWORD       size_of_block;  /* next block is at # bytes after this field */
    DWORD       start;          /* start address of function with line numbers */
    DWORD       seg;            /* segment of function with line numbers */
    DWORD       size;           /* size of function with line numbers */
    DWORD       file_offset;    /* offset for accessing corresponding
                                   codeview_linetab2_file */
    DWORD       nlines;         /* number of lines in this block */
    DWORD       size_lines;     /* number of bytes following for line
                                   number information */
    struct {
        DWORD   offset;         /* offset (from <seg>:<start>) for line number */
        DWORD   lineno;         /* the line number (OR:ed with
                                   0x80000000 why ???) */
    } l[1];                     /* actually array of <nlines> */
};

static ULong codeview_dump_linetab2(
                DebugInfo* di,
                Char* linetab,
                DWORD size,
                Char* strimage,
                DWORD strsize,
                Char* pfx
             )
{
   DWORD       offset;
   unsigned    i;
   struct codeview_linetab2_block* lbh;
   struct codeview_linetab2_file* fd;
   //const Bool debug = False;

   Addr  bias = BIAS_FOR_LINETAB2;
   ULong n_line2s_read = 0;

   if (*(const DWORD*)linetab != 0x000000f4)
      return 0;
   offset = *((DWORD*)linetab + 1);
   lbh = (struct codeview_linetab2_block*)(linetab + 8 + offset);

   while ((Char*)lbh < linetab + size) {

      HChar *filename, *dirname;
      Addr svma_s, svma_e;
      if (lbh->header != 0x000000f2) {
         /* FIXME: should also check that whole lbh fits in linetab + size */
         if (debug)
            VG_(printf)("%sblock end %x\n", pfx, lbh->header);
         break;
      }
      if (debug)
         VG_(printf)("%sblock from %04x:%08x-%08x (size %u) (%u lines)\n",
                     pfx, lbh->seg, lbh->start, lbh->start + lbh->size - 1,
                     lbh->size, lbh->nlines);
      fd = (struct codeview_linetab2_file*)(linetab + 8 + lbh->file_offset);
      if (debug)
         VG_(printf)(
            "%s  md5=%02x%02x%02x%02x%02x%02x%02x%02x"
                    "%02x%02x%02x%02x%02x%02x%02x%02x\n",
             pfx, fd->md5[ 0], fd->md5[ 1], fd->md5[ 2], fd->md5[ 3],
                  fd->md5[ 4], fd->md5[ 5], fd->md5[ 6], fd->md5[ 7],
                  fd->md5[ 8], fd->md5[ 9], fd->md5[10], fd->md5[11],
                  fd->md5[12], fd->md5[13], fd->md5[14], fd->md5[15] );
      /* FIXME: should check that string is within strimage + strsize */
      if (strimage) {
         dirname  = strimage + fd->offset;
         filename = VG_(strrchr)(dirname, '\\');
         if (filename == NULL) {
            filename = ML_(addStr)(di, dirname, -1);
            dirname  = NULL;
         } else {
            dirname  = ML_(addStr)(di, dirname, VG_(strlen)(dirname) 
                                                - VG_(strlen)(filename));
            filename = ML_(addStr)(di, filename+1, -1);
         }
      } else {
         filename = ML_(addStr)(di, "???", -1);
         dirname  = NULL;
      }

      if (debug)
         VG_(printf)("%s  file=%s\n", pfx, filename);

      for (i = 0; i < lbh->nlines; i++) {
         if (debug)
            VG_(printf)("%s  offset=%08x line=%d\n",
                        pfx, lbh->l[i].offset, lbh->l[i].lineno ^ 0x80000000);
      }

      if (lbh->nlines > 1) {
         for (i = 0; i < lbh->nlines-1; i++) {
            svma_s = lbh->start + lbh->l[i].offset;
            svma_e = lbh->start + lbh->l[i+1].offset-1;
            if (debug)
               VG_(printf)("%s  line %d: %08lx to %08lx\n",
                           pfx, lbh->l[i].lineno ^ 0x80000000, svma_s, svma_e);
            ML_(addLineInfo)( di, filename, dirname,
                              bias + svma_s,
                              bias + svma_e + 1,
                              lbh->l[i].lineno ^ 0x80000000, 0 );
            n_line2s_read++;
         }
         svma_s = lbh->start + lbh->l[ lbh->nlines-1].offset;
         svma_e = lbh->start + lbh->size - 1;
         if (debug)
            VG_(printf)("%s  line %d: %08lx to %08lx\n",
                        pfx, lbh->l[ lbh->nlines-1  ].lineno ^ 0x80000000,
                        svma_s, svma_e);
          ML_(addLineInfo)( di, filename, dirname,
                            bias + svma_s,
                            bias + svma_e + 1,
                            lbh->l[lbh->nlines-1].lineno ^ 0x80000000, 0 );
          n_line2s_read++;
       }

       lbh = (struct codeview_linetab2_block*)
                ((char*)lbh + 8 + lbh->size_of_block);
    }
    return n_line2s_read;
}


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- Main stuff: pdb_dump                                 ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

/* JRS fixme: compare with version in current Wine sources */
static void pdb_dump( struct pdb_reader* pdb,
                      DebugInfo* di,
                      Addr pe_avma,
                      Int  reloc,
                      IMAGE_SECTION_HEADER* sectp_avma )
{
   Int header_size;

   PDB_TYPES types;
   PDB_SYMBOLS symbols;
   unsigned len_modimage;
   char *modimage;
   char *file; 

   Addr bias_for_fpo = BIAS_FOR_FPO;

   ULong n_fpos_read = 0, n_syms_read = 0,
         n_lines_read = 0, n_line2s_read = 0;

   // FIXME: symbols for bare indices 1,2,3,5 in .pdb file

   char* types_image   = pdb->read_file( pdb, 2, 0 );
   char* symbols_image = pdb->read_file( pdb, 3, 0 );

   /* establish filesimage and filessize.  These are only needed for
      reading linetab2 tables, as far as I can deduce from the Wine
      sources. */
   char* filesimage = pdb->read_file( pdb, 12, 0);   /* FIXME: really fixed ??? */
   UInt  filessize  = 0;
   if (filesimage) {
      if (*(const DWORD*)filesimage == 0xeffeeffe) {
         filessize = *(const DWORD*)(filesimage + 8);
      } else {
         if (0)
            VG_(printf)("wrong header %x expecting 0xeffeeffe\n",
                        *(const DWORD*)filesimage);
         ML_(dinfo_free)( (void*)filesimage);
         filesimage = NULL;
      }
   }

   if (VG_(clo_verbosity) > 0) {
      VG_(message)(Vg_DebugMsg,
                   "PDB_READER:");
      VG_(message)(Vg_DebugMsg,
                   "   BIAS_FOR_SYMBOLS  = %#08lx  %s",
                   (PtrdiffT)BIAS_FOR_SYMBOLS, VG_STRINGIFY(BIAS_FOR_SYMBOLS));
      VG_(message)(Vg_DebugMsg,
                   "   BIAS_FOR_LINETAB  = %#08lx  %s",
                   (PtrdiffT)BIAS_FOR_LINETAB, VG_STRINGIFY(BIAS_FOR_LINETAB));
      VG_(message)(Vg_DebugMsg,
                   "   BIAS_FOR_LINETAB2 = %#08lx  %s",
                   (PtrdiffT)BIAS_FOR_LINETAB2, VG_STRINGIFY(BIAS_FOR_LINETAB2));
      VG_(message)(Vg_DebugMsg,
                   "   BIAS_FOR_FPO      = %#08lx  %s",
                   (PtrdiffT)BIAS_FOR_FPO, VG_STRINGIFY(BIAS_FOR_FPO));
      VG_(message)(Vg_DebugMsg,
                   "   RELOC             = %#08lx",
                   (PtrdiffT)reloc);
   }

   /* Since we just use the FPO data without reformatting, at least
      do a basic sanity check on the struct layout. */
   vg_assert(sizeof(FPO_DATA) == 16);
   if (di->text_present) { 
      /* only load FPO if there's text present (otherwise it's
         meaningless?) */
      unsigned sz = 0;
      di->fpo = pdb->read_file( pdb, 5, &sz );
      di->fpo_size = sz;
   } else {
      vg_assert(di->fpo == NULL);
      vg_assert(di->fpo_size == 0);
   }

   if (di->fpo) {
      Word i;
      Addr min_svma = ~(Addr)0;
      Addr max_svma = (Addr)0;
      vg_assert(sizeof(di->fpo[0]) == 16);
      di->fpo_size /= sizeof(di->fpo[0]);

      /* Sanity-check the table, and find the min and max avmas. */
      for (i = 0; i < di->fpo_size; i++) {
         /* If any of the following assertions fail, we'll need to add
            an extra pass to tidy up the FPO info -- make them be in
            order and non-overlapping, since in-orderness and
            non-overlappingness are required for safe use of
            ML_(search_one_fpotab). */
         vg_assert(di->fpo[i].cbProcSize > 0);
         if (i > 0) {
            Bool ok;
            Bool dup
               = di->fpo[i-1].ulOffStart == di->fpo[i].ulOffStart
                 && di->fpo[i-1].cbProcSize == di->fpo[i].cbProcSize;
            /* tolerate exact duplicates -- I think they are harmless
               w.r.t. termination properties of the binary search in
               ML_(search_one_fpotab). */
            if (dup)
               continue;

            ok = di->fpo[i-1].ulOffStart + di->fpo[i-1].cbProcSize 
                 <= di->fpo[i].ulOffStart;
            if (1 && !ok)
               VG_(printf)("%#x +%d  then  %#x +%d\n",
                           di->fpo[i-1].ulOffStart, di->fpo[i-1].cbProcSize,
                           di->fpo[i-0].ulOffStart, di->fpo[i-0].cbProcSize );
            vg_assert(ok);
         }
         /* Update min/max limits as we go along. */
         if (di->fpo[i].ulOffStart < min_svma)
            min_svma = di->fpo[i].ulOffStart;
         if (di->fpo[i].ulOffStart + di->fpo[i].cbProcSize - 1 > max_svma)
            max_svma = di->fpo[i].ulOffStart + di->fpo[i].cbProcSize - 1;
      }
      /* Now bias the table.  This can't be done in the same pass as
         the sanity check, hence a second loop. */
      for (i = 0; i < di->fpo_size; i++) {
         di->fpo[i].ulOffStart += bias_for_fpo;
      }

      /* And record min/max */
      vg_assert(min_svma <= max_svma); /* should always hold */

      di->fpo_minavma = min_svma + bias_for_fpo;
      di->fpo_maxavma = max_svma + bias_for_fpo;

      /* biasing shouldn't cause wraparound (?!) */
      vg_assert(di->fpo_minavma <= di->fpo_maxavma);

      if (0) {
         VG_(printf)("XXXXXXXXX min/max svma %#lx %#lx\n",
                     min_svma, max_svma);
         VG_(printf)("XXXXXXXXX min/max avma %#lx %#lx\n",
                     di->fpo_minavma, di->fpo_maxavma);
      }

      n_fpos_read += (ULong)di->fpo_size;
   }

   pdb_convert_types_header( &types, types_image );
   switch ( types.version ) {
      case 19950410:      /* VC 4.0 */
      case 19951122:
      case 19961031:      /* VC 5.0 / 6.0 */
      case 20040203:      /* VC 7.0  FIXME??  */
         break;
      default:
         if (VG_(clo_verbosity) > 1)
            VG_(message)(Vg_UserMsg, "Unknown .pdb type info version %ld\n",
                                     types.version );
   }

   header_size = 0;
   pdb_convert_symbols_header( &symbols, &header_size, symbols_image );
   switch ( symbols.version ) {
      case 0:            /* VC 4.0 */
      case 19960307:     /* VC 5.0 */
      case 19970606:     /* VC 6.0 */
      case 19990903:     /* VC 7.0  FIXME?? */
         break;
      default:
         if (VG_(clo_verbosity) > 1)
            VG_(message)(Vg_UserMsg, "Unknown .pdb symbol info version %ld\n",
                                     symbols.version );
   }

   /*
    * Read global symbol table
    */
   modimage = pdb->read_file( pdb, symbols.gsym_file, &len_modimage );
   if (modimage) {
      if (VG_(clo_verbosity) > 1)
         VG_(message)(Vg_UserMsg, "Reading global symbols\n" );
      DEBUG_SnarfCodeView( di, sectp_avma, modimage, 0, len_modimage );
      ML_(dinfo_free)( (void*)modimage );
   }

   /*
    * Read per-module symbol / linenumber tables
    */
   file = symbols_image + header_size;
   while ( file - symbols_image < header_size + symbols.module_size ) {
      int file_nr, file_index, symbol_size, lineno_size;
      char *file_name;

      if ( symbols.version < 19970000 ) {
         PDB_SYMBOL_FILE *sym_file = (PDB_SYMBOL_FILE *) file;
         file_nr     = sym_file->file;
         file_name   = sym_file->filename;
         file_index  = sym_file->range.index;
         symbol_size = sym_file->symbol_size;
         lineno_size = sym_file->lineno_size;
      } else {
         PDB_SYMBOL_FILE_EX *sym_file = (PDB_SYMBOL_FILE_EX *) file;
         file_nr     = sym_file->file;
         file_name   = sym_file->filename;
         file_index  = sym_file->range.index;
         symbol_size = sym_file->symbol_size;
         lineno_size = sym_file->lineno_size;
      }

      modimage = pdb->read_file( pdb, file_nr, 0 );
      if (modimage) {
         Int total_size;
         if (0) VG_(printf)("lineno_size %d symbol_size %d\n",
                            lineno_size, symbol_size );

         total_size = pdb_get_file_size(pdb, file_nr);

         if (symbol_size) {
            if (VG_(clo_verbosity) > 1)
               VG_(message)(Vg_UserMsg, "Reading symbols for %s", file_name );
            n_syms_read 
               += DEBUG_SnarfCodeView( di, sectp_avma, modimage,
                                           sizeof(unsigned long),
                                           symbol_size );
         }

         if (lineno_size) {
            if (VG_(clo_verbosity) > 1)
               VG_(message)(Vg_UserMsg, "Reading lines for %s", file_name );
            n_lines_read
               += DEBUG_SnarfLinetab( di, sectp_avma,
                                          modimage + symbol_size, lineno_size );
         }

         /* anyway, lineno_size doesn't see to really be the size of
          * the line number information, and it's not clear yet when
          * to call for linetab2...
          */
         n_line2s_read
            += codeview_dump_linetab2(
                  di, (char*)modimage + symbol_size + lineno_size,
                      total_size - (symbol_size + lineno_size),
                  /* if filesimage is NULL, pass that directly onwards
                     to codeview_dump_linetab2, so it knows not to
                     poke around in there. */
                  filesimage ? filesimage + 12 : NULL,
                  filessize, "        "
               );

         ML_(dinfo_free)( (void*)modimage );
      }

      file_name += VG_(strlen)(file_name) + 1;
      file = (char *)( 
                (unsigned long)(file_name
                                + VG_(strlen)(file_name) + 1 + 3) & ~3 );
   }

   /*
    * Cleanup
    */
   if ( symbols_image ) ML_(dinfo_free)( symbols_image );
   if ( types_image ) ML_(dinfo_free)( types_image );
   if ( pdb->u.jg.toc ) ML_(dinfo_free)( pdb->u.jg.toc );

   if (VG_(clo_verbosity) > 0) {
      VG_(message)(Vg_DebugMsg,"   # symbols read = %llu", n_syms_read );
      VG_(message)(Vg_DebugMsg,"   # lines   read = %llu", n_lines_read );
      VG_(message)(Vg_DebugMsg,"   # line2s  read = %llu", n_line2s_read );
      VG_(message)(Vg_DebugMsg,"   # fpos    read = %llu", n_fpos_read );
   }
}


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- TOP LEVEL for PDB reading                            ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

Bool ML_(read_pdb_debug_info)(
        DebugInfo* di,
        Addr       obj_avma,
        PtrdiffT   unknown_purpose__reloc,
        void*      pdbimage,
        SizeT      n_pdbimage,
        Char*      pdbname,
        ULong      pdbmtime
     )
{
   Char*    pe_seg_avma;
   Int      i;
   Addr     mapped_avma, mapped_end_avma;
   unsigned signature;
   void*    hdr;
   struct pdb_reader     reader;
   IMAGE_DOS_HEADER*     dos_avma;
   IMAGE_NT_HEADERS*     ntheaders_avma;
   IMAGE_SECTION_HEADER* sectp_avma;
   IMAGE_SECTION_HEADER* pe_sechdr_avma;

   if (VG_(clo_verbosity) > 1)
       VG_(message)(Vg_UserMsg, "Processing PDB file %s ", pdbname );

   dos_avma = (IMAGE_DOS_HEADER *)obj_avma;
   if (dos_avma->e_magic != IMAGE_DOS_SIGNATURE)
      return False;

   ntheaders_avma
      = (IMAGE_NT_HEADERS *)((Char*)dos_avma + dos_avma->e_lfanew);
   if (ntheaders_avma->Signature != IMAGE_NT_SIGNATURE)
      return False;

   sectp_avma
      = (IMAGE_SECTION_HEADER *)(
           (Char*)ntheaders_avma
           + OFFSET_OF(IMAGE_NT_HEADERS, OptionalHeader)
           + ntheaders_avma->FileHeader.SizeOfOptionalHeader
        );

   /* JRS: this seems like something of a hack. */
   di->soname = ML_(dinfo_strdup)("di.readpdb.rpdi.1", pdbname);

   /* someone (ie WINE) is loading a Windows PE format object.  we
      need to use its details to determine which area of memory is
      executable... */
   pe_seg_avma
      = (Char*)ntheaders_avma
        + OFFSET_OF(IMAGE_NT_HEADERS, OptionalHeader)
        + ntheaders_avma->FileHeader.SizeOfOptionalHeader;

   di->rx_map_avma = (Addr)obj_avma;

   /* Iterate over PE(?) headers.  Try to establish the text_bias,
      that's all we really care about. */
   for ( i = 0;
         i < ntheaders_avma->FileHeader.NumberOfSections;
         i++, pe_seg_avma += sizeof(IMAGE_SECTION_HEADER) ) {
      pe_sechdr_avma = (IMAGE_SECTION_HEADER *)pe_seg_avma;

      if (VG_(clo_verbosity) > 1)
         VG_(message)(Vg_UserMsg,
                      "  Scanning PE section %s at avma %p svma %#lx",
                      pe_sechdr_avma->Name, pe_seg_avma,
                      pe_sechdr_avma->VirtualAddress);

      if (pe_sechdr_avma->Characteristics & IMAGE_SCN_MEM_DISCARDABLE)
         continue;

      mapped_avma     = (Addr)obj_avma + pe_sechdr_avma->VirtualAddress;
      mapped_end_avma = mapped_avma + pe_sechdr_avma->Misc.VirtualSize;
      if (VG_(clo_verbosity) > 1)
         VG_(message)(Vg_DebugMsg,
             "   ::: mapped_avma is %#lx", mapped_avma);

      if (pe_sechdr_avma->Characteristics & IMAGE_SCN_CNT_CODE) {
         di->have_rx_map = True;
         if (di->rx_map_avma == 0) {
            di->rx_map_avma = mapped_avma;
         }
         if (di->rx_map_size==0) {
            di->rx_map_foff = pe_sechdr_avma->PointerToRawData;
         }
         di->text_present = True;
         if (di->text_avma==0) {
            di->text_avma = mapped_avma;
         }
         di->text_size   += pe_sechdr_avma->Misc.VirtualSize;
         di->rx_map_size += pe_sechdr_avma->Misc.VirtualSize;
      }
      else if (pe_sechdr_avma->Characteristics 
               & IMAGE_SCN_CNT_INITIALIZED_DATA) {
         di->have_rw_map = True;
         if (di->rw_map_avma == 0) {
            di->rw_map_avma = mapped_avma;
         }
         if (di->rw_map_size==0) {
            di->rw_map_foff = pe_sechdr_avma->PointerToRawData;
         }
         di->data_present = True;
         if (di->data_avma==0) {
            di->data_avma = mapped_avma;
         }
         di->rw_map_size += pe_sechdr_avma->Misc.VirtualSize;
         di->data_size   += pe_sechdr_avma->Misc.VirtualSize;
      }
      else if (pe_sechdr_avma->Characteristics
               & IMAGE_SCN_CNT_UNINITIALIZED_DATA) {
         di->bss_present = True;
         di->bss_avma = mapped_avma;
         di->bss_size = pe_sechdr_avma->Misc.VirtualSize;
      }

      mapped_avma     = VG_PGROUNDDN(mapped_avma);
      mapped_end_avma = VG_PGROUNDUP(mapped_end_avma);

      /* Urr.  These tests are bogus; ->rx_map_avma is not necessarily
         the start of the text section. */
      if ((1 /*VG_(needs).data_syms*/ 
           || (pe_sechdr_avma->Characteristics & IMAGE_SCN_CNT_CODE))
          && mapped_avma >= di->rx_map_avma
          && mapped_avma <= (di->rx_map_avma+di->text_size)
          && mapped_end_avma > (di->rx_map_avma+di->text_size)) {
         UInt newsz = mapped_end_avma - di->rx_map_avma;
         if (newsz > di->text_size) {
            /* extending the mapping is always needed for PE files
               under WINE */
            di->text_size = newsz;
            di->rx_map_size = newsz;
         }
      }
   }

   if (di->have_rx_map && di->have_rw_map && !di->have_dinfo) {
      vg_assert(di->filename);
      TRACE_SYMTAB("\n");
      TRACE_SYMTAB("------ start PE OBJECT with PDB INFO "
                   "---------------------\n");
      TRACE_SYMTAB("------ name = %s\n", di->filename);
      TRACE_SYMTAB("\n");
   }

   if (di->text_present) {
      di->text_bias = di->text_avma - di->text_svma;
   } else {
      di->text_bias = 0;
   }

   if (VG_(clo_verbosity) > 1) {
      VG_(message)(Vg_DebugMsg,
                   "rx_map: avma %#lx size %7lu foff %llu\n",
                   di->rx_map_avma, di->rx_map_size, (Off64T)di->rx_map_foff);
      VG_(message)(Vg_DebugMsg,
                   "rw_map: avma %#lx size %7lu foff %llu\n",
                   di->rw_map_avma, di->rw_map_size, (Off64T)di->rw_map_foff);

      VG_(message)(Vg_DebugMsg,
                   "  text: avma %#lx svma %#lx size %7lu bias %#lx\n",
                   di->text_avma, di->text_svma, di->text_size, di->text_bias);
   }

   /*
    * Read in TOC and well-known files
    */
   signature = 0;
   hdr = find_pdb_header( pdbimage, &signature );
   if (0==hdr)
      return False; /* JRS: significance? no pdb header? */

   VG_(memset)(&reader, 0, sizeof(reader));
   reader.u.jg.header = hdr;

   if (0==VG_(strncmp)((char const *)&signature, "DS\0\0", 4)) {
      struct PDB_DS_ROOT* root;
      pdb_ds_init( &reader, pdbimage, n_pdbimage );
      root = reader.read_file( &reader, 1, 0 );
      if (root) {
         pdb_check_root_version_and_timestamp(
            pdbname, pdbmtime, root->version, root->TimeDateStamp );
         ML_(dinfo_free)( root );
      }
      pdb_dump( &reader, di, obj_avma, unknown_purpose__reloc, sectp_avma );
   }
   else
   if (0==VG_(strncmp)((char const *)&signature, "JG\0\0", 4)) {
      struct PDB_JG_ROOT* root;
      pdb_jg_init( &reader, pdbimage, n_pdbimage );
      root = reader.read_file( &reader, 1, 0 );
      if (root) {
         pdb_check_root_version_and_timestamp(
            pdbname, pdbmtime, root->version, root->TimeDateStamp);
         ML_(dinfo_free)( root );
      }
      pdb_dump( &reader, di, obj_avma, unknown_purpose__reloc, sectp_avma );
   }

   if (1) {
      TRACE_SYMTAB("\n------ Canonicalising the "
                   "acquired info ------\n");
      /* prepare read data for use */
      ML_(canonicaliseTables)( di );
      /* notify m_redir about it */
      TRACE_SYMTAB("\n------ Notifying m_redir ------\n");
      VG_(redir_notify_new_DebugInfo)( di );
      /* Note that we succeeded */
      di->have_dinfo = True;
   } else {
      TRACE_SYMTAB("\n------ PE with PDB reading failed ------\n");
      /* Something went wrong (eg. bad ELF file).  Should we delete
         this DebugInfo?  No - it contains info on the rw/rx
         mappings, at least. */
   }

   TRACE_SYMTAB("\n");
   TRACE_SYMTAB("------ name = %s\n", di->filename);
   TRACE_SYMTAB("------ end PE OBJECT with PDB INFO "
                "--------------------\n");
   TRACE_SYMTAB("\n");

   return True;
}


/*--------------------------------------------------------------------*/
/*--- end                                                readpdb.c ---*/
/*--------------------------------------------------------------------*/
