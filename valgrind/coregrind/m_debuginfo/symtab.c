
/*--------------------------------------------------------------------*/
/*--- Management of symbols and debugging information.             ---*/
/*---                                                     symtab.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2005 Julian Seward 
      jseward@acm.org

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

/*
   Stabs reader greatly improved by Nick Nethercote, Apr 02.
*/


#include "pub_core_basics.h"
#include "pub_core_threadstate.h"
#include "pub_core_debuginfo.h"
#include "pub_core_demangle.h"
#include "pub_core_libcbase.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcfile.h"
#include "pub_core_libcprint.h"
#include "pub_core_machine.h"
#include "pub_core_mallocfree.h"
#include "pub_core_options.h"
#include "pub_core_redir.h"       // VG_(redir_notify_{new,delete}_SegInfo)
#include "pub_core_tooliface.h"   // VG_(needs).data_syms
#include "pub_core_oset.h"        // for ppc64-linux elf symbol reading

#include "pub_core_aspacemgr.h"

#include "priv_symtypes.h"
#include "priv_symtab.h"

#include <elf.h>          /* ELF defns */

/* The root structure for the entire symbol table system.  It is a
   linked list of SegInfos.  Note that this entire mechanism assumes
   that what we read from /proc/self/maps doesn't contain overlapping
   address ranges, and as a result the SegInfos in this list describe
   disjoint address ranges. 
*/
static SegInfo* segInfo_list = NULL;

/*------------------------------------------------------------*/
/*--- 32/64-bit parameterisation                           ---*/
/*------------------------------------------------------------*/

/* For all the ELF macros and types which specify '32' or '64',
   select the correct variant for this platform and give it
   an 'XX' name.  Then use the 'XX' variant consistently in
   the rest of this file. 
*/
#if VG_WORDSIZE == 4
#  define  ElfXX_Ehdr     Elf32_Ehdr
#  define  ElfXX_Shdr     Elf32_Shdr
#  define  ElfXX_Phdr     Elf32_Phdr
#  define  ElfXX_Sym      Elf32_Sym
#  define  ElfXX_Word     Elf32_Word
#  define  ElfXX_Addr     Elf32_Addr
#  define  ElfXX_Dyn      Elf32_Dyn
#  define  ELFXX_ST_BIND  ELF32_ST_BIND
#  define  ELFXX_ST_TYPE  ELF32_ST_TYPE

#elif VG_WORDSIZE == 8
#  define  ElfXX_Ehdr     Elf64_Ehdr
#  define  ElfXX_Shdr     Elf64_Shdr
#  define  ElfXX_Phdr     Elf64_Phdr
#  define  ElfXX_Sym      Elf64_Sym
#  define  ElfXX_Word     Elf64_Word
#  define  ElfXX_Addr     Elf64_Addr
#  define  ElfXX_Dyn      Elf64_Dyn
#  define  ELFXX_ST_BIND  ELF64_ST_BIND
#  define  ELFXX_ST_TYPE  ELF64_ST_TYPE

#else
# error "VG_WORDSIZE should be 4 or 8"
#endif


/*------------------------------------------------------------*/
/*--- Forwards decls                                       ---*/
/*------------------------------------------------------------*/

static Bool is_elf_object_file ( const void *buf );
static void unload_symbols ( Addr start, SizeT length );


/*------------------------------------------------------------*/
/*--- TOP LEVEL                                            ---*/
/*------------------------------------------------------------*/

/* If this mapping is at the beginning of a file, isn't part of
   Valgrind, is at least readable and seems to contain an object
   file, then try reading symbols from it.

   Getting this heuristic right is critical.  On x86-linux,
   objects are typically mapped twice:

   1b8fb000-1b8ff000 r-xp 00000000 08:02 4471477 vgpreload_memcheck.so
   1b8ff000-1b900000 rw-p 00004000 08:02 4471477 vgpreload_memcheck.so

   whereas ppc32-linux mysteriously does this:

   118a6000-118ad000 r-xp 00000000 08:05 14209428 vgpreload_memcheck.so
   118ad000-118b6000 ---p 00007000 08:05 14209428 vgpreload_memcheck.so
   118b6000-118bd000 rwxp 00000000 08:05 14209428 vgpreload_memcheck.so

   The third mapping should not be considered to have executable code in.
   Therefore a test which works for both is: r and x and NOT w.  Reading
   symbols from the rwx segment -- which overlaps the r-x segment in the
   file -- causes the redirection mechanism to redirect to addresses in
   that third segment, which is wrong and causes crashes.

   ------
   JRS 28 Dec 05: unfortunately icc 8.1 on x86 has been seen to
   produce executables with a single rwx segment rather than a
   (r-x,rw-) pair. That means the rules have to be modified thusly:

   x86-linux:   consider if r and x
   all others:  consider if r and x and NOT w

*/

static void nuke_syms_in_range ( Addr start, SizeT length )
{
   /* Repeatedly scan the segInfo list, looking for segInfos in this
      range, and call unload_symbols on the segInfo's stated start
      point.  This modifies the list, hence the multiple
      iterations. */
   Bool found;
   SegInfo* curr;

   while (True) {
      found = False;

      curr = segInfo_list;
      while (True) {
         if (curr == NULL) break;
         if (start+length-1 < curr->start 
             || curr->start+curr->size-1 < start) {
	   /* no overlap */
	 } else {
	   found = True;
	   break;
	 }
	 curr = curr->next;
      }

      if (!found) break;
      unload_symbols( curr->start, curr->size );
   }
}

/* Notify the debuginfo system about a new mapping.  This is the way
   new debug information gets loaded.  If allow_SkFileV is True, it
   will try load debug info if the mapping at 'a' belongs to Valgrind;
   whereas normally (False) it will not do that.  This allows us to
   carefully control when the thing will read symbols from the
   Valgrind executable itself. */

void VG_(di_notify_mmap)( Addr a, Bool allow_SkFileV )
{
   NSegment* seg;
   HChar*    filename;
   Bool      ok;

   /* See comment at start of section for explanation of this do/don't
      logic. */
#  if defined(VGP_x86_linux)
   Bool      require_no_W = False;
#  else
   Bool      require_no_W = True;
#  endif

   seg = VG_(am_find_nsegment)(a);
   vg_assert(seg);

   filename = VG_(am_get_filename)( seg );
   if (!filename)
      return;

   filename = VG_(arena_strdup)( VG_AR_SYMTAB, filename );

   ok = (seg->kind == SkFileC || (seg->kind == SkFileV && allow_SkFileV))
        && seg->offset == 0
        && seg->fnIdx != -1
        && seg->hasR
        && seg->hasX
        && (require_no_W ? (!seg->hasW) : True)
        && is_elf_object_file( (const void*)seg->start );

   if (!ok) {
      VG_(arena_free)(VG_AR_SYMTAB, filename);
      return;
   }

   nuke_syms_in_range( seg->start, seg->end + 1 - seg->start );
   VG_(read_seg_symbols)( seg->start, seg->end + 1 - seg->start, 
                          seg->offset, filename );

   /* VG_(read_seg_symbols) makes its own copy of filename, so is safe
      to free it. */
   VG_(arena_free)(VG_AR_SYMTAB, filename);
}

void VG_(di_notify_munmap)( Addr a, SizeT len )
{
   nuke_syms_in_range(a, len);
}

void VG_(di_notify_mprotect)( Addr a, SizeT len, UInt prot )
{
   Bool exe_ok = toBool(prot & VKI_PROT_EXEC);
#  if defined(VGP_x86_linux)
   exe_ok = exe_ok || toBool(prot & VKI_PROT_READ);
#  endif
   if (0 && !exe_ok)
      nuke_syms_in_range(a, len);
}


/*------------------------------------------------------------*/
/*--- Adding stuff                                         ---*/
/*------------------------------------------------------------*/

/* Add a str to the string table, including terminating zero, and
   return pointer to the string in vg_strtab.  Unless it's been seen
   recently, in which case we find the old pointer and return that.
   This avoids the most egregious duplications. 

   JSGF: changed from returning an index to a pointer, and changed to
   a chunking memory allocator rather than reallocating, so the
   pointers are stable.
*/

Char* ML_(addStr) ( SegInfo* si, Char* str, Int len )
{
   struct strchunk *chunk;
   Int    space_needed;
   Char* p;

   if (len == -1)
      len = VG_(strlen)(str);

   space_needed = 1 + len;

   // Allocate a new strtab chunk if necessary
   if (si->strchunks == NULL || 
       (si->strchunks->strtab_used + space_needed) > STRCHUNKSIZE) {
      chunk = VG_(arena_malloc)(VG_AR_SYMTAB, sizeof(*chunk));
      chunk->strtab_used = 0;
      chunk->next = si->strchunks;
      si->strchunks = chunk;
   }
   chunk = si->strchunks;

   p = &chunk->strtab[chunk->strtab_used];
   VG_(memcpy)(p, str, len);
   chunk->strtab[chunk->strtab_used+len] = '\0';
   chunk->strtab_used += space_needed;

   return p;
}

/* Add a symbol to the symbol table. */
static void addSym ( SegInfo* si, RiSym* sym )
{
   UInt   new_sz, i;
   RiSym* new_tab;

   /* Ignore zero-sized syms. */
   if (sym->size == 0) return;

   if (si->symtab_used == si->symtab_size) {
      new_sz = 2 * si->symtab_size;
      if (new_sz == 0) new_sz = 500;
      new_tab = VG_(arena_malloc)(VG_AR_SYMTAB, new_sz * sizeof(RiSym) );
      if (si->symtab != NULL) {
         for (i = 0; i < si->symtab_used; i++)
            new_tab[i] = si->symtab[i];
         VG_(arena_free)(VG_AR_SYMTAB, si->symtab);
      }
      si->symtab = new_tab;
      si->symtab_size = new_sz;
   }

   si->symtab[si->symtab_used] = *sym;
   si->symtab_used++;
   vg_assert(si->symtab_used <= si->symtab_size);
}

/* Add a location to the location table. */

static __inline__
void addLoc ( SegInfo* si, RiLoc* loc )
{
   UInt   new_sz, i;
   RiLoc* new_tab;

   /* Zero-sized locs should have been ignored earlier */
   vg_assert(loc->size > 0);

   if (si->loctab_used == si->loctab_size) {
      new_sz = 2 * si->loctab_size;
      if (new_sz == 0) new_sz = 500;
      new_tab = VG_(arena_malloc)(VG_AR_SYMTAB, new_sz * sizeof(RiLoc) );
      if (si->loctab != NULL) {
         for (i = 0; i < si->loctab_used; i++)
            new_tab[i] = si->loctab[i];
         VG_(arena_free)(VG_AR_SYMTAB, si->loctab);
      }
      si->loctab = new_tab;
      si->loctab_size = new_sz;
   }

   si->loctab[si->loctab_used] = *loc;
   si->loctab_used++;
   vg_assert(si->loctab_used <= si->loctab_size);
}


/* Top-level place to call to add a source-location mapping entry. */

void ML_(addLineInfo) ( SegInfo* si,
			Char*    filename,
			Char*    dirname, /* NULL == directory is unknown */
			Addr     this,
			Addr     next,
			Int      lineno,
			Int      entry /* only needed for debug printing */
		      )
{
   static const Bool debug = False;
   RiLoc loc;
   Int size = next - this;

   /* Ignore zero-sized locs */
   if (this == next) return;

   if (debug)
      VG_(printf)( "  src %s %s line %d %p-%p\n",
                   dirname ? dirname : (Char*)"(unknown)",
                   filename, lineno, this, next );

   /* Maximum sanity checking.  Some versions of GNU as do a shabby
    * job with stabs entries; if anything looks suspicious, revert to
    * a size of 1.  This should catch the instruction of interest
    * (since if using asm-level debug info, one instruction will
    * correspond to one line, unlike with C-level debug info where
    * multiple instructions can map to the one line), but avoid
    * catching any other instructions bogusly. */
   if (this > next) {
       if (VG_(clo_verbosity) > 2) {
           VG_(message)(Vg_DebugMsg, 
                        "warning: line info addresses out of order "
                        "at entry %d: 0x%x 0x%x", entry, this, next);
       }
       size = 1;
   }

   if (size > MAX_LOC_SIZE) {
       if (0)
       VG_(message)(Vg_DebugMsg, 
                    "warning: line info address range too large "
                    "at entry %d: %d", entry, size);
       size = 1;
   }

   /* vg_assert(this < si->start + si->size && next-1 >= si->start); */
   if (this >= si->start + si->size || next-1 < si->start) {
       if (0)
          VG_(message)(Vg_DebugMsg, 
                       "warning: ignoring line info entry falling "
                       "outside current SegInfo: %p %p %p %p",
                       si->start, si->start + si->size, 
                       this, next-1);
       return;
   }

   vg_assert(lineno >= 0);
   if (lineno > MAX_LINENO) {
      static Bool complained = False;
      if (!complained) {
         complained = True;
         VG_(message)(Vg_UserMsg, 
                      "warning: ignoring line info entry with "
                      "huge line number (%d)", lineno);
         VG_(message)(Vg_UserMsg, 
                      "         Can't handle line numbers "
                      "greater than %d, sorry", MAX_LINENO);
         VG_(message)(Vg_UserMsg, 
                      "(Nb: this message is only shown once)");
      }
      return;
   }

   loc.addr      = this;
   loc.size      = (UShort)size;
   loc.lineno    = lineno;
   loc.filename  = filename;
   loc.dirname   = dirname;

   if (0) VG_(message)(Vg_DebugMsg, 
		       "addLoc: addr %p, size %d, line %d, file %s",
		       this,size,lineno,filename);

   addLoc ( si, &loc );
}

static __inline__
void addScopeRange ( SegInfo* si, ScopeRange *range )
{
   Int    new_sz, i;
   ScopeRange* new_tab;

   /* Zero-sized scopes should have been ignored earlier */
   vg_assert(range->size > 0);

   if (si->scopetab_used == si->scopetab_size) {
      new_sz = 2 * si->scopetab_size;
      if (new_sz == 0) new_sz = 500;
      new_tab = VG_(arena_malloc)(VG_AR_SYMTAB, new_sz * sizeof(*new_tab) );
      if (si->scopetab != NULL) {
         for (i = 0; i < si->scopetab_used; i++)
            new_tab[i] = si->scopetab[i];
         VG_(arena_free)(VG_AR_SYMTAB, si->scopetab);
      }
      si->scopetab = new_tab;
      si->scopetab_size = new_sz;
   }

   si->scopetab[si->scopetab_used] = *range;
   si->scopetab_used++;
   vg_assert(si->scopetab_used <= si->scopetab_size);
}


/* Top-level place to call to add a source-location mapping entry. */

void ML_(addScopeInfo) ( SegInfo* si,
			 Addr     this,
			 Addr     next,
			 Scope    *scope)
{
   static const Bool debug = False;
   Int size = next - this;
   ScopeRange range;

   /* Ignore zero-sized or negative scopes */
   if (size <= 0) {
      if (debug)
	 VG_(printf)("ignoring zero-sized range, scope %p at %p\n", scope, this);
      return;
   }

   if (debug)
      VG_(printf)("adding scope range %p-%p (size=%d)  scope %p (%d)\n",
		  this, next, next-this, scope, scope->depth);

   range.addr    = this;
   range.size    = size;
   range.scope   = scope;

   addScopeRange ( si, &range );
}


/* Top-level place to call to add a CFI summary record.  The supplied
   CfiSI is copied. */
void ML_(addCfiSI) ( SegInfo* si, CfiSI* cfisi )
{
   static const Bool debug = False;
   UInt   new_sz, i;
   CfiSI* new_tab;

   if (debug) {
      VG_(printf)("adding CfiSI: ");
      ML_(ppCfiSI)(cfisi);
   }

   vg_assert(cfisi->len > 0 && cfisi->len < 2000000);

   /* Rule out ones which are completely outside the segment.  These
      probably indicate some kind of bug, but for the meantime ignore
      them. */
   if ( cfisi->base + cfisi->len - 1  <  si->start
        || si->start + si->size - 1 < cfisi->base ) {
      static Int complaints = 3;
      if (VG_(clo_trace_cfi) || complaints > 0) {
         complaints--;
         if (VG_(clo_verbosity) > 1) {
            VG_(message)(
               Vg_DebugMsg,
               "warning: CfiSI %p .. %p outside segment %p .. %p",
               cfisi->base, 
               cfisi->base + cfisi->len - 1,
               si->start,
               si->start + si->size - 1 
            );
         }
         if (VG_(clo_trace_cfi)) 
            ML_(ppCfiSI)(cfisi);
      }
      return;
   }

   if (si->cfisi_used == si->cfisi_size) {
      new_sz = 2 * si->cfisi_size;
      if (new_sz == 0) new_sz = 20;
      new_tab = VG_(arena_malloc)(VG_AR_SYMTAB, new_sz * sizeof(CfiSI) );
      if (si->cfisi != NULL) {
         for (i = 0; i < si->cfisi_used; i++)
            new_tab[i] = si->cfisi[i];
         VG_(arena_free)(VG_AR_SYMTAB, si->cfisi);
      }
      si->cfisi = new_tab;
      si->cfisi_size = new_sz;
   }

   si->cfisi[si->cfisi_used] = *cfisi;
   si->cfisi_used++;
   vg_assert(si->cfisi_used <= si->cfisi_size);
}


/*------------------------------------------------------------*/
/*--- Helpers                                              ---*/
/*------------------------------------------------------------*/

/* Non-fatal -- use vg_panic if terminal. */
void ML_(symerr) ( Char* msg )
{
   if (VG_(clo_verbosity) > 1)
      VG_(message)(Vg_DebugMsg,"%s", msg );
}


/* Print a symbol. */
static
void printSym ( SegInfo* si, Int i )
{
  VG_(printf)( "%5d:  %8p .. %8p (%d)      %s\n",
               i,
               si->symtab[i].addr, 
               si->symtab[i].addr + si->symtab[i].size - 1, si->symtab[i].size,
	       si->symtab[i].name );
}

#define TRACE_SYMTAB(format, args...) \
   if (VG_(clo_trace_symtab)) { VG_(printf)(format, ## args); }


#if 0
/* Print the entire sym tab. */
static __attribute__ ((unused))
void printSymtab ( void )
{
   Int i;
   VG_(printf)("\n------ BEGIN vg_symtab ------\n");
   for (i = 0; i < vg_symtab_used; i++)
      printSym(i);
   VG_(printf)("------ BEGIN vg_symtab ------\n");
}
#endif

#if 0
/* Paranoid strcat. */
static
void safeCopy ( UChar* dst, UInt maxlen, UChar* src )
{
   UInt i = 0, j = 0;
   while (True) {
      if (i >= maxlen) return;
      if (dst[i] == 0) break;
      i++;
   }
   while (True) {
      if (i >= maxlen) return;
      dst[i] = src[j];
      if (src[j] == 0) return;
      i++; j++;
   }
}
#endif


/*------------------------------------------------------------*/
/*--- Canonicalisers                                       ---*/
/*------------------------------------------------------------*/

/* Sort the symtab by starting address, and emit warnings if any
   symbols have overlapping address ranges.  We use that old chestnut,
   shellsort.  Mash the table around so as to establish the property
   that addresses are in order and the ranges to not overlap.  This
   facilitates using binary search to map addresses to symbols when we
   come to query the table.
*/
static Int compare_RiSym(void *va, void *vb) {
   RiSym *a = (RiSym *)va;
   RiSym *b = (RiSym *)vb;
   
   if (a->addr < b->addr) return -1;
   if (a->addr > b->addr) return  1;
   return 0;
}

/* Two symbols have the same address.  Which name do we prefer?

   The general rule is to prefer the shorter symbol name.  If the
   symbol contains a '@', which means its versioned, then the length
   up to the '@' is used for length comparison purposes (so
   "foo@GLIBC_2.4.2" is considered shorter than "foobar"), but if two
   symbols have the same length, the one with the version string is
   preferred.  If all else fails, use alphabetical ordering.

   Very occasionally this goes wrong (eg. 'memcmp' and 'bcmp' are aliases
   in glibc, we choose the 'bcmp' symbol because it's shorter, so we
   can misdescribe memcmp() as bcmp()).  This is hard to avoid.  It's
   mentioned in the FAQ file.
 */
static RiSym *prefersym(RiSym *a, RiSym *b)
{
   Int lena, lenb;		/* full length */
   Int vlena, vlenb;		/* length without version */
   const Char *vpa, *vpb;

   vlena = lena = VG_(strlen)(a->name);
   vlenb = lenb = VG_(strlen)(b->name);

   vpa = VG_(strchr)(a->name, '@');
   vpb = VG_(strchr)(b->name, '@');

   if (vpa)
      vlena = vpa - a->name;
   if (vpb)
      vlenb = vpb - b->name;

   TRACE_SYMTAB("choosing between '%s' and '%s'\n", a->name, b->name);

   /* MPI hack: prefer PMPI_Foo over MPI_Foo */
   if (0==VG_(strncmp)(a->name, "MPI_", 4)
       && 0==VG_(strncmp)(b->name, "PMPI_", 5)
       && 0==VG_(strcmp)(a->name, 1+b->name))
      return b;
   else
   if (0==VG_(strncmp)(b->name, "MPI_", 4)
       && 0==VG_(strncmp)(a->name, "PMPI_", 5)
       && 0==VG_(strcmp)(b->name, 1+a->name))
      return a;

   /* Select the shortest unversioned name */
   if (vlena < vlenb)
      return a;
   else if (vlenb < vlena)
      return b;

   /* Equal lengths; select the versioned name */
   if (vpa && !vpb)
      return a;
   if (vpb && !vpa)
      return b;

   /* Either both versioned or neither is versioned; select them
      alphabetically */
   if (VG_(strcmp)(a->name, b->name) < 0)
      return a;
   else
      return b;
}

static 
void canonicaliseSymtab ( SegInfo* si )
{
   Int   i, j, n_merged, n_truncated;
   Addr  s1, s2, e1, e2;

#  define SWAP(ty,aa,bb) \
      do { ty tt = (aa); (aa) = (bb); (bb) = tt; } while (0)

   if (si->symtab_used == 0)
      return;

   VG_(ssort)(si->symtab, si->symtab_used, sizeof(*si->symtab), compare_RiSym);

  cleanup_more:
 
   /* If two symbols have identical address ranges, we pick one
      using prefersym() (see it for details). */
   do {
      n_merged = 0;
      j = si->symtab_used;
      si->symtab_used = 0;
      for (i = 0; i < j; i++) {
         if (i < j-1
             && si->symtab[i].addr   == si->symtab[i+1].addr
             && si->symtab[i].size   == si->symtab[i+1].size) {
            n_merged++;
            /* merge the two into one */
	    si->symtab[si->symtab_used++] = *prefersym(&si->symtab[i], &si->symtab[i+1]);
            i++;
         } else {
            si->symtab[si->symtab_used++] = si->symtab[i];
         }
      }
      TRACE_SYMTAB( "%d merged\n", n_merged);
   }
   while (n_merged > 0);

   /* Detect and "fix" overlapping address ranges. */
   n_truncated = 0;

   for (i = 0; i < ((Int)si->symtab_used) -1; i++) {

      vg_assert(si->symtab[i].addr <= si->symtab[i+1].addr);

      /* Check for common (no overlap) case. */ 
      if (si->symtab[i].addr + si->symtab[i].size 
          <= si->symtab[i+1].addr)
         continue;

      /* There's an overlap.  Truncate one or the other. */
      if (VG_(clo_trace_symtab)) {
         VG_(printf)("overlapping address ranges in symbol table\n\t");
         printSym(si,i);
         VG_(printf)("\t");
         printSym(si,i+1);
         VG_(printf)("\n");
      }

      /* Truncate one or the other. */
      s1 = si->symtab[i].addr;
      s2 = si->symtab[i+1].addr;
      e1 = s1 + si->symtab[i].size - 1;
      e2 = s2 + si->symtab[i+1].size - 1;
      if (s1 < s2) {
         e1 = s2-1;
      } else {
         vg_assert(s1 == s2);
         if (e1 > e2) { 
            s1 = e2+1; SWAP(Addr,s1,s2); SWAP(Addr,e1,e2); 
         } else 
         if (e1 < e2) {
            s2 = e1+1;
         } else {
	   /* e1 == e2.  Identical addr ranges.  We'll eventually wind
              up back at cleanup_more, which will take care of it. */
	 }
      }
      si->symtab[i].addr   = s1;
      si->symtab[i+1].addr = s2;
      si->symtab[i].size   = e1 - s1 + 1;
      si->symtab[i+1].size = e2 - s2 + 1;
      vg_assert(s1 <= s2);
      vg_assert(si->symtab[i].size > 0);
      vg_assert(si->symtab[i+1].size > 0);
      /* It may be that the i+1 entry now needs to be moved further
         along to maintain the address order requirement. */
      j = i+1;
      while (j < ((Int)si->symtab_used)-1 
             && si->symtab[j].addr > si->symtab[j+1].addr) {
         SWAP(RiSym,si->symtab[j],si->symtab[j+1]);
         j++;
      }
      n_truncated++;
   }

   if (n_truncated > 0) goto cleanup_more;

   /* Ensure relevant postconditions hold. */
   for (i = 0; i < ((Int)si->symtab_used)-1; i++) {
      /* No zero-sized symbols. */
      vg_assert(si->symtab[i].size > 0);
      /* In order. */
      vg_assert(si->symtab[i].addr < si->symtab[i+1].addr);
      /* No overlaps. */
      vg_assert(si->symtab[i].addr + si->symtab[i].size - 1
                < si->symtab[i+1].addr);
   }
#  undef SWAP
}

/* Sort the scope range table by starting address.  Mash the table
   around so as to establish the property that addresses are in order
   and the ranges do not overlap.  This facilitates using binary
   search to map addresses to scopes when we come to query the
   table.
*/
static Int compare_ScopeRange(void *va, void *vb) {
   ScopeRange *a = (ScopeRange *)va;
   ScopeRange *b = (ScopeRange *)vb;
   
   if (a->addr < b->addr) return -1;
   if (a->addr > b->addr) return  1;
   return 0;
}

static 
void canonicaliseScopetab ( SegInfo* si )
{
   Int i,j;

   if (si->scopetab_used == 0)
      return;

   /* Sort by start address. */
   VG_(ssort)(si->scopetab, si->scopetab_used, sizeof(*si->scopetab), 
	      compare_ScopeRange);

   /* If two adjacent entries overlap, truncate the first. */
   for (i = 0; i < si->scopetab_used-1; i++) {
      if (si->scopetab[i].addr + si->scopetab[i].size > si->scopetab[i+1].addr) {
         Int new_size = si->scopetab[i+1].addr - si->scopetab[i].addr;

         if (new_size < 0)
            si->scopetab[i].size = 0;
         else
	    si->scopetab[i].size = new_size;
      }
   }

   /* Zap any zero-sized entries resulting from the truncation
      process. */
   j = 0;
   for (i = 0; i < si->scopetab_used; i++) {
      if (si->scopetab[i].size > 0) {
         if (j != i)
            si->scopetab[j] = si->scopetab[i];
         j++;
      }
   }
   si->scopetab_used = j;

   /* Ensure relevant postconditions hold. */
   for (i = 0; i < si->scopetab_used-1; i++) {
      /* 
      VG_(printf)("%d   (%d) %d 0x%x\n", 
                   i, si->scopetab[i+1].confident, 
                   si->scopetab[i+1].size, si->scopetab[i+1].addr );
      */
      /* No zero-sized symbols. */
      vg_assert(si->scopetab[i].size > 0);
      /* In order. */
      if (si->scopetab[i].addr >= si->scopetab[i+1].addr)
	 VG_(printf)("si->scopetab[%d] = %p,size=%d [%d] = %p,size=%d\n",
		     i, si->scopetab[i].addr, si->scopetab[i].size,
		     i+1, si->scopetab[i+1].addr, si->scopetab[i+1].size);
      vg_assert(si->scopetab[i].addr < si->scopetab[i+1].addr);
      /* No overlaps. */
      vg_assert(si->scopetab[i].addr + si->scopetab[i].size - 1
                < si->scopetab[i+1].addr);
   }
}


/* Sort the location table by starting address.  Mash the table around
   so as to establish the property that addresses are in order and the
   ranges do not overlap.  This facilitates using binary search to map
   addresses to locations when we come to query the table.  
*/
static Int compare_RiLoc(void *va, void *vb) {
   RiLoc *a = (RiLoc *)va;
   RiLoc *b = (RiLoc *)vb;

   if (a->addr < b->addr) return -1;
   if (a->addr > b->addr) return  1;
   return 0;
}

static 
void canonicaliseLoctab ( SegInfo* si )
{
   Int i, j;

#  define SWAP(ty,aa,bb) \
      do { ty tt = (aa); (aa) = (bb); (bb) = tt; } while (0);

   if (si->loctab_used == 0)
      return;

   /* Sort by start address. */
   VG_(ssort)(si->loctab, si->loctab_used, sizeof(*si->loctab), compare_RiLoc);

   /* If two adjacent entries overlap, truncate the first. */
   for (i = 0; i < ((Int)si->loctab_used)-1; i++) {
      vg_assert(si->loctab[i].size < 10000);
      if (si->loctab[i].addr + si->loctab[i].size > si->loctab[i+1].addr) {
         /* Do this in signed int32 because the actual .size fields
            are only 12 bits. */
         Int new_size = si->loctab[i+1].addr - si->loctab[i].addr;
         if (new_size < 0) {
            si->loctab[i].size = 0;
         } else
         if (new_size > MAX_LOC_SIZE) {
           si->loctab[i].size = MAX_LOC_SIZE;
         } else {
           si->loctab[i].size = (UShort)new_size;
         }
      }
   }

   /* Zap any zero-sized entries resulting from the truncation
      process. */
   j = 0;
   for (i = 0; i < (Int)si->loctab_used; i++) {
      if (si->loctab[i].size > 0) {
         if (j != i)
            si->loctab[j] = si->loctab[i];
         j++;
      }
   }
   si->loctab_used = j;

   /* Ensure relevant postconditions hold. */
   for (i = 0; i < ((Int)si->loctab_used)-1; i++) {
      /* 
      VG_(printf)("%d   (%d) %d 0x%x\n", 
                   i, si->loctab[i+1].confident, 
                   si->loctab[i+1].size, si->loctab[i+1].addr );
      */
      /* No zero-sized symbols. */
      vg_assert(si->loctab[i].size > 0);
      /* In order. */
      vg_assert(si->loctab[i].addr < si->loctab[i+1].addr);
      /* No overlaps. */
      vg_assert(si->loctab[i].addr + si->loctab[i].size - 1
                < si->loctab[i+1].addr);
   }
#  undef SWAP
}


/* Sort the call-frame-info table by starting address.  Mash the table
   around so as to establish the property that addresses are in order
   and the ranges do not overlap.  This facilitates using binary
   search to map addresses to locations when we come to query the
   table.  

   Also, set cfisi_minaddr and cfisi_maxaddr to be the min and max of
   any of the address ranges contained in cfisi[0 .. cfisi_used-1], so
   as to facilitate rapidly skipping this SegInfo when looking for an
   address which falls outside that range.
*/
static Int compare_CfiSI(void *va, void *vb) {
   CfiSI *a = (CfiSI*)va;
   CfiSI *b = (CfiSI*)vb;

   if (a->base < b->base) return -1;
   if (a->base > b->base) return  1;
   return 0;
}

static
void canonicaliseCfiSI ( SegInfo* si )
{
   Int   i, j;
   const Addr minAddr = 0;
   const Addr maxAddr = ~minAddr;

   /* Note: take care in here.  si->cfisi can be NULL, in which
      case _used and _size fields will be zero. */
   if (si->cfisi == NULL) {
      vg_assert(si->cfisi_used == 0);
      vg_assert(si->cfisi_size == 0);
   }

   /* Set cfisi_minaddr and cfisi_maxaddr to summarise the entire
      address range contained in cfisi[0 .. cfisi_used-1]. */
   si->cfisi_minaddr = maxAddr; 
   si->cfisi_maxaddr = minAddr;
   for (i = 0; i < (Int)si->cfisi_used; i++) {
      Addr here_min = si->cfisi[i].base;
      Addr here_max = si->cfisi[i].base + si->cfisi[i].len - 1;
      if (here_min < si->cfisi_minaddr)
         si->cfisi_minaddr = here_min;
      if (here_max > si->cfisi_maxaddr)
         si->cfisi_maxaddr = here_max;
   }

   if (VG_(clo_trace_cfi))
      VG_(printf)("canonicaliseCfiSI: %d entries, %p .. %p\n", 
                  si->cfisi_used,
	          si->cfisi_minaddr, si->cfisi_maxaddr);

   /* Sort the cfisi array by base address. */
   VG_(ssort)(si->cfisi, si->cfisi_used, sizeof(*si->cfisi), compare_CfiSI);

   /* If two adjacent entries overlap, truncate the first. */
   for (i = 0; i < (Int)si->cfisi_used-1; i++) {
      if (si->cfisi[i].base + si->cfisi[i].len > si->cfisi[i+1].base) {
         Int new_len = si->cfisi[i+1].base - si->cfisi[i].base;
         /* how could it be otherwise?  The entries are sorted by the
            .base field. */         
         vg_assert(new_len >= 0);
	 vg_assert(new_len <= si->cfisi[i].len);
         si->cfisi[i].len = new_len;
      }
   }

   /* Zap any zero-sized entries resulting from the truncation
      process. */
   j = 0;
   for (i = 0; i < (Int)si->cfisi_used; i++) {
      if (si->cfisi[i].len > 0) {
         if (j != i)
            si->cfisi[j] = si->cfisi[i];
         j++;
      }
   }
   /* VG_(printf)("XXXXXXXXXXXXX %d %d\n", si->cfisi_used, j); */
   si->cfisi_used = j;

   /* Ensure relevant postconditions hold. */
   for (i = 0; i < (Int)si->cfisi_used; i++) {
      /* No zero-length ranges. */
      vg_assert(si->cfisi[i].len > 0);
      /* Makes sense w.r.t. summary address range */
      vg_assert(si->cfisi[i].base >= si->cfisi_minaddr);
      vg_assert(si->cfisi[i].base + si->cfisi[i].len - 1
                <= si->cfisi_maxaddr);

      if (i < si->cfisi_used - 1) {
         /*
         if (!(si->cfisi[i].base < si->cfisi[i+1].base)) {
            VG_(printf)("\nOOO cfisis:\n");
            ML_(ppCfiSI)(&si->cfisi[i]);
            ML_(ppCfiSI)(&si->cfisi[i+1]);
         }
         */
         /* In order. */
         vg_assert(si->cfisi[i].base < si->cfisi[i+1].base);
         /* No overlaps. */
         vg_assert(si->cfisi[i].base + si->cfisi[i].len - 1
                   < si->cfisi[i+1].base);
      }
   }

}


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- Read symbol table and line info from ELF files.      ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

/* Identify an ELF object file. */

static Bool is_elf_object_file(const void *buf)
{
   ElfXX_Ehdr *ehdr = (ElfXX_Ehdr *)buf;
   Int ok = 1;

   ok &= (ehdr->e_ident[EI_MAG0] == 0x7F
          && ehdr->e_ident[EI_MAG1] == 'E'
          && ehdr->e_ident[EI_MAG2] == 'L'
          && ehdr->e_ident[EI_MAG3] == 'F');
   ok &= (ehdr->e_ident[EI_CLASS] == VG_ELF_CLASS
          && ehdr->e_ident[EI_DATA] == VG_ELF_DATA2XXX
          && ehdr->e_ident[EI_VERSION] == EV_CURRENT);
   ok &= (ehdr->e_type == ET_EXEC || ehdr->e_type == ET_DYN);
   ok &= (ehdr->e_machine == VG_ELF_MACHINE);
   ok &= (ehdr->e_version == EV_CURRENT);
   ok &= (ehdr->e_shstrndx != SHN_UNDEF);
   ok &= (ehdr->e_shoff != 0 && ehdr->e_shnum != 0);
   ok &= (ehdr->e_phoff != 0 && ehdr->e_phnum != 0);

   if (ok)
      return True;
   else
      return False;
}


/* Show a raw ELF symbol, given its in-image address and name. */

static
void show_raw_elf_symbol ( Int i, 
                           ElfXX_Sym* sym, Char* sym_name, Addr sym_addr,
                           Bool ppc64_linux_format )
{
   HChar* space = ppc64_linux_format ? "                  " : "";
   VG_(printf)("raw symbol [%4d]: ", i);
   switch (ELFXX_ST_BIND(sym->st_info)) {
      case STB_LOCAL:  VG_(printf)("LOC "); break;
      case STB_GLOBAL: VG_(printf)("GLO "); break;
      case STB_WEAK:   VG_(printf)("WEA "); break;
      case STB_LOPROC: VG_(printf)("lop "); break;
      case STB_HIPROC: VG_(printf)("hip "); break;
      default:         VG_(printf)("??? "); break;
   }
   switch (ELFXX_ST_TYPE(sym->st_info)) {
      case STT_NOTYPE:  VG_(printf)("NOT "); break;
      case STT_OBJECT:  VG_(printf)("OBJ "); break;
      case STT_FUNC:    VG_(printf)("FUN "); break;
      case STT_SECTION: VG_(printf)("SEC "); break;
      case STT_FILE:    VG_(printf)("FIL "); break;
      case STT_LOPROC:  VG_(printf)("lop "); break;
      case STT_HIPROC:  VG_(printf)("hip "); break;
      default:          VG_(printf)("??? "); break;
   }
   VG_(printf)(": val %010p, %ssz %4d  %s\n",
               sym_addr, space, sym->st_size,
               ( sym->st_name ? sym_name : (Char*)"NONAME" ) ); 
}               


/* Decide whether SYM is something we should collect, and if so, copy
   relevant info to the _OUT arguments.  For {x86,amd64,ppc32}-linux
   this is straightforward - the name, address, size are copied out
   unchanged.

   For ppc64-linux it's more complex.  If the symbol is seen to be in
   the .opd section, it is taken to be a function descriptor, and so
   a dereference is attempted, in order to get hold of the real entry
   point address.  Also as part of the dereference, there is an attempt
   to calculate the TOC pointer (R2 value) associated with the symbol.

   To support the ppc64-linux pre-"dotless" ABI (prior to gcc 4.0.0),
   if the symbol is seen to be outside the .opd section and its name
   starts with a dot, an .opd deference is not attempted, and no TOC
   pointer is calculated, but the the leading dot is removed from the
   name.

   As a result, on ppc64-linux, the caller of this function may have
   to piece together the real size, address, name of the symbol from
   multiple calls to this function.  Ugly and confusing.
*/
static 
Bool get_elf_symbol_info ( 
        /* INPUTS */
        SegInfo*   si,        /* containing SegInfo */
        ElfXX_Sym* sym,       /* ELF symbol */
        Char*      sym_name,  /* name */
        Addr       sym_addr,  /* declared address */
        UChar*     opd_filea, /* oimage of .opd sec (ppc64-linux only) */
        /* OUTPUTS */
        Char** sym_name_out,   /* name we should record */
        Addr*  sym_addr_out,   /* addr we should record */
        Int*   sym_size_out,   /* symbol size */
        Addr*  sym_tocptr_out, /* ppc64-linux only: R2 value to be
                                  used on entry */
        Bool*  from_opd_out    /* ppc64-linux only: did we deref an
                                  .opd entry? */ 
     )
{
   Bool plausible, is_in_opd;

   /* Set defaults */
   *sym_name_out   = sym_name;
   *sym_addr_out   = sym_addr;
   *sym_size_out   = (Int)sym->st_size;
   *sym_tocptr_out = 0; /* unknown/inapplicable */
   *from_opd_out   = False;

   /* Figure out if we're interested in the symbol.  Firstly, is it of
      the right flavour?  */
   plausible 
      = (ELFXX_ST_BIND(sym->st_info) == STB_GLOBAL 
         || ELFXX_ST_BIND(sym->st_info) == STB_LOCAL 
         || ELFXX_ST_BIND(sym->st_info) == STB_WEAK
        )
        &&
        (ELFXX_ST_TYPE(sym->st_info) == STT_FUNC 
         || (VG_(needs).data_syms 
             && ELFXX_ST_TYPE(sym->st_info) == STT_OBJECT)
        );

#  if defined(VGP_ppc64_linux)
   /* Allow STT_NOTYPE in the very special case where we're running on
      ppc64-linux and the symbol is one which the .opd-chasing hack
      below will chase. */
   if (!plausible
       && ELFXX_ST_TYPE(sym->st_info) == STT_NOTYPE
       && sym->st_size > 0
       && si->opd_start_vma != 0
       && sym_addr >= si->opd_start_vma
       && sym_addr <  si->opd_start_vma + si->opd_size)
      plausible = True;
#  endif

   if (!plausible)
      return False;

   /* Ignore if nameless, or zero-sized. */
   if (sym->st_name == (ElfXX_Word)NULL
       || /* VG_(strlen)(sym_name) == 0 */
          /* equivalent but cheaper ... */
          sym_name[0] == 0
       || sym->st_size == 0) {
      TRACE_SYMTAB("    ignore -- size=0: %s\n", sym_name);
      return False;
   }

   /* This seems to significantly reduce the number of junk
      symbols, and particularly reduces the number of
      overlapping address ranges.  Don't ask me why ... */
   if ((Int)sym->st_value == 0) {
      TRACE_SYMTAB( "    ignore -- valu=0: %s\n", sym_name);
      return False;
   }

   /* If it's apparently in a GOT or PLT, it's really a reference to a
      symbol defined elsewhere, so ignore it. */
   if (si->got_start_vma != 0
       && sym_addr >= si->got_start_vma 
       && sym_addr <  si->got_start_vma + si->got_size) {
      TRACE_SYMTAB("    ignore -- in GOT: %s\n", sym_name);
      return False;
   }
   if (si->plt_start_vma != 0
       && sym_addr >= si->plt_start_vma
       && sym_addr <  si->plt_start_vma + si->plt_size) {
      TRACE_SYMTAB("    ignore -- in PLT: %s\n", sym_name);
      return False;
   }

   /* ppc64-linux nasty hack: if the symbol is in an .opd section,
      then really what we have is the address of a function
      descriptor.  So use the first word of that as the function's
      text.

      See thread starting at
      http://gcc.gnu.org/ml/gcc-patches/2004-08/msg00557.html
   */
   is_in_opd = False;

   if (si->opd_start_vma != 0
       && sym_addr >= si->opd_start_vma
       && sym_addr <  si->opd_start_vma + si->opd_size) {
#     if !defined(VGP_ppc64_linux)
      TRACE_SYMTAB("    ignore -- in OPD: %s\n", sym_name);
      return False;
#     else
      Int    offset_in_opd;
      ULong* fn_descr;

      if (0) VG_(printf)("opdXXX: si->offset %p, sym_addr %p\n", 
                         (void*)(si->offset), (void*)sym_addr);

      if (!VG_IS_8_ALIGNED(sym_addr)) {
         TRACE_SYMTAB("    ignore -- not 8-aligned: %s\n", sym_name);
         return False;
      }

      /* sym_addr is a vma pointing into the .opd section.  We know
         the vma of the opd section start, so we can figure out how
         far into the opd section this is. */

      offset_in_opd = (Addr)sym_addr - (Addr)(si->opd_start_vma);
      if (offset_in_opd < 0 || offset_in_opd >= si->opd_size) {
         TRACE_SYMTAB("    ignore -- invalid OPD offset: %s\n", sym_name);
         return False;
      }

      /* Now we want to know what's at that offset in the .opd
         section.  We can't look in the running image since it won't
         necessarily have been mapped.  But we can consult the oimage.
         opd_filea is the start address of the .opd in the oimage.
         Hence: */

      fn_descr = (ULong*)(opd_filea + offset_in_opd);

      if (0) VG_(printf)("opdXXY: offset %d,  fn_descr %p\n", 
                         offset_in_opd, fn_descr);
      if (0) VG_(printf)("opdXXZ: *fn_descr %p\n", (void*)(fn_descr[0]));

      sym_addr = fn_descr[0];

      /* Hopefully sym_addr is now an offset into the text section.
         Problem is, where did the text section get mapped?  Well,
         this SegInfo (si) exists because a text section got mapped,
         and it got mapped to si->start.  Hence add si->start to the
         sym_addr to get the real vma. */

      sym_addr += si->offset;
      *sym_addr_out   = sym_addr;
      *sym_tocptr_out = fn_descr[1] + si->offset;
      *from_opd_out   = True;
      is_in_opd = True;

      /* Do a final sanity check: if the symbol falls outside the
         SegInfo's mapped range, ignore it.  Since sym_addr has been
         updated, that can be achieved simply by falling through to
         the test below. */

#     endif /* ppc64-linux nasty hack */
   }

   /* Here's yet another ppc64-linux hack.  Get rid of leading dot if
      the symbol is outside .opd. */
#  if defined(VGP_ppc64_linux)
   if (si->opd_start_vma != 0
       && !is_in_opd
       && sym_name[0] == '.') {
      vg_assert(!(*from_opd_out));
      *sym_name_out = &sym_name[1];
   }
#  endif

   /* If no part of the symbol falls within the mapped range,
      ignore it. */
   if (*sym_addr_out + *sym_size_out <= si->start
       || *sym_addr_out >= si->start+si->size) {
      TRACE_SYMTAB( "   ignore -- outside mapped range\n" );
      return False;
   }

#  if defined(VGP_ppc64_linux)
   /* It's crucial that we never add symbol addresses in the .opd
      section.  This would completely mess up function redirection and
      intercepting.  This assert ensures that any symbols that make it
      into the symbol table on ppc64-linux don't point into .opd. */
   if (si->opd_start_vma != 0) {
      vg_assert(*sym_addr_out + *sym_size_out <= si->opd_start_vma
                || *sym_addr_out >= si->opd_start_vma + si->opd_size);
   }
#  endif

   /* Acquire! */
   return True;
}


/* Read an ELF symbol table (normal or dynamic).  This one is for the
   "normal" case ({x86,amd64,ppc32}-linux). */
static
__attribute__((unused)) /* not referred to on all targets */
void read_elf_symtab__normal( 
        SegInfo* si, Char* tab_name,
        ElfXX_Sym* o_symtab, UInt o_symtab_sz,
        UChar*     o_strtab, UInt o_strtab_sz,
        UChar*     opd_filea /* ppc64-linux only */ 
     )
{
   Int        i;
   Addr       sym_addr, sym_addr_really;
   Char      *sym_name, *sym_name_really;
   Int        sym_size;
   Addr       sym_tocptr;
   Bool       from_opd;
   RiSym      risym;
   ElfXX_Sym *sym;

   if (o_strtab == NULL || o_symtab == NULL) {
      Char buf[80];
      vg_assert(VG_(strlen)(tab_name) < 40);
      VG_(sprintf)(buf, "   object doesn't have a %s", tab_name);
      ML_(symerr)(buf);
      return;
   }

   TRACE_SYMTAB("\nReading (ELF, standard) %s (%d entries)\n", tab_name, 
                o_symtab_sz/sizeof(ElfXX_Sym) );

   /* Perhaps should start at i = 1; ELF docs suggest that entry
      0 always denotes 'unknown symbol'. */
   for (i = 1; i < (Int)(o_symtab_sz/sizeof(ElfXX_Sym)); i++) {
      sym      = & o_symtab[i];
      sym_name = (Char*)(o_strtab + sym->st_name);
      sym_addr = si->offset + sym->st_value;

      if (VG_(clo_trace_symtab))
         show_raw_elf_symbol(i, sym, sym_name, sym_addr, False);

      if (get_elf_symbol_info(si, sym, sym_name, sym_addr, opd_filea,
                              &sym_name_really, 
                              &sym_addr_really,
                              &sym_size,
                              &sym_tocptr,
                              &from_opd)) {

         risym.addr   = sym_addr_really;
         risym.size   = sym_size;
         risym.name   = ML_(addStr) ( si, sym_name_really, -1 );
         risym.tocptr = sym_tocptr;
         vg_assert(risym.name != NULL);
         vg_assert(risym.tocptr == 0); /* has no role except on ppc64-linux */
         addSym ( si, &risym );

         if (VG_(clo_trace_symtab)) {
            VG_(printf)("    record [%4d]:          "
                        " val %010p, sz %4d  %s\n",
                        i, (void*)risym.addr, (Int)risym.size, 
                           (HChar*)risym.name
            );
         }

      }
   }
}


/* Read an ELF symbol table (normal or dynamic).  This one is for
   ppc64-linux, which requires special treatment. */

typedef
   struct { 
      Addr  addr; 
      Char* name; 
   }
   TempSymKey;

typedef
   struct {
      TempSymKey key;
      Addr       tocptr;
      Int        size;
      Bool       from_opd;
   }
   TempSym;

static Word cmp_TempSymKey ( TempSymKey* key1, TempSym* elem2 ) {
   if (key1->addr < elem2->key.addr) return -1;
   if (key1->addr > elem2->key.addr) return 1;
   return (Word)VG_(strcmp)(key1->name, elem2->key.name);
}
static void* oset_malloc ( SizeT szB ) { 
   return VG_(arena_malloc)(VG_AR_SYMTAB, szB);
}
static void oset_free ( void* p ) {
   VG_(arena_free)(VG_AR_SYMTAB, p);
}

static
__attribute__((unused)) /* not referred to on all targets */
void read_elf_symtab__ppc64_linux( 
        SegInfo* si, Char* tab_name,
        ElfXX_Sym* o_symtab, UInt o_symtab_sz,
        UChar*     o_strtab, UInt o_strtab_sz,
        UChar*     opd_filea /* ppc64-linux only */ 
     )
{
   Int         i, old_size;
   Addr        sym_addr, sym_addr_really;
   Char       *sym_name, *sym_name_really;
   Int         sym_size;
   Addr        sym_tocptr, old_tocptr;
   Bool        from_opd, modify_size, modify_tocptr;
   RiSym       risym;
   ElfXX_Sym  *sym;
   OSet       *oset;
   TempSymKey  key;
   TempSym    *elem;
   TempSym    *prev;

   if (o_strtab == NULL || o_symtab == NULL) {
      Char buf[80];
      vg_assert(VG_(strlen)(tab_name) < 40);
      VG_(sprintf)(buf, "   object doesn't have a %s", tab_name);
      ML_(symerr)(buf);
      return;
   }

   TRACE_SYMTAB("\nReading (ELF, ppc64-linux) %s (%d entries)\n", tab_name, 
                o_symtab_sz/sizeof(ElfXX_Sym) );

   oset = VG_(OSet_Create)( offsetof(TempSym,key), 
                            (OSetCmp_t)cmp_TempSymKey, 
                            oset_malloc, oset_free );
   vg_assert(oset);

   /* Perhaps should start at i = 1; ELF docs suggest that entry
      0 always denotes 'unknown symbol'. */
   for (i = 1; i < (Int)(o_symtab_sz/sizeof(ElfXX_Sym)); i++) {
      sym      = & o_symtab[i];
      sym_name = (Char*)(o_strtab + sym->st_name);
      sym_addr = si->offset + sym->st_value;

      if (VG_(clo_trace_symtab))
         show_raw_elf_symbol(i, sym, sym_name, sym_addr, True);

      if (get_elf_symbol_info(si, sym, sym_name, sym_addr, opd_filea,
                              &sym_name_really, 
                              &sym_addr_really,
                              &sym_size,
                              &sym_tocptr,
                              &from_opd)) {

         /* Check if we've seen this (name,addr) key before. */
         key.addr = sym_addr_really;
         key.name = sym_name_really;
         prev = VG_(OSet_Lookup)( oset, &key );

         if (prev) {

            /* Seen it before.  Fold in whatever new info we can. */
            modify_size   = False;
            modify_tocptr = False;
            old_size   = 0;
	    old_tocptr = 0;

            if (prev->from_opd && !from_opd 
                && (prev->size == 24 || prev->size == 16)
                && sym_size != prev->size) {
               /* Existing one is an opd-redirect, with a bogus size,
                  so the only useful new fact we have is the real size
                  of the symbol. */
               modify_size = True;
               old_size = prev->size;
               prev->size = sym_size;
            }
            else
            if (!prev->from_opd && from_opd
                && (sym_size == 24 || sym_size == 16)) {
               /* Existing one is non-opd, new one is opd.  What we
                  can acquire from the new one is the TOC ptr to be
                  used.  Since the existing sym is non-toc, it
                  shouldn't currently have an known TOC ptr. */
               vg_assert(prev->tocptr == 0);
               modify_tocptr = True;
               old_tocptr = prev->tocptr;
               prev->tocptr = sym_tocptr;
            }
            else {
               /* ignore. can we do better here? */
            }

            /* Only one or the other is possible (I think) */
	    vg_assert(!(modify_size && modify_tocptr));

            if (modify_size && VG_(clo_trace_symtab)) {
               VG_(printf)("    modify (old sz %4d)    "
                           " val %010p, toc %010p, sz %4d  %s\n",
                           old_size,
                           (void*) prev->key.addr, 
                           (void*) prev->tocptr,
                           (Int)   prev->size, 
                           (HChar*)prev->key.name
               );
            }
            if (modify_tocptr && VG_(clo_trace_symtab)) {
               VG_(printf)("    modify (upd tocptr)     "
                           " val %010p, toc %010p, sz %4d  %s\n",
                            (void*) prev->key.addr, 
                            (void*) prev->tocptr, 
                            (Int)   prev->size, 
                            (HChar*)prev->key.name
               );
            }

         } else {

            /* A new (name,addr) key.  Add and continue. */
            elem = VG_(OSet_AllocNode)(oset, sizeof(TempSym));
            vg_assert(elem);
            elem->key      = key;
            elem->tocptr   = sym_tocptr;
            elem->size     = sym_size;
            elem->from_opd = from_opd;
            VG_(OSet_Insert)(oset, elem);
            if (VG_(clo_trace_symtab)) {
               VG_(printf)("   to-oset [%4d]:          "
                           " val %010p, toc %010p, sz %4d  %s\n",
                           i, (void*) elem->key.addr,
                              (void*) elem->tocptr,
                              (Int)   elem->size, 
                              (HChar*)elem->key.name
               );
            }

         }
      }
   }

   /* All the syms that matter are in the oset.  Now pull them out,
      build a "standard" symbol table, and nuke the oset. */

   i = 0;
   VG_(OSet_ResetIter)( oset );

   while ( (elem = VG_(OSet_Next)(oset)) ) {
      risym.addr   = elem->key.addr;
      risym.size   = elem->size;
      risym.name   = ML_(addStr) ( si, elem->key.name, -1 );
      risym.tocptr = elem->tocptr;
      vg_assert(risym.name != NULL);

      addSym ( si, &risym );
      if (VG_(clo_trace_symtab)) {
         VG_(printf)("    record [%4d]:          "
                     " val %010p, toc %010p, sz %4d  %s\n",
                     i, (void*) risym.addr,
                        (void*) risym.tocptr,
                        (Int)   risym.size, 
                        (HChar*)risym.name
               );
      }
      i++;
   }

   VG_(OSet_Destroy)( oset, NULL );
}


/*
 * This routine for calculating the CRC for a separate debug file
 * is GPLed code borrowed from binutils.
 */
static UInt
calc_gnu_debuglink_crc32(UInt crc, const UChar *buf, Int len)
{
  static const UInt crc32_table[256] =
    {
      0x00000000, 0x77073096, 0xee0e612c, 0x990951ba, 0x076dc419,
      0x706af48f, 0xe963a535, 0x9e6495a3, 0x0edb8832, 0x79dcb8a4,
      0xe0d5e91e, 0x97d2d988, 0x09b64c2b, 0x7eb17cbd, 0xe7b82d07,
      0x90bf1d91, 0x1db71064, 0x6ab020f2, 0xf3b97148, 0x84be41de,
      0x1adad47d, 0x6ddde4eb, 0xf4d4b551, 0x83d385c7, 0x136c9856,
      0x646ba8c0, 0xfd62f97a, 0x8a65c9ec, 0x14015c4f, 0x63066cd9,
      0xfa0f3d63, 0x8d080df5, 0x3b6e20c8, 0x4c69105e, 0xd56041e4,
      0xa2677172, 0x3c03e4d1, 0x4b04d447, 0xd20d85fd, 0xa50ab56b,
      0x35b5a8fa, 0x42b2986c, 0xdbbbc9d6, 0xacbcf940, 0x32d86ce3,
      0x45df5c75, 0xdcd60dcf, 0xabd13d59, 0x26d930ac, 0x51de003a,
      0xc8d75180, 0xbfd06116, 0x21b4f4b5, 0x56b3c423, 0xcfba9599,
      0xb8bda50f, 0x2802b89e, 0x5f058808, 0xc60cd9b2, 0xb10be924,
      0x2f6f7c87, 0x58684c11, 0xc1611dab, 0xb6662d3d, 0x76dc4190,
      0x01db7106, 0x98d220bc, 0xefd5102a, 0x71b18589, 0x06b6b51f,
      0x9fbfe4a5, 0xe8b8d433, 0x7807c9a2, 0x0f00f934, 0x9609a88e,
      0xe10e9818, 0x7f6a0dbb, 0x086d3d2d, 0x91646c97, 0xe6635c01,
      0x6b6b51f4, 0x1c6c6162, 0x856530d8, 0xf262004e, 0x6c0695ed,
      0x1b01a57b, 0x8208f4c1, 0xf50fc457, 0x65b0d9c6, 0x12b7e950,
      0x8bbeb8ea, 0xfcb9887c, 0x62dd1ddf, 0x15da2d49, 0x8cd37cf3,
      0xfbd44c65, 0x4db26158, 0x3ab551ce, 0xa3bc0074, 0xd4bb30e2,
      0x4adfa541, 0x3dd895d7, 0xa4d1c46d, 0xd3d6f4fb, 0x4369e96a,
      0x346ed9fc, 0xad678846, 0xda60b8d0, 0x44042d73, 0x33031de5,
      0xaa0a4c5f, 0xdd0d7cc9, 0x5005713c, 0x270241aa, 0xbe0b1010,
      0xc90c2086, 0x5768b525, 0x206f85b3, 0xb966d409, 0xce61e49f,
      0x5edef90e, 0x29d9c998, 0xb0d09822, 0xc7d7a8b4, 0x59b33d17,
      0x2eb40d81, 0xb7bd5c3b, 0xc0ba6cad, 0xedb88320, 0x9abfb3b6,
      0x03b6e20c, 0x74b1d29a, 0xead54739, 0x9dd277af, 0x04db2615,
      0x73dc1683, 0xe3630b12, 0x94643b84, 0x0d6d6a3e, 0x7a6a5aa8,
      0xe40ecf0b, 0x9309ff9d, 0x0a00ae27, 0x7d079eb1, 0xf00f9344,
      0x8708a3d2, 0x1e01f268, 0x6906c2fe, 0xf762575d, 0x806567cb,
      0x196c3671, 0x6e6b06e7, 0xfed41b76, 0x89d32be0, 0x10da7a5a,
      0x67dd4acc, 0xf9b9df6f, 0x8ebeeff9, 0x17b7be43, 0x60b08ed5,
      0xd6d6a3e8, 0xa1d1937e, 0x38d8c2c4, 0x4fdff252, 0xd1bb67f1,
      0xa6bc5767, 0x3fb506dd, 0x48b2364b, 0xd80d2bda, 0xaf0a1b4c,
      0x36034af6, 0x41047a60, 0xdf60efc3, 0xa867df55, 0x316e8eef,
      0x4669be79, 0xcb61b38c, 0xbc66831a, 0x256fd2a0, 0x5268e236,
      0xcc0c7795, 0xbb0b4703, 0x220216b9, 0x5505262f, 0xc5ba3bbe,
      0xb2bd0b28, 0x2bb45a92, 0x5cb36a04, 0xc2d7ffa7, 0xb5d0cf31,
      0x2cd99e8b, 0x5bdeae1d, 0x9b64c2b0, 0xec63f226, 0x756aa39c,
      0x026d930a, 0x9c0906a9, 0xeb0e363f, 0x72076785, 0x05005713,
      0x95bf4a82, 0xe2b87a14, 0x7bb12bae, 0x0cb61b38, 0x92d28e9b,
      0xe5d5be0d, 0x7cdcefb7, 0x0bdbdf21, 0x86d3d2d4, 0xf1d4e242,
      0x68ddb3f8, 0x1fda836e, 0x81be16cd, 0xf6b9265b, 0x6fb077e1,
      0x18b74777, 0x88085ae6, 0xff0f6a70, 0x66063bca, 0x11010b5c,
      0x8f659eff, 0xf862ae69, 0x616bffd3, 0x166ccf45, 0xa00ae278,
      0xd70dd2ee, 0x4e048354, 0x3903b3c2, 0xa7672661, 0xd06016f7,
      0x4969474d, 0x3e6e77db, 0xaed16a4a, 0xd9d65adc, 0x40df0b66,
      0x37d83bf0, 0xa9bcae53, 0xdebb9ec5, 0x47b2cf7f, 0x30b5ffe9,
      0xbdbdf21c, 0xcabac28a, 0x53b39330, 0x24b4a3a6, 0xbad03605,
      0xcdd70693, 0x54de5729, 0x23d967bf, 0xb3667a2e, 0xc4614ab8,
      0x5d681b02, 0x2a6f2b94, 0xb40bbe37, 0xc30c8ea1, 0x5a05df1b,
      0x2d02ef8d
    };
  const UChar *end;

  crc = ~crc & 0xffffffff;
  for (end = buf + len; buf < end; ++ buf)
    crc = crc32_table[(crc ^ *buf) & 0xff] ^ (crc >> 8);
  return ~crc & 0xffffffff;;
}

/*
 * Try and open a separate debug file, ignoring any where the CRC does
 * not match the value from the main object file.
 */
static
Addr open_debug_file( Char* name, UInt crc, UInt* size )
{
   SysRes fd, sres;
   struct vki_stat stat_buf;
   UInt calccrc;

   fd = VG_(open)(name, VKI_O_RDONLY, 0);
   if (fd.isError)
      return 0;

   if (VG_(fstat)(fd.val, &stat_buf) != 0) {
      VG_(close)(fd.val);
      return 0;
   }

   if (VG_(clo_verbosity) > 1)
      VG_(message)(Vg_DebugMsg, "Reading debug info from %s...", name);

   *size = stat_buf.st_size;
   
   sres = VG_(am_mmap_file_float_valgrind)
             ( *size, VKI_PROT_READ, fd.val, 0 );

   VG_(close)(fd.val);
   
   if (sres.isError)
      return 0;

   calccrc = calc_gnu_debuglink_crc32(0, (UChar*)sres.val, *size);
   if (calccrc != crc) {
      SysRes res = VG_(am_munmap_valgrind)(sres.val, *size);
      vg_assert(!res.isError);
      if (VG_(clo_verbosity) > 1)
	 VG_(message)(Vg_DebugMsg, "... CRC mismatch (computed %08x wanted %08x)", calccrc, crc);
      return 0;
   }
   
   return sres.val;
}

/*
 * Try to find a separate debug file for a given object file.
 */
static
Addr find_debug_file( Char* objpath, Char* debugname, UInt crc, UInt* size )
{
   Char *objdir = VG_(arena_strdup)(VG_AR_SYMTAB, objpath);
   Char *objdirptr;
   Char *debugpath;
   Addr addr = 0;
  
   if ((objdirptr = VG_(strrchr)(objdir, '/')) != NULL)
      *objdirptr = '\0';

   debugpath = VG_(arena_malloc)(VG_AR_SYMTAB, VG_(strlen)(objdir) + VG_(strlen)(debugname) + 16);
   
   VG_(sprintf)(debugpath, "%s/%s", objdir, debugname);

   if ((addr = open_debug_file(debugpath, crc, size)) == 0) {
      VG_(sprintf)(debugpath, "%s/.debug/%s", objdir, debugname);
      if ((addr = open_debug_file(debugpath, crc, size)) == 0) {
         VG_(sprintf)(debugpath, "/usr/lib/debug%s/%s", objdir, debugname);
         addr = open_debug_file(debugpath, crc, size);
      }
   }

   VG_(arena_free)(VG_AR_SYMTAB, debugpath);
   VG_(arena_free)(VG_AR_SYMTAB, objdir);
   
   return addr;
}


/* The central function for reading ELF debug info.  For the
   object/exe specified by the SegInfo, find ELF sections, then read
   the symbols, line number info, file name info, CFA (stack-unwind
   info) and anything else we want, into the tables within the
   supplied SegInfo.
*/
static
Bool read_elf_debug_info ( SegInfo* si )
{
   Bool          res;
   ElfXX_Ehdr*   ehdr;       /* The ELF header                          */
   ElfXX_Shdr*   shdr;       /* The section table                       */
   UChar*        sh_strtab;  /* The section table's string table        */
   SysRes        fd, sres;
   Int           i;
   Bool          ok;
   Addr          oimage;
   UInt          n_oimage;
   Addr          dimage = 0;
   UInt          n_dimage = 0;
   struct vki_stat stat_buf;

   oimage = (Addr)NULL;
   if (VG_(clo_verbosity) > 1 || VG_(clo_trace_redir))
      VG_(message)(Vg_DebugMsg, "Reading syms from %s (%p)", 
                                si->filename, si->start );

   /* mmap the object image aboard, so that we can read symbols and
      line number info out of it.  It will be munmapped immediately
      thereafter; it is only aboard transiently. */

   fd = VG_(stat)(si->filename, &stat_buf);
   if (fd.isError) {
      ML_(symerr)("Can't stat .so/.exe (to determine its size)?!");
      return False;
   }
   n_oimage = stat_buf.st_size;

   fd = VG_(open)(si->filename, VKI_O_RDONLY, 0);
   if (fd.isError) {
      ML_(symerr)("Can't open .so/.exe to read symbols?!");
      return False;
   }

   sres = VG_(am_mmap_file_float_valgrind)
             ( n_oimage, VKI_PROT_READ, fd.val, 0 );

   VG_(close)(fd.val);

   if (sres.isError) {
      VG_(message)(Vg_UserMsg, "warning: mmap failed on %s", si->filename );
      VG_(message)(Vg_UserMsg, "         no symbols or debug info loaded" );
      return False;
   }

   oimage = sres.val;

   /* Ok, the object image is safely in oimage[0 .. n_oimage-1]. 
      Now verify that it is a valid ELF .so or executable image.
   */
   res = False;
   ok = (n_oimage >= sizeof(ElfXX_Ehdr));
   ehdr = (ElfXX_Ehdr*)oimage;

   if (ok)
      ok &= is_elf_object_file(ehdr);

   if (!ok) {
      ML_(symerr)("Invalid ELF header, or missing stringtab/sectiontab.");
      goto out;
   }

   /* Walk the LOAD headers in the phdr and update the SegInfo to
      include them all, so that this segment also contains data and
      bss memory.  Also computes correct symbol offset value for this
      ELF file. */
   if (ehdr->e_phoff + ehdr->e_phnum*sizeof(ElfXX_Phdr) > n_oimage) {
      ML_(symerr)("ELF program header is beyond image end?!");
      goto out;
   }
   {
      Bool offset_set = False;
      ElfXX_Addr prev_addr = 0;
      Addr baseaddr = 0;

      si->offset = 0;

      vg_assert(si->soname == NULL);

      for (i = 0; i < ehdr->e_phnum; i++) {
	 ElfXX_Phdr *o_phdr;
	 ElfXX_Addr mapped, mapped_end;

	 o_phdr = &((ElfXX_Phdr *)(oimage + ehdr->e_phoff))[i];

         /* Try to get the soname.  If there isn't one, use "NONE".
            The seginfo needs to have some kind of soname in order to
            facilitate writing redirect functions, since all redirect
            specifications require a soname (pattern). */
	 if (o_phdr->p_type == PT_DYNAMIC && si->soname == NULL) {
	    const ElfXX_Dyn *dyn = (const ElfXX_Dyn *)(oimage + o_phdr->p_offset);
	    Int stroff = -1;
	    Char *strtab = NULL;
	    Int j;
	    
	    for(j = 0; dyn[j].d_tag != DT_NULL; j++) {
	       switch(dyn[j].d_tag) {
	       case DT_SONAME:
		  stroff = dyn[j].d_un.d_val;
		  break;

	       case DT_STRTAB:
		  strtab = (Char *)oimage + dyn[j].d_un.d_ptr - baseaddr;
		  break;
	       }
	    }

	    if (stroff != -1 && strtab != 0) {
	       TRACE_SYMTAB("soname=%s\n", strtab+stroff);
	       si->soname = VG_(arena_strdup)(VG_AR_SYMTAB, strtab+stroff);
	    }
	 }

	 if (o_phdr->p_type != PT_LOAD)
	    continue;

	 if (!offset_set) {
	    offset_set = True;
	    si->offset = si->start - o_phdr->p_vaddr;
	    baseaddr = o_phdr->p_vaddr;
	 }

         // Make sure the Phdrs are in order
	 if (o_phdr->p_vaddr < prev_addr) {
	    ML_(symerr)("ELF Phdrs are out of order!?");
            goto out;
	 }
	 prev_addr = o_phdr->p_vaddr;

         // Get the data and bss start/size if appropriate
	 mapped = o_phdr->p_vaddr + si->offset;
	 mapped_end = mapped + o_phdr->p_memsz;
	 if (si->data_start_vma == 0 &&
	     (o_phdr->p_flags & (PF_R|PF_W|PF_X)) == (PF_R|PF_W)) {
	    si->data_start_vma = mapped;
	    si->data_size      = o_phdr->p_filesz;
	    si->bss_start_vma  = mapped + o_phdr->p_filesz;
	    if (o_phdr->p_memsz > o_phdr->p_filesz)
	       si->bss_size = o_phdr->p_memsz - o_phdr->p_filesz;
	    else
	       si->bss_size = 0;
	 }

         mapped = mapped & ~(VKI_PAGE_SIZE-1);
	 mapped_end = (mapped_end + VKI_PAGE_SIZE - 1) & ~(VKI_PAGE_SIZE-1);

	 if (VG_(needs).data_syms &&
	     (mapped >= si->start && mapped <= (si->start+si->size)) &&
	     (mapped_end > (si->start+si->size))) {
	    UInt newsz = mapped_end - si->start;
	    if (newsz > si->size) {
	       if (0)
		  VG_(printf)("extending mapping %p..%p %d -> ..%p %d\n", 
			      si->start, si->start+si->size, si->size,
			      si->start+newsz, newsz);

	       si->size = newsz;
	    }
	 }
      }
   }

   /* If, after looking at all the program headers, we still didn't 
      find a soname, add a fake one. */
   if (si->soname == NULL) {
      TRACE_SYMTAB("soname(fake)=\"NONE\"\n");
      si->soname = "NONE";
   }

   TRACE_SYMTAB("shoff = %d,  shnum = %d,  size = %d,  n_vg_oimage = %d\n",
                ehdr->e_shoff, ehdr->e_shnum, sizeof(ElfXX_Shdr), n_oimage );

   if (ehdr->e_shoff + ehdr->e_shnum*sizeof(ElfXX_Shdr) > n_oimage) {
      ML_(symerr)("ELF section header is beyond image end?!");
      goto out;
   }

   shdr = (ElfXX_Shdr*)(oimage + ehdr->e_shoff);
   sh_strtab = (UChar*)(oimage + shdr[ehdr->e_shstrndx].sh_offset);

   /* Find interesting sections, read the symbol table(s), read any debug
      information */
   {
      /* Pointers to start of sections (in the oimage, not in the
	 running image) */
      UChar*     o_strtab     = NULL; /* .strtab */
      ElfXX_Sym* o_symtab     = NULL; /* .symtab */
      UChar*     o_dynstr     = NULL; /* .dynstr */
      ElfXX_Sym* o_dynsym     = NULL; /* .dynsym */
      Char*      debuglink    = NULL; /* .gnu_debuglink */
      UChar*     stab         = NULL; /* .stab         (stabs)  */
      UChar*     stabstr      = NULL; /* .stabstr      (stabs)  */
      UChar*     debug_line   = NULL; /* .debug_line   (dwarf2) */
      UChar*     debug_info   = NULL; /* .debug_info   (dwarf2) */
      UChar*     debug_abbv   = NULL; /* .debug_abbrev (dwarf2) */
      UChar*     debug_str    = NULL; /* .debug_str    (dwarf2) */
      UChar*     dwarf1d      = NULL; /* .debug        (dwarf1) */
      UChar*     dwarf1l      = NULL; /* .line         (dwarf1) */
      UChar*     ehframe      = NULL; /* .eh_frame     (dwarf2) */
      UChar*     opd_filea    = NULL; /* .opd          (dwarf2, ppc64-linux) */
      UChar*     dummy_filea  = NULL;

      /* Section sizes, in bytes */
      UInt       o_strtab_sz     = 0;
      UInt       o_symtab_sz     = 0;
      UInt       o_dynstr_sz     = 0;
      UInt       o_dynsym_sz     = 0;
      UInt       debuglink_sz    = 0;
      UInt       stab_sz         = 0;
      UInt       stabstr_sz      = 0;
      UInt       debug_line_sz   = 0;
      UInt       debug_info_sz   = 0;
      UInt       debug_abbv_sz   = 0;
      UInt       debug_str_sz    = 0;
      UInt       dwarf1d_sz      = 0;
      UInt       dwarf1l_sz      = 0;
      UInt       ehframe_sz      = 0;

      /* Section virtual addresses */
      Addr       dummy_vma       = 0;
      Addr       ehframe_vma     = 0;

      /* Find all interesting sections */

      /* What FIND does: it finds the section called SEC_NAME.  The
	 size of it is assigned to SEC_SIZE.  The address that it will
	 appear in the running image is assigned to SEC_VMA (note,
	 this will be meaningless for sections which are not marked
	 loadable.  Even for sections which are marked loadable, the
	 client's ld.so may not have loaded them yet, so there is no
	 guarantee that we can safely prod around in any such area)
	 The address of the section in the transiently loaded oimage
	 is assigned to SEC_FILEA.  Because the entire object file is
	 transiently mapped aboard for inspection, it's always safe to
	 inspect that area. */

      for (i = 0; i < ehdr->e_shnum; i++) {

#        define FIND(sec_name, sec_size, sec_filea, sec_vma) \
         if (0 == VG_(strcmp)(sec_name, sh_strtab + shdr[i].sh_name)) { \
            Bool nobits; \
            sec_vma   = (Addr)(si->offset + shdr[i].sh_addr); \
            sec_filea = (void*)(oimage + shdr[i].sh_offset); \
            sec_size  = shdr[i].sh_size; \
            nobits = shdr[i].sh_type == SHT_NOBITS; \
            TRACE_SYMTAB( "%18s: filea %p .. %p, vma %p .. %p\n", \
                          sec_name, (UChar*)sec_filea, \
                                    ((UChar*)sec_filea) + sec_size - 1, \
                          sec_vma, sec_vma + sec_size - 1); \
            /* SHT_NOBITS sections have zero size in the file. */ \
            if ( shdr[i].sh_offset + (nobits ? 0 : sec_size) > n_oimage ) { \
               ML_(symerr)("   section beyond image end?!"); \
               goto out; \
            } \
         }

         /* Nb: must find where .got and .plt sections will be in the
          * executable image, not in the object image transiently loaded. */
         /*   NAME              SIZE           ADDR_IN_OIMAGE  ADDR_WHEN_MAPPED */
         FIND(".dynsym",        o_dynsym_sz,   o_dynsym,       dummy_vma)
         FIND(".dynstr",        o_dynstr_sz,   o_dynstr,       dummy_vma)
         FIND(".symtab",        o_symtab_sz,   o_symtab,       dummy_vma)
         FIND(".strtab",        o_strtab_sz,   o_strtab,       dummy_vma)

         FIND(".gnu_debuglink", debuglink_sz,  debuglink,      dummy_vma)

         FIND(".stab",          stab_sz,       stab,           dummy_vma)
         FIND(".stabstr",       stabstr_sz,    stabstr,        dummy_vma)

         FIND(".debug_line",    debug_line_sz, debug_line,     dummy_vma)
         FIND(".debug_info",    debug_info_sz, debug_info,     dummy_vma)
         FIND(".debug_abbrev",  debug_abbv_sz, debug_abbv,     dummy_vma)
         FIND(".debug_str",     debug_str_sz,  debug_str,      dummy_vma)

         FIND(".debug",         dwarf1d_sz,    dwarf1d,        dummy_vma)
         FIND(".line",          dwarf1l_sz,    dwarf1l,        dummy_vma)
         FIND(".eh_frame",      ehframe_sz,    ehframe,        ehframe_vma)

         FIND(".got",           si->got_size,  dummy_filea,    si->got_start_vma)
         FIND(".plt",           si->plt_size,  dummy_filea,    si->plt_start_vma)
         FIND(".opd",           si->opd_size,  opd_filea,      si->opd_start_vma)

#        undef FIND
      }
         
      /* Check some sizes */
      vg_assert((o_dynsym_sz % sizeof(ElfXX_Sym)) == 0);
      vg_assert((o_symtab_sz % sizeof(ElfXX_Sym)) == 0);

      /* Did we find a debuglink section? */
      if (debuglink != NULL) {
         UInt crc_offset = VG_ROUNDUP(VG_(strlen)(debuglink)+1, 4);
         UInt crc;

         vg_assert(crc_offset + sizeof(UInt) <= debuglink_sz);

         /* Extract the CRC from the debuglink section */
         crc = *(UInt *)(debuglink + crc_offset);

         /* See if we can find a matching debug file */
         if ((dimage = find_debug_file(si->filename, debuglink, crc, &n_dimage)) != 0) {
            ehdr = (ElfXX_Ehdr*)dimage;

            if (n_dimage >= sizeof(ElfXX_Ehdr) && is_elf_object_file(ehdr)) {
               shdr = (ElfXX_Shdr*)(dimage + ehdr->e_shoff);
               sh_strtab = (UChar*)(dimage + shdr[ehdr->e_shstrndx].sh_offset);

               /* Same deal as previous FIND, except simpler - doesn't
                  look for vma, only oimage address. */

               /* Find all interesting sections */
               for (i = 0; i < ehdr->e_shnum; i++) {

#                 define FIND(sec_name, sec_size, sec_filea)	\
                  if (0 == VG_(strcmp)(sec_name, sh_strtab + shdr[i].sh_name)) { \
                     Bool nobits; \
                     if (0 != sec_filea) \
                        VG_(core_panic)("repeated section!\n"); \
                     sec_filea = (void*)(dimage + shdr[i].sh_offset); \
                     sec_size  = shdr[i].sh_size; \
                     nobits = shdr[i].sh_type == SHT_NOBITS; \
                     TRACE_SYMTAB( "%18s: filea %p .. %p\n", \
                                   sec_name, (UChar*)sec_filea, \
                                             ((UChar*)sec_filea) + sec_size - 1); \
                     /* SHT_NOBITS sections have zero size in the file. */ \
                     if ( shdr[i].sh_offset + (nobits ? 0 : sec_size) > n_dimage ) { \
                        ML_(symerr)("   section beyond image end?!"); \
                        goto out; \
                     } \
                  }

                  FIND(".stab",         stab_sz,         stab)
                  FIND(".stabstr",      stabstr_sz,      stabstr)
                  FIND(".debug_line",   debug_line_sz,   debug_line)
                  FIND(".debug_info",   debug_info_sz,   debug_info)
                  FIND(".debug_abbrev", debug_abbv_sz,   debug_abbv)
                  FIND(".debug_str",    debug_str_sz,    debug_str)
                  FIND(".debug",        dwarf1d_sz,      dwarf1d)
                  FIND(".line",         dwarf1l_sz,      dwarf1l)

#                 undef FIND
               }
            }
         }
      }

      /* Read symbols */
      {
         void (*read_elf_symtab)(SegInfo*,Char*,ElfXX_Sym*,
                                 UInt,UChar*,UInt,UChar*);
#        if defined(VGP_ppc64_linux)
         read_elf_symtab = read_elf_symtab__ppc64_linux;
#        else
         read_elf_symtab = read_elf_symtab__normal;
#        endif
         read_elf_symtab(si, "symbol table",
                         o_symtab, o_symtab_sz,
                         o_strtab, o_strtab_sz, opd_filea);

         read_elf_symtab(si, "dynamic symbol table",
                         o_dynsym, o_dynsym_sz,
                         o_dynstr, o_dynstr_sz, opd_filea);
      }

      /* Read .eh_frame (call-frame-info) if any */
      if (ehframe) {
         ML_(read_callframe_info_dwarf2) ( si, ehframe, ehframe_sz, ehframe_vma );
      }

      /* Read the stabs and/or dwarf2 debug information, if any.  It
         appears reading stabs stuff on amd64-linux doesn't work, so
         we ignore it. */
#     if !defined(VGP_amd64_linux)
      if (stab && stabstr) {
         ML_(read_debuginfo_stabs) ( si, stab, stab_sz, 
                                         stabstr, stabstr_sz );
      }
#     endif
      /* jrs 2006-01-01: icc-8.1 has been observed to generate
         binaries without debug_str sections.  Don't preclude
         debuginfo reading for that reason, but, in
         read_unitinfo_dwarf2, do check that debugstr is non-NULL
         before using it. */
      if (debug_info && debug_abbv && debug_line /* && debug_str */) {
         ML_(read_debuginfo_dwarf2) ( si, 
                                      debug_info,   debug_info_sz,
                                      debug_abbv,
                                      debug_line,   debug_line_sz,
                                      debug_str );
      }
      if (dwarf1d && dwarf1l) {
         ML_(read_debuginfo_dwarf1) ( si, dwarf1d, dwarf1d_sz, 
                                          dwarf1l, dwarf1l_sz );
      }
   }
   res = True;

  out: {
   SysRes m_res;
   /* Last, but not least, heave the image(s) back overboard. */
   if (dimage) {
      m_res = VG_(am_munmap_valgrind) ( dimage, n_dimage );
      vg_assert(!m_res.isError);
   }
   m_res = VG_(am_munmap_valgrind) ( oimage, n_oimage );
   vg_assert(!m_res.isError);
   return res;
  } 
}

/*------------------------------------------------------------*/
/*--- Main entry point for symbols table reading.          ---*/
/*------------------------------------------------------------*/

static SegInfo*
alloc_SegInfo(Addr start, SizeT size, OffT foffset, const Char* filename)
{
   SegInfo* si = VG_(arena_calloc)(VG_AR_SYMTAB, 1, sizeof(SegInfo));

   si->start    = start;
   si->size     = size;
   si->foffset  = foffset;
   si->filename = VG_(arena_strdup)(VG_AR_SYMTAB, filename);

   si->ref = 1;

   // Everything else -- pointers, sizes, arrays -- is zeroed by calloc.

   return si;
}

static void freeSegInfo ( SegInfo* si )
{
   struct strchunk *chunk, *next;
   vg_assert(si != NULL);
   if (si->filename) VG_(arena_free)(VG_AR_SYMTAB, si->filename);
   if (si->symtab)   VG_(arena_free)(VG_AR_SYMTAB, si->symtab);
   if (si->loctab)   VG_(arena_free)(VG_AR_SYMTAB, si->loctab);
   if (si->scopetab) VG_(arena_free)(VG_AR_SYMTAB, si->scopetab);
   if (si->cfisi)    VG_(arena_free)(VG_AR_SYMTAB, si->cfisi);

   for(chunk = si->strchunks; chunk != NULL; chunk = next) {
      next = chunk->next;
      VG_(arena_free)(VG_AR_SYMTAB, chunk);
   }
   VG_(arena_free)(VG_AR_SYMTAB, si);
}


SegInfo *VG_(read_seg_symbols) ( Addr seg_addr, SizeT seg_len,
                                 OffT seg_offset, const Char* seg_filename)
{
   SegInfo* si = alloc_SegInfo(seg_addr, seg_len, seg_offset, seg_filename);

   if (!read_elf_debug_info ( si )) {
      // Something went wrong (eg. bad ELF file).
      freeSegInfo( si );
      si = NULL;

   } else {
      // Prepend si to segInfo_list
      si->next = segInfo_list;
      segInfo_list = si;

      canonicaliseSymtab   ( si );
      canonicaliseLoctab   ( si );
      canonicaliseScopetab ( si );
      canonicaliseCfiSI    ( si );

      /* notify m_redir about it */
      VG_(redir_notify_new_SegInfo)( si );
   }

   return si;
}


/* When an munmap() call happens, check to see whether it corresponds
   to a segment for a .so, and if so discard the relevant SegInfo.
   This might not be a very clever idea from the point of view of
   accuracy of error messages, but we need to do it in order to
   maintain the no-overlapping invariant.
*/
static void unload_symbols ( Addr start, SizeT length )
{
   SegInfo** prev_next_ptr = &segInfo_list;
   SegInfo*  curr          =  segInfo_list;

   while (curr) {
      if (start == curr->start) {
         // Found it;  remove from list and free it.
         if (VG_(clo_verbosity) > 1 || VG_(clo_trace_redir))
            VG_(message)(Vg_DebugMsg, 
                         "Discarding syms at %p-%p in %s due to munmap()", 
                         start, start+length,
                         curr->filename ? curr->filename : (Char *)"???");
         vg_assert(*prev_next_ptr == curr);
         *prev_next_ptr = curr->next;
         VG_(redir_notify_delete_SegInfo)( curr );
         freeSegInfo(curr);
         return;
      }
      prev_next_ptr = &curr->next;
      curr          =  curr->next;
   }

   // Not found.
}

/*------------------------------------------------------------*/
/*--- Use of symbol table & location info to create        ---*/
/*--- plausible-looking stack dumps.                       ---*/
/*------------------------------------------------------------*/

/* Find a symbol-table index containing the specified pointer, or -1
   if not found.  Binary search.  */

static Int search_one_symtab ( SegInfo* si, Addr ptr,
                               Bool match_anywhere_in_fun )
{
   Addr a_mid_lo, a_mid_hi;
   Int  mid, size, 
        lo = 0, 
        hi = si->symtab_used-1;
   while (True) {
      /* current unsearched space is from lo to hi, inclusive. */
      if (lo > hi) return -1; /* not found */
      mid      = (lo + hi) / 2;
      a_mid_lo = si->symtab[mid].addr;
      size = ( match_anywhere_in_fun
             ? si->symtab[mid].size
             : 1);
      a_mid_hi = ((Addr)si->symtab[mid].addr) + size - 1;

      if (ptr < a_mid_lo) { hi = mid-1; continue; } 
      if (ptr > a_mid_hi) { lo = mid+1; continue; }
      vg_assert(ptr >= a_mid_lo && ptr <= a_mid_hi);
      return mid;
   }
}


/* Search all symtabs that we know about to locate ptr.  If found, set
   *psi to the relevant SegInfo, and *symno to the symtab entry number
   within that.  If not found, *psi is set to NULL.  */
static void search_all_symtabs ( Addr ptr, /*OUT*/SegInfo** psi, 
                                           /*OUT*/Int* symno,
                                 Bool match_anywhere_in_fun )
{
   Int      sno;
   SegInfo* si;

   for (si = segInfo_list; si != NULL; si = si->next) {
      if (si->start <= ptr && ptr < si->start+si->size) {
         sno = search_one_symtab ( si, ptr, match_anywhere_in_fun );
         if (sno == -1) goto not_found;
         *symno = sno;
         *psi = si;
         return;
      }
   }
  not_found:
   *psi = NULL;
}


/* Find a location-table index containing the specified pointer, or -1
   if not found.  Binary search.  */

static Int search_one_loctab ( SegInfo* si, Addr ptr )
{
   Addr a_mid_lo, a_mid_hi;
   Int  mid, 
        lo = 0, 
        hi = si->loctab_used-1;
   while (True) {
      /* current unsearched space is from lo to hi, inclusive. */
      if (lo > hi) return -1; /* not found */
      mid      = (lo + hi) / 2;
      a_mid_lo = si->loctab[mid].addr;
      a_mid_hi = ((Addr)si->loctab[mid].addr) + si->loctab[mid].size - 1;

      if (ptr < a_mid_lo) { hi = mid-1; continue; } 
      if (ptr > a_mid_hi) { lo = mid+1; continue; }
      vg_assert(ptr >= a_mid_lo && ptr <= a_mid_hi);
      return mid;
   }
}


/* Search all loctabs that we know about to locate ptr.  If found, set
   *psi to the relevant SegInfo, and *locno to the loctab entry number
   within that.  If not found, *psi is set to NULL.
*/
static void search_all_loctabs ( Addr ptr, /*OUT*/SegInfo** psi,
                                           /*OUT*/Int* locno )
{
   Int      lno;
   SegInfo* si;

   for (si = segInfo_list; si != NULL; si = si->next) {
      if (si->start <= ptr && ptr < si->start+si->size) {
         lno = search_one_loctab ( si, ptr );
         if (lno == -1) goto not_found;
         *locno = lno;
         *psi = si;
         return;
      }
   }
  not_found:
   *psi = NULL;
}


/* Find a scope-table index containing the specified pointer, or -1
   if not found.  Binary search.  */

static Int search_one_scopetab ( SegInfo* si, Addr ptr )
{
   Addr a_mid_lo, a_mid_hi;
   Int  mid, 
        lo = 0, 
        hi = si->scopetab_used-1;
   while (True) {
      /* current unsearched space is from lo to hi, inclusive. */
      if (lo > hi) return -1; /* not found */
      mid      = (lo + hi) / 2;
      a_mid_lo = si->scopetab[mid].addr;
      a_mid_hi = ((Addr)si->scopetab[mid].addr) + si->scopetab[mid].size - 1;

      if (ptr < a_mid_lo) { hi = mid-1; continue; } 
      if (ptr > a_mid_hi) { lo = mid+1; continue; }
      vg_assert(ptr >= a_mid_lo && ptr <= a_mid_hi);
      return mid;
   }
}


/* Search all scopetabs that we know about to locate ptr.  If found, set
   *psi to the relevant SegInfo, and *locno to the scopetab entry number
   within that.  If not found, *psi is set to NULL.
*/
static void search_all_scopetabs ( Addr ptr,
				   /*OUT*/SegInfo** psi,
				   /*OUT*/Int* scopeno )
{
   Int      scno;
   SegInfo* si;

   for (si = segInfo_list; si != NULL; si = si->next) {
      if (si->start <= ptr && ptr < si->start+si->size) {
         scno = search_one_scopetab ( si, ptr );
         if (scno == -1) goto not_found;
         *scopeno = scno;
         *psi = si;
         return;
      }
   }
  not_found:
   *psi = NULL;
}


/* Find a CFI-table index containing the specified pointer, or -1
   if not found.  Binary search.  */

static Int search_one_cfitab ( SegInfo* si, Addr ptr )
{
   Addr a_mid_lo, a_mid_hi;
   Int  mid, size, 
        lo = 0, 
        hi = si->cfisi_used-1;
   while (True) {
      /* current unsearched space is from lo to hi, inclusive. */
      if (lo > hi) return -1; /* not found */
      mid      = (lo + hi) / 2;
      a_mid_lo = si->cfisi[mid].base;
      size     = si->cfisi[mid].len;
      a_mid_hi = a_mid_lo + size - 1;
      vg_assert(a_mid_hi >= a_mid_lo);
      if (ptr < a_mid_lo) { hi = mid-1; continue; } 
      if (ptr > a_mid_hi) { lo = mid+1; continue; }
      vg_assert(ptr >= a_mid_lo && ptr <= a_mid_hi);
      return mid;
   }
}


/* The whole point of this whole big deal: map a code address to a
   plausible symbol name.  Returns False if no idea; otherwise True.
   Caller supplies buf and nbuf.  If demangle is False, don't do
   demangling, regardless of VG_(clo_demangle) -- probably because the
   call has come from VG_(get_fnname_nodemangle)(). */
static
Bool get_fnname ( Bool demangle, Addr a, Char* buf, Int nbuf,
                  Bool match_anywhere_in_fun, Bool show_offset)
{
   SegInfo* si;
   Int      sno;
   Int      offset;

   search_all_symtabs ( a, &si, &sno, match_anywhere_in_fun );
   if (si == NULL) 
      return False;
   if (demangle) {
      VG_(demangle) ( True/*do C++ demangle*/,
                      si->symtab[sno].name, buf, nbuf );
   } else {
      VG_(strncpy_safely) ( buf, si->symtab[sno].name, nbuf );
   }

   offset = a - si->symtab[sno].addr;
   if (show_offset && offset != 0) {
      Char     buf2[12];
      Char*    symend = buf + VG_(strlen)(buf);
      Char*    end = buf + nbuf;
      Int      len;

      len = VG_(sprintf)(buf2, "%c%d",
			 offset < 0 ? '-' : '+',
			 offset < 0 ? -offset : offset);
      vg_assert(len < (Int)sizeof(buf2));

      if (len < (end - symend)) {
	 Char *cp = buf2;
	 VG_(memcpy)(symend, cp, len+1);
      }
   }

   return True;
}

/* ppc64-linux only: find the TOC pointer (R2 value) that should be in
   force at the entry point address of the function containing
   guest_code_addr.  Returns 0 if not known. */
Addr VG_(get_tocptr) ( Addr guest_code_addr )
{
   SegInfo* si;
   Int      sno;
   search_all_symtabs ( guest_code_addr, 
                        &si, &sno, True/*match_anywhere_in_fun*/ );
   if (si == NULL) 
      return 0;
   else
      return si->symtab[sno].tocptr;
}

/* This is available to tools... always demangle C++ names,
   match anywhere in function, but don't show offsets. */
Bool VG_(get_fnname) ( Addr a, Char* buf, Int nbuf )
{
   return get_fnname ( /*demangle*/True, a, buf, nbuf,
                       /*match_anywhere_in_fun*/True, 
                       /*show offset?*/False );
}

/* This is available to tools... always demangle C++ names,
   match anywhere in function, and show offset if nonzero. */
Bool VG_(get_fnname_w_offset) ( Addr a, Char* buf, Int nbuf )
{
   return get_fnname ( /*demangle*/True, a, buf, nbuf,
                       /*match_anywhere_in_fun*/True, 
                       /*show offset?*/True );
}

/* This is available to tools... always demangle C++ names,
   only succeed if 'a' matches first instruction of function,
   and don't show offsets. */
Bool VG_(get_fnname_if_entry) ( Addr a, Char* buf, Int nbuf )
{
   return get_fnname ( /*demangle*/True, a, buf, nbuf,
                       /*match_anywhere_in_fun*/False, 
                       /*show offset?*/False );
}

/* This is only available to core... don't demangle C++ names,
   match anywhere in function, and don't show offsets. */
Bool VG_(get_fnname_nodemangle) ( Addr a, Char* buf, Int nbuf )
{
   return get_fnname ( /*demangle*/False, a, buf, nbuf,
                       /*match_anywhere_in_fun*/True, 
                       /*show offset?*/False );
}

/* This is only available to core... don't demangle C++ names, but do
   do Z-demangling, match anywhere in function, and don't show
   offsets. */
Bool VG_(get_fnname_Z_demangle_only) ( Addr a, Char* buf, Int nbuf )
{
#  define N_TMPBUF 4096 /* arbitrary, 4096 == ERRTXT_LEN */
   Char tmpbuf[N_TMPBUF];
   Bool ok;
   vg_assert(nbuf > 0);
   ok = get_fnname ( /*demangle*/False, a, tmpbuf, N_TMPBUF,
                     /*match_anywhere_in_fun*/True, 
                     /*show offset?*/False );
   tmpbuf[N_TMPBUF-1] = 0; /* paranoia */
   if (!ok) 
      return False;

   /* We have something, at least.  Try to Z-demangle it. */
   VG_(demangle)( False/*don't do C++ demangling*/, tmpbuf, buf, nbuf);

   buf[nbuf-1] = 0; /* paranoia */
   return True;
#  undef N_TMPBUF
}

/* Map a code address to the name of a shared object file or the executable.
   Returns False if no idea; otherwise True.  Doesn't require debug info.
   Caller supplies buf and nbuf. */
Bool VG_(get_objname) ( Addr a, Char* buf, Int nbuf )
{
   SegInfo* si;

   for (si = segInfo_list; si != NULL; si = si->next) {
      if (si->start <= a && a < si->start+si->size) {
         VG_(strncpy_safely)(buf, si->filename, nbuf);
         return True;
      }
   }
   return False;
}

/* Map a code address to its SegInfo.  Returns NULL if not found.  Doesn't
   require debug info. */
SegInfo* VG_(find_seginfo) ( Addr a )
{
   SegInfo* si;

   for (si = segInfo_list; si != NULL; si = si->next) {
      if (si->start <= a && a < si->start+si->size) {
         return si;
      }
   }
   return NULL;
}


/* Map a code address to a filename.  Returns True if successful.  */
Bool VG_(get_filename)( Addr a, Char* filename, Int n_filename )
{
   SegInfo* si;
   Int      locno;
   search_all_loctabs ( a, &si, &locno );
   if (si == NULL) 
      return False;
   VG_(strncpy_safely)(filename, si->loctab[locno].filename, n_filename);
   return True;
}

/* Map a code address to a line number.  Returns True if successful. */
Bool VG_(get_linenum)( Addr a, UInt* lineno )
{
   SegInfo* si;
   Int      locno;
   search_all_loctabs ( a, &si, &locno );
   if (si == NULL) 
      return False;
   *lineno = si->loctab[locno].lineno;

   return True;
}

/* Map a code address to a filename/line number/dir name info.
   See prototype for detailed description of behaviour.
*/
Bool VG_(get_filename_linenum) ( Addr a, 
                                 /*OUT*/Char* filename, Int n_filename,
                                 /*OUT*/Char* dirname,  Int n_dirname,
                                 /*OUT*/Bool* dirname_available,
                                 /*OUT*/UInt* lineno )
{
   SegInfo* si;
   Int      locno;

   vg_assert( (dirname == NULL && dirname_available == NULL)
              ||
              (dirname != NULL && dirname_available != NULL) );

   search_all_loctabs ( a, &si, &locno );
   if (si == NULL) 
      return False;
   VG_(strncpy_safely)(filename, si->loctab[locno].filename, n_filename);
   *lineno = si->loctab[locno].lineno;

   if (dirname) {
      /* caller wants directory info too .. */
      vg_assert(n_dirname > 0);
      if (si->loctab[locno].dirname) {
         /* .. and we have some */
         *dirname_available = True;
         VG_(strncpy_safely)(dirname, si->loctab[locno].dirname,
                                      n_dirname);
      } else {
         /* .. but we don't have any */
         *dirname_available = False;
         *dirname = 0;
      }
   }

   return True;
}

#ifndef TEST

// Note that R_STACK_PTR and R_FRAME_PTR are used again further below,
// which is why they get a named constant.
static Addr regaddr_from_tst(Int regno, ThreadArchState *arch)
{
#if defined(VGA_x86)
   /* This is the Intel register encoding -- integer regs. */
#  define R_STACK_PTR   4
#  define R_FRAME_PTR   5
   switch (regno) {
   case 0:           return (Addr) & arch->vex.guest_EAX;
   case 1:           return (Addr) & arch->vex.guest_ECX;
   case 2:           return (Addr) & arch->vex.guest_EDX;
   case 3:           return (Addr) & arch->vex.guest_EBX;
   case R_STACK_PTR: return (Addr) & arch->vex.guest_ESP;
   case R_FRAME_PTR: return (Addr) & arch->vex.guest_EBP;
   case 6:           return (Addr) & arch->vex.guest_ESI;
   case 7:           return (Addr) & arch->vex.guest_EDI;
   default:          return 0;
   }
#elif defined(VGA_amd64)
   /* This is the AMD64 register encoding -- integer regs. */
#  define R_STACK_PTR   7
#  define R_FRAME_PTR   6
   switch (regno) {
   case 0:           return (Addr) & arch->vex.guest_RAX;
   case 1:           return (Addr) & arch->vex.guest_RDX;
   case 2:           return (Addr) & arch->vex.guest_RCX;
   case 3:           return (Addr) & arch->vex.guest_RBX;
   case 4:           return (Addr) & arch->vex.guest_RSI;
   case 5:           return (Addr) & arch->vex.guest_RDI;
   case R_FRAME_PTR: return (Addr) & arch->vex.guest_RBP;
   case R_STACK_PTR: return (Addr) & arch->vex.guest_RSP;
   case 8:           return (Addr) & arch->vex.guest_R8;
   case 9:           return (Addr) & arch->vex.guest_R9;
   case 10:          return (Addr) & arch->vex.guest_R10;
   case 11:          return (Addr) & arch->vex.guest_R11;
   case 12:          return (Addr) & arch->vex.guest_R12;
   case 13:          return (Addr) & arch->vex.guest_R13;
   case 14:          return (Addr) & arch->vex.guest_R14;
   case 15:          return (Addr) & arch->vex.guest_R15;
   default:          return 0;
   }
#elif defined(VGA_ppc32) || defined(VGA_ppc64)
   /* This is the PPC register encoding -- integer regs. */
#  define R_STACK_PTR   1
#  define R_FRAME_PTR   1
   switch (regno) {
   case 0:           return (Addr) & arch->vex.guest_GPR0;
   case R_STACK_PTR: return (Addr) & arch->vex.guest_GPR1;
   case 2:           return (Addr) & arch->vex.guest_GPR2;
   case 3:           return (Addr) & arch->vex.guest_GPR3;
   case 4:           return (Addr) & arch->vex.guest_GPR4;
   case 5:           return (Addr) & arch->vex.guest_GPR5;
   case 6:           return (Addr) & arch->vex.guest_GPR6;
   case 7:           return (Addr) & arch->vex.guest_GPR7;
   case 8:           return (Addr) & arch->vex.guest_GPR8;
   case 9:           return (Addr) & arch->vex.guest_GPR9;
   case 10:          return (Addr) & arch->vex.guest_GPR10;
   case 11:          return (Addr) & arch->vex.guest_GPR11;
   case 12:          return (Addr) & arch->vex.guest_GPR12;
   case 13:          return (Addr) & arch->vex.guest_GPR13;
   case 14:          return (Addr) & arch->vex.guest_GPR14;
   case 15:          return (Addr) & arch->vex.guest_GPR15;
   case 16:          return (Addr) & arch->vex.guest_GPR16;
   case 17:          return (Addr) & arch->vex.guest_GPR17;
   case 18:          return (Addr) & arch->vex.guest_GPR18;
   case 19:          return (Addr) & arch->vex.guest_GPR19;
   case 20:          return (Addr) & arch->vex.guest_GPR20;
   case 21:          return (Addr) & arch->vex.guest_GPR21;
   case 22:          return (Addr) & arch->vex.guest_GPR22;
   case 23:          return (Addr) & arch->vex.guest_GPR23;
   case 24:          return (Addr) & arch->vex.guest_GPR24;
   case 25:          return (Addr) & arch->vex.guest_GPR25;
   case 26:          return (Addr) & arch->vex.guest_GPR26;
   case 27:          return (Addr) & arch->vex.guest_GPR27;
   case 28:          return (Addr) & arch->vex.guest_GPR28;
   case 29:          return (Addr) & arch->vex.guest_GPR29;
   case 30:          return (Addr) & arch->vex.guest_GPR30;
   case 31:          return (Addr) & arch->vex.guest_GPR31;
   default:          return 0;
   }
#else
#  error Unknown platform
#endif
}


/* return a pointer to a register (now for 5 other impossible things
   before breakfast) */
static Addr regaddr(ThreadId tid, Int regno)
{
   Addr ret = regaddr_from_tst(regno, &VG_(threads)[tid].arch);

   if (ret == 0) {
      Char buf[100];
      VG_(describe_IP)( VG_(get_IP)(tid), buf, 100 );
      VG_(printf)("mysterious register %d used at %s\n", regno, buf);
   }

   return ret;
}

/* Get a list of all variables in scope, working out from the directly
   current one */
Variable* ML_(get_scope_variables)(ThreadId tid)
{
   static const Bool debug = False;
   Variable *list, *end;
   Addr eip;
   SegInfo *si;
   Int scopeidx;
   Scope *scope;
   Int distance;
   static const Int maxsyms = 1000;
   Int nsyms = maxsyms;

   list = end = NULL;

   eip = VG_(get_IP)(tid);
   
   search_all_scopetabs(eip, &si, &scopeidx);

   if (debug)
      VG_(printf)("eip=%p si=%p (%s; offset=%p) scopeidx=%d\n", 
		  eip, si, si ? si->filename : (Char *)"???",
		  si ? si->offset : 0x99999, scopeidx);

   if (si == NULL)
      return NULL;		/* nothing in scope (should use global scope at least) */

   if (debug) {
      ScopeRange *sr = &si->scopetab[scopeidx];
      Char file[100];
      Int line;

      if (!VG_(get_filename_linenum)(sr->addr, file, sizeof(file), 
                                                     NULL, 0, NULL, &line))
	 file[0] = 0;

      VG_(printf)("found scope range %p: eip=%p (%s:%d) size=%d scope=%p\n",
		  sr, sr->addr, file, line, sr->size, sr->scope);
   }

   distance = 0;
   for (scope = si->scopetab[scopeidx].scope; 
        scope != NULL; 
        scope = scope->outer, distance++) {
      UInt i;

      for(i = 0; i < scope->nsyms; i++) {
	 Sym *sym = &scope->syms[i];
	 Variable *v;

	 if (nsyms-- == 0) {
	    VG_(printf)("max %d syms reached\n", maxsyms);
	    return list;
	 }
	    
	 v = VG_(arena_malloc)(VG_AR_SYMTAB, sizeof(*v));

	 v->next = NULL;
	 v->distance = distance;
	 v->type = ML_(st_basetype)(sym->type, False);
	 v->name = VG_(arena_strdup)(VG_AR_SYMTAB, sym->name);
	 v->container = NULL;
	 v->size = ML_(st_sizeof)(sym->type);

	 if (debug && 0)
	    VG_(printf)("sym->name=%s sym->kind=%d offset=%d\n", sym->name, sym->kind, sym->u.offset);
	 switch(sym->kind) {

	 case SyGlobal:
	 case SyStatic:
	    if (sym->u.addr == 0) {
	       /* XXX lookup value */
	    }
	    v->valuep = sym->u.addr;
	    break;

	 case SyReg:
	    v->valuep = regaddr(tid, sym->u.regno);
	    break;

	 case SyEBPrel:
	 case SyESPrel: {
	    Addr reg = *(Addr*)regaddr(tid, sym->kind == SyESPrel
                                            ? R_STACK_PTR : R_FRAME_PTR);
	    if (debug)
	       VG_(printf)("reg=%p+%d=%p\n", reg, sym->u.offset, reg+sym->u.offset);
	    v->valuep = reg + sym->u.offset;
	    break;
         }

	 case SyType:
	    VG_(core_panic)("unexpected typedef in scope");
	 }

	 if (v->valuep == 0) {
	    /* not interesting or useful */
	    VG_(arena_free)(VG_AR_SYMTAB, v);
	    continue;
	 }

	 /* append to end of list */
	 if (list == NULL)
	    list = end = v;
	 else {
	    end->next = v;
	    end = v;
	 }
      }  
   }

   return list;
}

#  undef R_STACK_PTR
#  undef R_FRAME_PTR

#endif /* TEST */

/* Print into buf info on code address, function name and filename */

static Int putStr ( Int n, Int n_buf, Char* buf, Char* str ) 
{
   for (; n < n_buf-1 && *str != 0; n++,str++)
      buf[n] = *str;
   buf[n] = '\0';
   return n;
}
static Int putStrEsc ( Int n, Int n_buf, Char* buf, Char* str ) 
{
   Char alt[2];
   for (; *str != 0; str++) {
      switch (*str) {
         case '&': n = putStr( n, n_buf, buf, "&amp;"); break;
         case '<': n = putStr( n, n_buf, buf, "&lt;"); break;
         case '>': n = putStr( n, n_buf, buf, "&gt;"); break;
         default:  alt[0] = *str;
                   alt[1] = 0;
                   n = putStr( n, n_buf, buf, alt );
                   break;
      }
   }
   return n;
}

Char* VG_(describe_IP)(Addr eip, Char* buf, Int n_buf)
{
#  define APPEND(_str) \
      n = putStr(n, n_buf, buf, _str);
#  define APPEND_ESC(_str) \
      n = putStrEsc(n, n_buf, buf, _str);
#  define BUF_LEN    4096

   UInt  lineno; 
   UChar ibuf[50];
   Int   n = 0;
   static UChar buf_fn[BUF_LEN];
   static UChar buf_obj[BUF_LEN];
   static UChar buf_srcloc[BUF_LEN];
   static UChar buf_dirname[BUF_LEN];
   Bool  know_dirinfo = False;
   Bool  know_fnname  = VG_(get_fnname) (eip, buf_fn,  BUF_LEN);
   Bool  know_objname = VG_(get_objname)(eip, buf_obj, BUF_LEN);
   Bool  know_srcloc  = VG_(get_filename_linenum)(
                           eip, 
                           buf_srcloc,  BUF_LEN, 
                           buf_dirname, BUF_LEN, &know_dirinfo,
                           &lineno 
                        );
   if (VG_(clo_xml)) {

      Bool   human_readable = True;
      HChar* maybe_newline  = human_readable ? "\n      " : "";
      HChar* maybe_newline2 = human_readable ? "\n    "   : "";

      /* Print in XML format, dumping in as much info as we know. */
      APPEND("<frame>");
      VG_(sprintf)(ibuf,"<ip>0x%llx</ip>", (ULong)eip);
      APPEND(maybe_newline);
      APPEND(ibuf);
      if (know_objname) {
         APPEND(maybe_newline);
         APPEND("<obj>");
         APPEND_ESC(buf_obj);
         APPEND("</obj>");
      }
      if (know_fnname) {
         APPEND(maybe_newline);
         APPEND("<fn>");
         APPEND_ESC(buf_fn);
         APPEND("</fn>");
      }
      if (know_srcloc) {
         if (know_dirinfo) {
            APPEND(maybe_newline);
            APPEND("<dir>");
            APPEND(buf_dirname);
            APPEND("</dir>");
         }
         APPEND(maybe_newline);
         APPEND("<file>");
         APPEND_ESC(buf_srcloc);
         APPEND("</file>");
         APPEND(maybe_newline);
         APPEND("<line>");
         VG_(sprintf)(ibuf,"%d",lineno);
         APPEND(ibuf);
         APPEND("</line>");
      }
      APPEND(maybe_newline2);
      APPEND("</frame>");

   } else {

      /* Print for humans to read */
      VG_(sprintf)(ibuf,"0x%llx: ", (ULong)eip);
      APPEND(ibuf);
      if (know_fnname) { 
         APPEND(buf_fn);
         if (!know_srcloc && know_objname) {
            APPEND(" (in ");
            APPEND(buf_obj);
            APPEND(")");
         }
      } else if (know_objname && !know_srcloc) {
         APPEND("(within ");
         APPEND(buf_obj);
         APPEND(")");
      } else {
         APPEND("???");
      }
      if (know_srcloc) {
         APPEND(" (");
         APPEND(buf_srcloc);
         APPEND(":");
         VG_(sprintf)(ibuf,"%d",lineno);
         APPEND(ibuf);
         APPEND(")");
      }

   }
   return buf;

#  undef APPEND
#  undef APPEND_ESC
#  undef BUF_LEN
}

/* Returns True if OK.  If not OK, *{ip,sp,fp}P are not changed. */
/* NOTE: this function may rearrange the order of entries in the
   SegInfo list. */
Bool VG_(use_CFI_info) ( /*MOD*/Addr* ipP,
                         /*MOD*/Addr* spP,
                         /*MOD*/Addr* fpP,
                         Addr min_accessible,
                         Addr max_accessible )
{
   Int      i;
   SegInfo* si;
   CfiSI*   cfisi = NULL;
   Addr     cfa, ipHere, spHere, fpHere, ipPrev, spPrev, fpPrev;

   static UInt n_search = 0;
   static UInt n_steps = 0;
   n_search++;

   if (0) VG_(printf)("search for %p\n", *ipP);

   for (si = segInfo_list; si != NULL; si = si->next) {
      n_steps++;

      /* Use the per-SegInfo summary address ranges to skip
	 inapplicable SegInfos quickly. */
      if (si->cfisi_used == 0)
         continue;
      if (*ipP < si->cfisi_minaddr || *ipP > si->cfisi_maxaddr)
         continue;

      i = search_one_cfitab( si, *ipP );
      if (i != -1) {
         vg_assert(i >= 0 && i < si->cfisi_used);
         cfisi = &si->cfisi[i];
         break;
      }
   }

   if (cfisi == NULL)
      return False;

   if (0 && ((n_search & 0xFFFFF) == 0))
      VG_(printf)("%u %u\n", n_search, n_steps);

   /* Start of performance-enhancing hack: once every 16 (chosen
      hackily after profiling) successful searchs, move the found
      SegInfo one step closer to the start of the list.  This makes
      future searches cheaper.  For starting konqueror on amd64, this
      in fact reduces the total amount of searching done by the above
      find-the-right-SegInfo loop by more than a factor of 20. */
   if ((n_search & 0xF) == 0) {
      /* Move si one step closer to the start of the list. */
      SegInfo* si0 = segInfo_list;
      SegInfo* si1 = NULL;
      SegInfo* si2 = NULL;
      SegInfo* tmp;
      while (True) {
         if (si0 == NULL) break;
         if (si0 == si) break;
         si2 = si1;
         si1 = si0;
         si0 = si0->next;
      }
      if (si0 == si && si0 != NULL && si1 != NULL && si2 != NULL) {
         /* si0 points to si, si1 to its predecessor, and si2 to si1's
            predecessor.  Swap si0 and si1, that is, move si0 one step
            closer to the start of the list. */
         tmp = si0->next;
         si2->next = si0;
         si0->next = si1;
         si1->next = tmp;
      }
   }
   /* End of performance-enhancing hack. */

   if (0) {
      VG_(printf)("found cfisi: "); 
      ML_(ppCfiSI)(cfisi);
   }

   ipPrev = spPrev = fpPrev = 0;

   ipHere = *ipP;
   spHere = *spP;
   fpHere = *fpP;

   cfa = cfisi->cfa_off + (cfisi->cfa_sprel ? spHere : fpHere);

#  define COMPUTE(_prev, _here, _how, _off)             \
      do {                                              \
         switch (_how) {                                \
            case CFIR_UNKNOWN:                          \
               return False;                            \
            case CFIR_SAME:                             \
               _prev = _here; break;                    \
            case CFIR_MEMCFAREL: {                      \
               Addr a = cfa + (Word)_off;               \
               if (a < min_accessible                   \
                   || a+sizeof(Addr) > max_accessible)  \
                  return False;                         \
               _prev = *(Addr*)a;                       \
               break;                                   \
            }                                           \
            case CFIR_CFAREL:                           \
               _prev = cfa + (Word)_off;                \
               break;                                   \
         }                                              \
      } while (0)

   COMPUTE(ipPrev, ipHere, cfisi->ra_how, cfisi->ra_off);
   COMPUTE(spPrev, spHere, cfisi->sp_how, cfisi->sp_off);
   COMPUTE(fpPrev, fpHere, cfisi->fp_how, cfisi->fp_off);

#  undef COMPUTE

   *ipP = ipPrev;
   *spP = spPrev;
   *fpP = fpPrev;
   return True;
}


/*------------------------------------------------------------*/
/*--- SegInfo accessor functions                           ---*/
/*------------------------------------------------------------*/

const SegInfo* VG_(next_seginfo)(const SegInfo* si)
{
   if (si == NULL)
      return segInfo_list;
   return si->next;
}

Addr VG_(seginfo_start)(const SegInfo* si)
{
   return si->start;
}

SizeT VG_(seginfo_size)(const SegInfo* si)
{
   return si->size;
}

const UChar* VG_(seginfo_soname)(const SegInfo* si)
{
   return si->soname;
}

const UChar* VG_(seginfo_filename)(const SegInfo* si)
{
   return si->filename;
}

ULong VG_(seginfo_sym_offset)(const SegInfo* si)
{
   return si->offset;
}

VgSectKind VG_(seginfo_sect_kind)(Addr a)
{
   SegInfo* si;
   VgSectKind ret = Vg_SectUnknown;

   for(si = segInfo_list; si != NULL; si = si->next) {
      if (a >= si->start && a < (si->start + si->size)) {

	 if (0)
	    VG_(printf)(
               "addr=%p si=%p %s got=%p %d  plt=%p %d data=%p %d bss=%p %d\n",
               a, si, si->filename, 
               si->got_start_vma,  si->got_size,
               si->plt_start_vma,  si->plt_size,
               si->data_start_vma, si->data_size,
               si->bss_start_vma,  si->bss_size);

	 ret = Vg_SectText;

	 if (a >= si->data_start_vma && a < (si->data_start_vma + si->data_size))
	    ret = Vg_SectData;
	 else 
         if (a >= si->bss_start_vma && a < (si->bss_start_vma + si->bss_size))
	    ret = Vg_SectBSS;
	 else 
         if (a >= si->plt_start_vma && a < (si->plt_start_vma + si->plt_size))
	    ret = Vg_SectPLT;
	 else 
         if (a >= si->got_start_vma && a < (si->got_start_vma + si->got_size))
	    ret = Vg_SectGOT;
      }
   }

   return ret;
}

Int VG_(seginfo_syms_howmany) ( const SegInfo *si )
{
   return si->symtab_used;
}

void VG_(seginfo_syms_getidx) ( const SegInfo *si, 
                                      Int idx,
                               /*OUT*/Addr*   addr,
                               /*OUT*/UInt*   size,
                               /*OUT*/HChar** name )
{
   vg_assert(idx >= 0 && idx < si->symtab_used);
   if (addr) *addr = si->symtab[idx].addr;
   if (size) *size = si->symtab[idx].size;
   if (name) *name = (HChar*)si->symtab[idx].name;
}


/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
