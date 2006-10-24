
/*--------------------------------------------------------------------*/
/*--- Top level management of symbols and debugging information.   ---*/
/*---                                                  debuginfo.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2006 Julian Seward 
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
   This module was also extensively hacked on by Jeremy Fitzhardinge
   and Tom Hughes.
*/

#include "pub_core_basics.h"
#include "pub_core_vki.h"
#include "pub_core_threadstate.h"
#include "pub_core_debuginfo.h"   /* self */
#include "pub_core_demangle.h"
#include "pub_core_libcbase.h"
#include "pub_core_libcassert.h"
#include "pub_core_libcprint.h"
#include "pub_core_mallocfree.h"
#include "pub_core_options.h"
#include "pub_core_redir.h"       // VG_(redir_notify_{new,delete}_SegInfo)
#include "pub_core_aspacemgr.h"
#include "pub_core_machine.h"     // VG_PLAT_USES_PPCTOC
#include "priv_storage.h"
#include "priv_readdwarf.h"
#include "priv_readstabs.h"
#if defined(VGO_linux)
# include "priv_readelf.h"
#elif defined(VGO_aix5)
# include "pub_core_debuglog.h"
# include "pub_core_libcproc.h"
# include "pub_core_libcfile.h"
# include "priv_readxcoff.h"
#endif

/*------------------------------------------------------------*/
/*--- Root structure                                       ---*/
/*------------------------------------------------------------*/

/* The root structure for the entire symbol table system.  It is a
   linked list of SegInfos.  Note that this entire mechanism assumes
   that what we read from /proc/self/maps doesn't contain overlapping
   address ranges, and as a result the SegInfos in this list describe
   disjoint address ranges.
*/
static SegInfo* segInfo_list = NULL;


/*------------------------------------------------------------*/
/*--- Notification (acquire/discard) helpers               ---*/
/*------------------------------------------------------------*/

/* Allocate and zero out a new SegInfo record. */
static 
SegInfo* alloc_SegInfo(Addr start, SizeT size, OffT foffset, 
                       const UChar* filename,
                       const UChar* memname)
{
   SegInfo* si = VG_(arena_calloc)(VG_AR_SYMTAB, 1, sizeof(SegInfo));

   si->start    = start;
   si->size     = size;
   si->foffset  = foffset;
   si->filename = VG_(arena_strdup)(VG_AR_SYMTAB, filename);
   si->memname  = memname ?  VG_(arena_strdup)(VG_AR_SYMTAB, memname)
                          :  NULL;

   // Everything else -- pointers, sizes, arrays -- is zeroed by calloc.
   return si;
}


/* Free a SegInfo, and also all the stuff hanging off it. */
static void free_SegInfo ( SegInfo* si )
{
   struct strchunk *chunk, *next;
   vg_assert(si != NULL);
   if (si->filename) VG_(arena_free)(VG_AR_SYMTAB, si->filename);
   if (si->symtab)   VG_(arena_free)(VG_AR_SYMTAB, si->symtab);
   if (si->loctab)   VG_(arena_free)(VG_AR_SYMTAB, si->loctab);
   if (si->cfsi)     VG_(arena_free)(VG_AR_SYMTAB, si->cfsi);

   for (chunk = si->strchunks; chunk != NULL; chunk = next) {
      next = chunk->next;
      VG_(arena_free)(VG_AR_SYMTAB, chunk);
   }
   VG_(arena_free)(VG_AR_SYMTAB, si);
}


/* 'si' is a member of segInfo_list.  Find it, remove it from the
   list, notify m_redir that this has happened, and free all storage
   reachable from it.
*/
static void discard_SegInfo ( SegInfo* si )
{
#  if defined(VGP_ppc32_aix5)
   HChar* reason = "__unload";
#  elif defined(VGP_ppc64_aix5)
   HChar* reason = "kunload64";
#  else
   HChar* reason = "munmap";
#  endif

   SegInfo** prev_next_ptr = &segInfo_list;
   SegInfo*  curr          =  segInfo_list;

   while (curr) {
      if (curr == si) {
         // Found it;  remove from list and free it.
         if (VG_(clo_verbosity) > 1 || VG_(clo_trace_redir))
            VG_(message)(Vg_DebugMsg, 
                         "Discarding syms at %p-%p in %s due to %s()", 
                         si->start, si->start + si->size,
                         curr->filename ? curr->filename : (UChar*)"???",
                         reason);
         vg_assert(*prev_next_ptr == curr);
         *prev_next_ptr = curr->next;
         VG_(redir_notify_delete_SegInfo)( curr );
         free_SegInfo(curr);
         return;
      }
      prev_next_ptr = &curr->next;
      curr          =  curr->next;
   }

   // Not found.
}


/* Repeatedly scan segInfo_list, looking for segInfos intersecting
   [start,start+length), and call discard_SegInfo to get rid of them.
   This modifies the list, hence the multiple iterations.
   JRS 20060401: I don't understand that last sentence. */
static void discard_syms_in_range ( Addr start, SizeT length )
{
   Bool found;
   SegInfo* curr;

   while (True) {
      found = False;

      curr = segInfo_list;
      while (True) {
         if (curr == NULL)
            break;
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
      discard_SegInfo( curr );
   }
}


/* Create a new SegInfo with the specific address/length/vma offset,
   then snarf whatever info we can from the given filename into it. */
static
SegInfo* acquire_syms_for_range( 
            /* ALL        */ Addr  seg_addr, 
            /* ALL        */ SizeT seg_len,
            /* ELF only   */ OffT  seg_offset, 
            /* ALL        */ const UChar* seg_filename,
            /* XCOFF only */ const UChar* seg_memname,
	    /* XCOFF only */ Addr  data_addr,
	    /* XCOFF only */ SizeT data_len,
	    /* XCOFF only */ Bool  is_mainexe
         )
{
   Bool     ok;
   SegInfo* si = alloc_SegInfo(seg_addr, seg_len, seg_offset, 
                               seg_filename, seg_memname);
#  if defined(VGO_linux)
   ok = ML_(read_elf_debug_info) ( si );
#  elif defined(VGO_aix5)
   ok = ML_(read_xcoff_debug_info) ( si, data_addr, data_len, is_mainexe );
#  else
#    error Unknown OS
#  endif

   if (!ok) {
      // Something went wrong (eg. bad ELF file).
      free_SegInfo( si );
      si = NULL;

   } else {
      // Prepend si to segInfo_list
      si->next = segInfo_list;
      segInfo_list = si;

      ML_(canonicaliseTables) ( si );

      /* notify m_redir about it */
      VG_(redir_notify_new_SegInfo)( si );
   }

   return si;
}


/*--------------------------------------------------------------*/
/*---                                                        ---*/
/*--- TOP LEVEL: NOTIFICATION (ACQUIRE/DISCARD INFO) (LINUX) ---*/
/*---                                                        ---*/
/*--------------------------------------------------------------*/

#if defined(VGO_linux)

/* The debug info system is driven by notifications that a text
   segment has been mapped in, or unmapped.  When that happens it
   tries to acquire/discard whatever info is available for the
   corresponding object.  This section contains the notification
   handlers. */

/* Notify the debuginfo system about a new mapping.  This is the way
   new debug information gets loaded.  If allow_SkFileV is True, it
   will try load debug info if the mapping at 'a' belongs to Valgrind;
   whereas normally (False) it will not do that.  This allows us to
   carefully control when the thing will read symbols from the
   Valgrind executable itself. */

void VG_(di_notify_mmap)( Addr a, Bool allow_SkFileV )
{
   NSegment const * seg;
   HChar*    filename;
   Bool      ok;

   /* If this mapping is at the beginning of a file, isn't part of
      Valgrind, is at least readable and seems to contain an object
      file, then try reading symbols from it.

      Getting this heuristic right is critical.  On x86-linux, objects
      are typically mapped twice:

      1b8fb000-1b8ff000 r-xp 00000000 08:02 4471477 vgpreload_memcheck.so
      1b8ff000-1b900000 rw-p 00004000 08:02 4471477 vgpreload_memcheck.so

      whereas ppc32-linux mysteriously does this:

      118a6000-118ad000 r-xp 00000000 08:05 14209428 vgpreload_memcheck.so
      118ad000-118b6000 ---p 00007000 08:05 14209428 vgpreload_memcheck.so
      118b6000-118bd000 rwxp 00000000 08:05 14209428 vgpreload_memcheck.so

      The third mapping should not be considered to have executable
      code in.  Therefore a test which works for both is: r and x and
      NOT w.  Reading symbols from the rwx segment -- which overlaps
      the r-x segment in the file -- causes the redirection mechanism
      to redirect to addresses in that third segment, which is wrong
      and causes crashes.

      ------ 
      JRS 28 Dec 05: unfortunately icc 8.1 on x86 has been seen to
      produce executables with a single rwx segment rather than a
      (r-x,rw-) pair. That means the rules have to be modified thusly:

      x86-linux:   consider if r and x
      all others:  consider if r and x and NOT w
   */
#  if defined(VGP_x86_linux)
   Bool      require_no_W = False;
#  else
   Bool      require_no_W = True;
#  endif

   seg = VG_(am_find_nsegment)(a);
   vg_assert(seg);

   filename = VG_(am_get_filename)( (NSegment*)seg );
   if (!filename)
      return;

   filename = VG_(arena_strdup)( VG_AR_SYMTAB, filename );

   ok = (seg->kind == SkFileC || (seg->kind == SkFileV && allow_SkFileV))
        && seg->offset == 0
        && seg->fnIdx != -1
        && seg->hasR
        && seg->hasX
        && (require_no_W ? (!seg->hasW) : True)
        && ML_(is_elf_object_file)( (const void*)seg->start );

   if (!ok) {
      VG_(arena_free)(VG_AR_SYMTAB, filename);
      return;
   }

   /* Dump any info previously associated with the range. */
   discard_syms_in_range( seg->start, seg->end + 1 - seg->start );

   /* .. and acquire new info. */
   acquire_syms_for_range( seg->start, seg->end + 1 - seg->start, 
                           seg->offset, filename,
                           /* XCOFF only */ NULL, 0, 0, False );

   /* acquire_syms_for_range makes its own copy of filename, so is
      safe to free it. */
   VG_(arena_free)(VG_AR_SYMTAB, filename);
}


/* Unmap is simpler - throw away any SegInfos intersecting 
   [a, a+len).  */
void VG_(di_notify_munmap)( Addr a, SizeT len )
{
   discard_syms_in_range(a, len);
}


/* Uh, this doesn't do anything at all.  IIRC glibc (or ld.so, I don't
   remember) does a bunch of mprotects on itself, and if we follow
   through here, it causes the debug info for that object to get
   discarded. */
void VG_(di_notify_mprotect)( Addr a, SizeT len, UInt prot )
{
   Bool exe_ok = toBool(prot & VKI_PROT_EXEC);
#  if defined(VGP_x86_linux)
   exe_ok = exe_ok || toBool(prot & VKI_PROT_READ);
#  endif
   if (0 && !exe_ok)
      discard_syms_in_range(a, len);
}

#endif /* defined(VGO_linux) */


/*-------------------------------------------------------------*/
/*---                                                       ---*/
/*--- TOP LEVEL: NOTIFICATION (ACQUIRE/DISCARD INFO) (AIX5) ---*/
/*---                                                       ---*/
/*-------------------------------------------------------------*/

#if defined(VGO_aix5)

/* The supplied parameters describe a code segment and its associated
   data segment, that have recently been mapped in -- so we need to
   read debug info for it -- or conversely, have recently been dumped,
   in which case the relevant debug info has to be unloaded. */

void VG_(di_aix5_notify_segchange)( 
               Addr   code_start,
               Word   code_len,
               Addr   data_start,
               Word   data_len,
               UChar* file_name,
               UChar* mem_name,
               Bool   is_mainexe,
               Bool   acquire )
{
   SegInfo* si;

   if (acquire) {

      acquire_syms_for_range(
         /* ALL        */ code_start, 
         /* ALL        */ code_len,
         /* ELF only   */ 0,
         /* ALL        */ file_name,
         /* XCOFF only */ mem_name,
         /* XCOFF only */ data_start,
         /* XCOFF only */ data_len,
         /* XCOFF only */ is_mainexe 
      );

   } else {

      /* Dump all the segInfos which intersect code_start/code_len. */
      while (True) {
         for (si = segInfo_list; si; si = si->next) {
            if (code_start + code_len <= si->start
                || si->start + si->size <= code_start)
               continue; /* no overlap */
            else 
               break;
         }
         if (si == NULL)
            break;
         /* Need to delete 'si' */
         discard_SegInfo(si);
      }

   }
}
        

#endif /* defined(VGO_aix5) */


/*------------------------------------------------------------*/
/*---                                                      ---*/
/*--- TOP LEVEL: QUERYING EXISTING DEBUG INFO              ---*/
/*---                                                      ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Use of symbol table & location info to create        ---*/
/*--- plausible-looking stack dumps.                       ---*/
/*------------------------------------------------------------*/

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
         sno = ML_(search_one_symtab) ( si, ptr, match_anywhere_in_fun );
         if (sno == -1) goto not_found;
         *symno = sno;
         *psi = si;
         return;
      }
   }
  not_found:
   *psi = NULL;
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
         lno = ML_(search_one_loctab) ( si, ptr );
         if (lno == -1) goto not_found;
         *locno = lno;
         *psi = si;
         return;
      }
   }
  not_found:
   *psi = NULL;
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
   Int used;
   SegInfo* si;

   vg_assert(nbuf > 0);
   for (si = segInfo_list; si != NULL; si = si->next) {
      if (si->start <= a && a < si->start+si->size) {
         VG_(strncpy_safely)(buf, si->filename, nbuf);
         if (si->memname) {
            used = VG_(strlen)(buf);
            if (used < nbuf) 
               VG_(strncpy_safely)(&buf[used], "(", nbuf-used);
            used = VG_(strlen)(buf);
            if (used < nbuf) 
               VG_(strncpy_safely)(&buf[used], si->memname, nbuf-used);
            used = VG_(strlen)(buf);
            if (used < nbuf) 
               VG_(strncpy_safely)(&buf[used], ")", nbuf-used);
         }
         buf[nbuf-1] = 0;
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


/* Map a function name to its entry point and toc pointer.  Is done by
   sequential search of all symbol tables, so is very slow.  To
   mitigate the worst performance effects, you may specify a soname
   pattern, and only objects matching that pattern are searched.
   Therefore specify "*" to search all the objects.  On TOC-afflicted
   platforms, a symbol is deemed to be found only if it has a nonzero
   TOC pointer.  */
Bool VG_(lookup_symbol_SLOW)(UChar* sopatt, UChar* name, Addr* pEnt, Addr* pToc)
{
   Bool     require_pToc = False;
   Int      i;
   SegInfo* si;
   Bool     debug = False;
#  if defined(VG_PLAT_USES_PPCTOC)
   require_pToc = True;
#  endif
   for (si = segInfo_list; si; si = si->next) {
      if (debug)
         VG_(printf)("lookup_symbol_SLOW: considering %s\n", si->soname);
      if (!VG_(string_match)(sopatt, si->soname)) {
         if (debug)
            VG_(printf)(" ... skip\n");
         continue;
      }
      for (i = 0; i < si->symtab_used; i++) {
         if (0==VG_(strcmp)(name, si->symtab[i].name)
             && (require_pToc ? si->symtab[i].tocptr : True)) {
            *pEnt = si->symtab[i].addr;
            *pToc = si->symtab[i].tocptr;
            return True;
         }
      }
   }
   return False;
}


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
   Bool  know_fnname  = VG_(clo_sym_offsets)
                        ? VG_(get_fnname_w_offset) (eip, buf_fn, BUF_LEN)
                        : VG_(get_fnname) (eip, buf_fn, BUF_LEN);
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
Bool VG_(use_CF_info) ( /*MOD*/Addr* ipP,
                        /*MOD*/Addr* spP,
                        /*MOD*/Addr* fpP,
                        Addr min_accessible,
                        Addr max_accessible )
{
   Int      i;
   SegInfo* si;
   DiCfSI*  cfsi = NULL;
   Addr     cfa, ipHere, spHere, fpHere, ipPrev, spPrev, fpPrev;

   static UInt n_search = 0;
   static UInt n_steps = 0;
   n_search++;

   if (0) VG_(printf)("search for %p\n", *ipP);

   for (si = segInfo_list; si != NULL; si = si->next) {
      n_steps++;

      /* Use the per-SegInfo summary address ranges to skip
	 inapplicable SegInfos quickly. */
      if (si->cfsi_used == 0)
         continue;
      if (*ipP < si->cfsi_minaddr || *ipP > si->cfsi_maxaddr)
         continue;

      i = ML_(search_one_cfitab)( si, *ipP );
      if (i != -1) {
         vg_assert(i >= 0 && i < si->cfsi_used);
         cfsi = &si->cfsi[i];
         break;
      }
   }

   if (cfsi == NULL)
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
      ML_(ppDiCfSI)(cfsi);
   }

   ipPrev = spPrev = fpPrev = 0;

   ipHere = *ipP;
   spHere = *spP;
   fpHere = *fpP;

   cfa = cfsi->cfa_off + (cfsi->cfa_sprel ? spHere : fpHere);

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

   COMPUTE(ipPrev, ipHere, cfsi->ra_how, cfsi->ra_off);
   COMPUTE(spPrev, spHere, cfsi->sp_how, cfsi->sp_off);
   COMPUTE(fpPrev, fpHere, cfsi->fp_how, cfsi->fp_off);

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

Addr VG_(seginfo_sect_start)(const SegInfo *si, VgSectKind kind) {
   switch (kind) {
   case Vg_SectData: return si->data_start_vma;
   case Vg_SectBSS:  return si-> bss_start_vma;
   case Vg_SectPLT:  return si-> plt_start_vma;
   case Vg_SectGOT:  return si-> got_start_vma;
   default:
      VG_(core_panic)("unexpected VgSectKind in seginfo_sect_start");
   }
}

SizeT VG_(seginfo_sect_size)(const SegInfo *si, VgSectKind kind) {
   switch (kind) {
   case Vg_SectData: return si->data_size;
   case Vg_SectBSS:  return si-> bss_size;
   case Vg_SectPLT:  return si-> plt_size;
   case Vg_SectGOT:  return si-> got_size;
   default:
      VG_(core_panic)("unexpected VgSectKind in seginfo_sect_size");
   }
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
                               /*OUT*/Addr*   tocptr,
                               /*OUT*/UInt*   size,
                               /*OUT*/HChar** name )
{
   vg_assert(idx >= 0 && idx < si->symtab_used);
   if (addr)   *addr   = si->symtab[idx].addr;
   if (tocptr) *tocptr = si->symtab[idx].tocptr;
   if (size)   *size   = si->symtab[idx].size;
   if (name)   *name   = (HChar*)si->symtab[idx].name;
}


/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
