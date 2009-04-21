
/*--------------------------------------------------------------------*/
/*--- User-mode execve(), and other stuff shared between stage1    ---*/
/*--- and stage2.                                          m_ume.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2008 Julian Seward 
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


#include "pub_core_basics.h"
#include "pub_core_vki.h"

#if defined(VGO_linux)

#include "pub_core_aspacemgr.h"   // various mapping fns
#include "pub_core_debuglog.h"
#include "pub_core_libcbase.h"
#include "pub_core_machine.h"
#include "pub_core_libcprint.h"
#include "pub_core_libcfile.h"    // VG_(close) et al
#include "pub_core_libcproc.h"    // VG_(geteuid), VG_(getegid)
#include "pub_core_libcassert.h"  // VG_(exit), vg_assert
#include "pub_core_mallocfree.h"  // VG_(malloc), VG_(free)
#include "pub_core_syscall.h"     // VG_(strerror)
#include "pub_core_options.h"     // VG_(clo_xml)
#include "pub_core_ume.h"         // self

/* --- !!! --- EXTERNAL HEADERS start --- !!! --- */
#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
/* This is for ELF types etc, and also the AT_ constants. */
#include <elf.h>
/* --- !!! --- EXTERNAL HEADERS end --- !!! --- */


#if	VG_WORDSIZE == 8
#define ESZ(x)	Elf64_##x
#elif	VG_WORDSIZE == 4
#define ESZ(x)	Elf32_##x
#else
#error VG_WORDSIZE needs to ==4 or ==8
#endif

struct elfinfo
{
   ESZ(Ehdr)	e;
   ESZ(Phdr)	*p;
   Int		fd;
};

static void check_mmap(SysRes res, Addr base, SizeT len)
{
   if (res.isError) {
      VG_(printf)("valgrind: mmap(0x%llx, %lld) failed in UME "
                  "with error %lu (%s).\n", 
                  (ULong)base, (Long)len, 
                  res.err, VG_(strerror)(res.err) );
      if (res.err == VKI_EINVAL) {
         VG_(printf)("valgrind: this can be caused by executables with "
                     "very large text, data or bss segments.\n");
      }
      VG_(exit)(1);
   }
}

/*------------------------------------------------------------*/
/*--- Finding auxv on the stack                            ---*/
/*------------------------------------------------------------*/

struct ume_auxv *VG_(find_auxv)(UWord* sp)
{
   sp++;                // skip argc (Nb: is word-sized, not int-sized!)

   while (*sp != 0)     // skip argv
      sp++;
   sp++;

   while (*sp != 0)     // skip env
      sp++;
   sp++;
   
#if defined(VGA_ppc32) || defined(VGA_ppc64)
# if defined AT_IGNOREPPC
   while (*sp == AT_IGNOREPPC)        // skip AT_IGNOREPPC entries
      sp += 2;
# endif
#endif

   return (struct ume_auxv *)sp;
}

/*------------------------------------------------------------*/
/*--- Loading ELF files                                    ---*/
/*------------------------------------------------------------*/

static 
struct elfinfo *readelf(Int fd, const char *filename)
{
   SysRes sres;
   struct elfinfo *e = VG_(malloc)("ume.re.1", sizeof(*e));
   Int phsz;

   vg_assert(e);
   e->fd = fd;

   sres = VG_(pread)(fd, &e->e, sizeof(e->e), 0);
   if (sres.isError || sres.res != sizeof(e->e)) {
      VG_(printf)("valgrind: %s: can't read ELF header: %s\n", 
                  filename, VG_(strerror)(sres.err));
      goto bad;
   }

   if (VG_(memcmp)(&e->e.e_ident[0], ELFMAG, SELFMAG) != 0) {
      VG_(printf)("valgrind: %s: bad ELF magic number\n", filename);
      goto bad;
   }
   if (e->e.e_ident[EI_CLASS] != VG_ELF_CLASS) {
      VG_(printf)("valgrind: wrong ELF executable class "
                  "(eg. 32-bit instead of 64-bit)\n");
      goto bad;
   }
   if (e->e.e_ident[EI_DATA] != VG_ELF_DATA2XXX) {
      VG_(printf)("valgrind: executable has wrong endian-ness\n");
      goto bad;
   }
   if (!(e->e.e_type == ET_EXEC || e->e.e_type == ET_DYN)) {
      VG_(printf)("valgrind: this is not an executable\n");
      goto bad;
   }

   if (e->e.e_machine != VG_ELF_MACHINE) {
      VG_(printf)("valgrind: executable is not for "
                  "this architecture\n");
      goto bad;
   }

   if (e->e.e_phentsize != sizeof(ESZ(Phdr))) {
      VG_(printf)("valgrind: sizeof ELF Phdr wrong\n");
      goto bad;
   }

   phsz = sizeof(ESZ(Phdr)) * e->e.e_phnum;
   e->p = VG_(malloc)("ume.re.2", phsz);
   vg_assert(e->p);

   sres = VG_(pread)(fd, e->p, phsz, e->e.e_phoff);
   if (sres.isError || sres.res != phsz) {
      VG_(printf)("valgrind: can't read phdr: %s\n", 
                  VG_(strerror)(sres.err));
      VG_(free)(e->p);
      goto bad;
   }

   return e;

  bad:
   VG_(free)(e);
   return NULL;
}

/* Map an ELF file.  Returns the brk address. */
static
ESZ(Addr) mapelf(struct elfinfo *e, ESZ(Addr) base)
{
   Int    i;
   SysRes res;
   ESZ(Addr) elfbrk = 0;

   for(i = 0; i < e->e.e_phnum; i++) {
      ESZ(Phdr) *ph = &e->p[i];
      ESZ(Addr) addr, brkaddr;
      ESZ(Word) memsz;

      if (ph->p_type != PT_LOAD)
	 continue;

      addr    = ph->p_vaddr+base;
      memsz   = ph->p_memsz;
      brkaddr = addr+memsz;

      if (brkaddr > elfbrk)
	 elfbrk = brkaddr;
   }

   for(i = 0; i < e->e.e_phnum; i++) {
      ESZ(Phdr) *ph = &e->p[i];
      ESZ(Addr) addr, bss, brkaddr;
      ESZ(Off) off;
      ESZ(Word) filesz;
      ESZ(Word) memsz;
      unsigned prot = 0;

      if (ph->p_type != PT_LOAD)
	 continue;

      if (ph->p_flags & PF_X) prot |= VKI_PROT_EXEC;
      if (ph->p_flags & PF_W) prot |= VKI_PROT_WRITE;
      if (ph->p_flags & PF_R) prot |= VKI_PROT_READ;

      addr    = ph->p_vaddr+base;
      off     = ph->p_offset;
      filesz  = ph->p_filesz;
      bss     = addr+filesz;
      memsz   = ph->p_memsz;
      brkaddr = addr+memsz;

      // Tom says: In the following, do what the Linux kernel does and only
      // map the pages that are required instead of rounding everything to
      // the specified alignment (ph->p_align).  (AMD64 doesn't work if you
      // use ph->p_align -- part of stage2's memory gets trashed somehow.)
      //
      // The condition handles the case of a zero-length segment.
      if (VG_PGROUNDUP(bss)-VG_PGROUNDDN(addr) > 0) {
         if (0) VG_(debugLog)(0,"ume","mmap_file_fixed_client #1\n");
         res = VG_(am_mmap_file_fixed_client)(
                  VG_PGROUNDDN(addr),
                  VG_PGROUNDUP(bss)-VG_PGROUNDDN(addr),
                  prot, /*VKI_MAP_FIXED|VKI_MAP_PRIVATE, */
                  e->fd, VG_PGROUNDDN(off)
               );
         if (0) VG_(am_show_nsegments)(0,"after #1");
         check_mmap(res, VG_PGROUNDDN(addr),
                         VG_PGROUNDUP(bss)-VG_PGROUNDDN(addr));
      }

      // if memsz > filesz, fill the remainder with zeroed pages
      if (memsz > filesz) {
	 UInt bytes;

	 bytes = VG_PGROUNDUP(brkaddr)-VG_PGROUNDUP(bss);
	 if (bytes > 0) {
            if (0) VG_(debugLog)(0,"ume","mmap_anon_fixed_client #2\n");
	    res = VG_(am_mmap_anon_fixed_client)(
                     VG_PGROUNDUP(bss), bytes,
		     prot
                  );
            if (0) VG_(am_show_nsegments)(0,"after #2");
            check_mmap(res, VG_PGROUNDUP(bss), bytes);
         }

	 bytes = bss & (VKI_PAGE_SIZE - 1);

         // The 'prot' condition allows for a read-only bss
         if ((prot & VKI_PROT_WRITE) && (bytes > 0)) {
	    bytes = VKI_PAGE_SIZE - bytes;
	    VG_(memset)((char *)bss, 0, bytes);
	 }
      }
   }

   return elfbrk;
}

static Bool match_ELF(const char *hdr, Int len)
{
   ESZ(Ehdr) *e = (ESZ(Ehdr) *)hdr;
   return (len > sizeof(*e)) && VG_(memcmp)(&e->e_ident[0], ELFMAG, SELFMAG) == 0;
}


/* load_ELF pulls an ELF executable into the address space, prepares
   it for execution, and writes info about it into INFO.  In
   particular it fills in .init_eip, which is the starting point.

   Returns zero on success, non-zero (a VKI_E.. value) on failure.

   The sequence of activities is roughly as follows:

   - use readelf() to extract program header info from the exe file.

   - scan the program header, collecting info (not sure what all those
     info-> fields are, or whether they are used, but still) and in
     particular looking out fo the PT_INTERP header, which describes
     the interpreter.  If such a field is found, the space needed to
     hold the interpreter is computed into interp_size.

   - map the executable in, by calling mapelf().  This maps in all
     loadable sections, and I _think_ also creates any .bss areas
     required.  mapelf() returns the address just beyond the end of
     the furthest-along mapping it creates.  The executable is mapped
     starting at EBASE, which is usually read from it (eg, 0x8048000
     etc) except if it's a PIE, in which case I'm not sure what
     happens.

     The returned address is recorded in info->brkbase as the start
     point of the brk (data) segment, as it is traditional to place
     the data segment just after the executable.  Neither load_ELF nor
     mapelf creates the brk segment, though: that is for the caller of
     load_ELF to attend to.

   - If the initial phdr scan didn't find any mention of an
     interpreter (interp == NULL), this must be a statically linked
     executable, and we're pretty much done.

   - Otherwise, we need to use mapelf() a second time to load the
     interpreter.  The interpreter can go anywhere, but mapelf() wants
     to be told a specific address to put it at.  So an advisory query
     is passed to aspacem, asking where it would put an anonymous
     client mapping of size INTERP_SIZE.  That address is then used
     as the mapping address for the interpreter.

   - The entry point in INFO is set to the interpreter's entry point,
     and we're done.  */
static Int load_ELF(Int fd, const HChar* name, /*MOD*/ExeInfo* info)
{
   SysRes sres;
   struct elfinfo *e;
   struct elfinfo *interp = NULL;
   ESZ(Addr) minaddr = ~0;	/* lowest mapped address */
   ESZ(Addr) maxaddr = 0;	/* highest mapped address */
   ESZ(Addr) interp_addr = 0;	/* interpreter (ld.so) address */
   ESZ(Word) interp_size = 0;	/* interpreter size */
   ESZ(Word) interp_align = VKI_PAGE_SIZE;
   Int i;
   void *entry;
   ESZ(Addr) ebase = 0;

   /* The difference between where the interpreter got mapped and
      where it asked to be mapped.  Needed for computing the ppc64 ELF
      entry point and initial tocptr (R2) value. */
   ESZ(Word) interp_offset = 0;

#ifdef HAVE_PIE
   ebase = info->exe_base;
#endif

   e = readelf(fd, name);

   if (e == NULL)
      return VKI_ENOEXEC;

   /* The kernel maps position-independent executables at TASK_SIZE*2/3;
      duplicate this behavior as close as we can. */
   if (e->e.e_type == ET_DYN && ebase == 0) {
      ebase = VG_PGROUNDDN(info->exe_base 
                           + (info->exe_end - info->exe_base) * 2 / 3);
      /* We really don't want to load PIEs at zero or too close.  It
         works, but it's unrobust (NULL pointer reads and writes
         become legit, which is really bad) and causes problems for
         exp-ptrcheck, which assumes all numbers below 1MB are
         nonpointers.  So, hackily, move it above 1MB. */
      /* Later .. is appears ppc32-linux tries to put [vdso] at 1MB,
         which totally screws things up, because nothing else can go
         there.  So bump the hacky load addess along by 0x8000, to
         0x108000. */
      if (ebase < 0x108000)
         ebase = 0x108000;
   }

   info->phnum = e->e.e_phnum;
   info->entry = e->e.e_entry + ebase;
   info->phdr = 0;

   for(i = 0; i < e->e.e_phnum; i++) {
      ESZ(Phdr) *ph = &e->p[i];

      switch(ph->p_type) {
      case PT_PHDR:
	 info->phdr = ph->p_vaddr + ebase;
	 break;

      case PT_LOAD:
	 if (ph->p_vaddr < minaddr)
	    minaddr = ph->p_vaddr;
	 if (ph->p_vaddr+ph->p_memsz > maxaddr)
	    maxaddr = ph->p_vaddr+ph->p_memsz;
	 break;
			
      case PT_INTERP: {
         HChar *buf = VG_(malloc)("ume.LE.1", ph->p_filesz+1);
	 Int j;
	 Int intfd;
	 Int baseaddr_set;

         vg_assert(buf);
	 VG_(pread)(fd, buf, ph->p_filesz, ph->p_offset);
	 buf[ph->p_filesz] = '\0';

	 sres = VG_(open)(buf, VKI_O_RDONLY, 0);
         if (sres.isError) {
	    VG_(printf)("valgrind: m_ume.c: can't open interpreter\n");
	    VG_(exit)(1);
	 }
         intfd = sres.res;

	 interp = readelf(intfd, buf);
	 if (interp == NULL) {
	    VG_(printf)("valgrind: m_ume.c: can't read interpreter\n");
	    return 1;
	 }
	 VG_(free)(buf);

	 baseaddr_set = 0;
	 for(j = 0; j < interp->e.e_phnum; j++) {
	    ESZ(Phdr) *iph = &interp->p[j];
	    ESZ(Addr) end;

	    if (iph->p_type != PT_LOAD)
	       continue;
	    
	    if (!baseaddr_set) {
	       interp_addr  = iph->p_vaddr;
	       interp_align = iph->p_align;
	       baseaddr_set = 1;
	    }

	    /* assumes that all segments in the interp are close */
	    end = (iph->p_vaddr - interp_addr) + iph->p_memsz;

	    if (end > interp_size)
	       interp_size = end;
	 }
	 break;

      default:
         // do nothing
         break;
      }
      }
   }

   if (info->phdr == 0)
      info->phdr = minaddr + ebase + e->e.e_phoff;

   if (info->exe_base != info->exe_end) {
      if (minaddr >= maxaddr ||
	  (minaddr + ebase < info->exe_base ||
	   maxaddr + ebase > info->exe_end)) {
	 VG_(printf)("Executable range %p-%p is outside the\n"
                     "acceptable range %p-%p\n",
                     (char *)minaddr + ebase, (char *)maxaddr + ebase,
                     (char *)info->exe_base,  (char *)info->exe_end);
	 return VKI_ENOMEM;
      }
   }

   info->brkbase = mapelf(e, ebase);	/* map the executable */

   if (info->brkbase == 0)
      return VKI_ENOMEM;

   if (interp != NULL) {
      /* reserve a chunk of address space for interpreter */
      MapRequest mreq;
      Addr       advised;
      Bool       ok;

      /* Don't actually reserve the space.  Just get an advisory
         indicating where it would be allocated, and pass that to
         mapelf(), which in turn asks aspacem to do some fixed maps at
         the specified address.  This is a bit of hack, but it should
         work because there should be no intervening transactions with
         aspacem which could cause those fixed maps to fail.

         Placement policy is:

         if the interpreter asks to be loaded at zero
            ignore that and put it wherever we like (mappings at zero 
            are bad news)
         else
            try and put it where it asks for, but if that doesn't work,
            just put it anywhere.
      */
      if (interp_addr == 0) {
         mreq.rkind = MAny;
         mreq.start = 0;
         mreq.len   = interp_size;
      } else {
         mreq.rkind = MHint;
         mreq.start = interp_addr;
         mreq.len   = interp_size;
      }

      advised = VG_(am_get_advisory)( &mreq, True/*client*/, &ok );

      if (!ok) {
         /* bomb out */
         SysRes res = VG_(mk_SysRes_Error)(VKI_EINVAL);
         if (0) VG_(printf)("reserve for interp: failed\n");
         check_mmap(res, (Addr)interp_addr, interp_size);
         /*NOTREACHED*/
      }

      (void)mapelf(interp, (ESZ(Addr))advised - interp_addr);

      VG_(close)(interp->fd);

      entry = (void *)(advised - interp_addr + interp->e.e_entry);
      info->interp_base = (ESZ(Addr))advised;
      interp_offset = advised - interp_addr;

      VG_(free)(interp->p);
      VG_(free)(interp);
   } else
      entry = (void *)(ebase + e->e.e_entry);

   info->exe_base = minaddr + ebase;
   info->exe_end  = maxaddr + ebase;

#if defined(VGP_ppc64_linux)
   /* On PPC64, a func ptr is represented by a TOC entry ptr.  This
      TOC entry contains three words; the first word is the function
      address, the second word is the TOC ptr (r2), and the third word
      is the static chain value. */
   info->init_ip  = ((ULong*)entry)[0];
   info->init_toc = ((ULong*)entry)[1];
   info->init_ip  += interp_offset;
   info->init_toc += interp_offset;
#else
   info->init_ip  = (Addr)entry;
   info->init_toc = 0; /* meaningless on this platform */
#endif
   VG_(free)(e->p);
   VG_(free)(e);

   return 0;
}


static Bool match_script(char *hdr, Int len)
{
   Char* end    = hdr + len;
   Char* interp = hdr + 2;

   // len < 4: need '#', '!', plus at least a '/' and one more char
   if (len < 4) return False;    
   if (0 != VG_(memcmp)(hdr, "#!", 2)) return False;

   // Find interpreter name, make sure it's an absolute path (starts with
   // '/') and has at least one more char.  First, skip over any space
   // between the #! and the start of the interpreter name
   while (interp < end && VG_(isspace)(*interp)) interp++;

   // overrun?
   if (interp >= end)   return False;  // can't find start of interp name

   // interp should now point at the /
   if (*interp != '/')  return False;  // absolute path only for interpreter

   // check for something plausible after the /
   interp++;
   if (interp >= end)   return False;
   if (VG_(isspace)(*interp)) return False;

   // Here we should get the full interpreter name and check it with
   // check_executable().  See the "EXEC FAILED" failure when running shell
   // for an example.

   return True;   // looks like a #! script
}

// Forward declaration.
static Int do_exec_inner(const HChar* exe, ExeInfo* info);

/* returns: 0 = success, non-0 is failure */
static Int load_script(Int fd, const HChar* name, ExeInfo* info)
{
   Char  hdr[4096];
   Int   len = 4096;
   Int   eol;
   Char* interp;
   Char* end;
   Char* cp;
   Char* arg = NULL;
   SysRes res;

   // Read the first part of the file.
   res = VG_(pread)(fd, hdr, len, 0);
   if (res.isError) {
      VG_(close)(fd);
      return VKI_EACCES;
   } else {
      len = res.res;
   }

   vg_assert('#' == hdr[0] && '!' == hdr[1]);

   end    = hdr + len;
   interp = hdr + 2;
   while (interp < end && VG_(isspace)(*interp))
      interp++;

   vg_assert(*interp == '/');   /* absolute path only for interpreter */

   /* skip over interpreter name */
   for (cp = interp; cp < end && !VG_(isspace)(*cp); cp++)
      ;

   eol = (*cp == '\n');

   *cp++ = '\0';

   if (!eol && cp < end) {
      /* skip space before arg */
      while (cp < end && VG_(isspace)(*cp) && *cp != '\n')
	 cp++;

      /* arg is from here to eol */
      arg = cp;
      while (cp < end && *cp != '\n')
	 cp++;
      *cp = '\0';
   }
   
   info->interp_name = VG_(strdup)("ume.ls.1", interp);
   vg_assert(NULL != info->interp_name);
   if (arg != NULL && *arg != '\0') {
      info->interp_args = VG_(strdup)("ume.ls.2", arg);
      vg_assert(NULL != info->interp_args);
   }

   if (info->argv && info->argv[0] != NULL)
      info->argv[0] = (char *)name;

   if (0)
      VG_(printf)("#! script: interp_name=\"%s\" interp_args=\"%s\"\n",
                  info->interp_name, info->interp_args);

   return do_exec_inner(interp, info);
}


typedef enum {
   VG_EXE_FORMAT_ELF    = 1,
   VG_EXE_FORMAT_SCRIPT = 2,
} ExeFormat;

// Check the file looks executable.
SysRes 
VG_(pre_exec_check)(const HChar* exe_name, Int* out_fd, Bool allow_setuid)
{
   Int fd, ret;
   SysRes res;
   Char  buf[4096];
   SizeT bufsz = 4096, fsz;
   Bool is_setuid = False;

   // Check it's readable
   res = VG_(open)(exe_name, VKI_O_RDONLY, 0);
   if (res.isError) {
      return res;
   }
   fd = res.res;

   // Check we have execute permissions
   ret = VG_(check_executable)(&is_setuid, (HChar*)exe_name, allow_setuid);
   if (0 != ret) {
      VG_(close)(fd);
      if (is_setuid && !VG_(clo_xml)) {
         VG_(message)(Vg_UserMsg, "");
         VG_(message)(Vg_UserMsg,
                      "Warning: Can't execute setuid/setgid executable: %s",
                      exe_name);
         VG_(message)(Vg_UserMsg, "Possible workaround: remove "
                      "--trace-children=yes, if in effect");
         VG_(message)(Vg_UserMsg, "");
      }
      return VG_(mk_SysRes_Error)(ret);
   }

   fsz = (SizeT)VG_(fsize)(fd);
   if (fsz < bufsz)
      bufsz = fsz;

   res = VG_(pread)(fd, buf, bufsz, 0);
   if (res.isError || res.res != bufsz) {
      VG_(close)(fd);
      return VG_(mk_SysRes_Error)(VKI_EACCES);
   }
   bufsz = res.res;

   if (match_ELF(buf, bufsz)) {
      res = VG_(mk_SysRes_Success)(VG_EXE_FORMAT_ELF);
   } else if (match_script(buf, bufsz)) {
      res = VG_(mk_SysRes_Success)(VG_EXE_FORMAT_SCRIPT);
   } else {
      res = VG_(mk_SysRes_Error)(VKI_ENOEXEC);
   }

   // Write the 'out_fd' param if necessary, or close the file.
   if (!res.isError && out_fd) {
      *out_fd = fd; 
   } else { 
      VG_(close)(fd);
   }

   return res;
}

// returns: 0 = success, non-0 is failure
//
// We can execute only ELF binaries or scripts that begin with "#!".  (Not,
// for example, scripts that don't begin with "#!";  see the VG_(do_exec)()
// invocation from m_main.c for how that's handled.)
static Int do_exec_inner(const HChar *exe, ExeInfo* info)
{
   SysRes res;
   Int fd;
   Int ret;

   res = VG_(pre_exec_check)(exe, &fd, False/*allow_setuid*/);
   if (res.isError)
      return res.err;

   switch (res.res) {
    case VG_EXE_FORMAT_ELF:    ret = load_ELF   (fd, exe, info); break;
    case VG_EXE_FORMAT_SCRIPT: ret = load_script(fd, exe, info); break;
    default:
      vg_assert2(0, "unrecognised VG_EXE_FORMAT value\n");
   }

   VG_(close)(fd);

   return ret;
}


static Bool is_hash_bang_file(Char* f)
{
   SysRes res = VG_(open)(f, VKI_O_RDONLY, 0);
   if (!res.isError) {
      Char buf[3] = {0,0,0};
      Int fd = res.res;
      Int n  = VG_(read)(fd, buf, 2); 
      if (n == 2 && VG_STREQ("#!", buf))
         return True;
   }
   return False;
}

// Look at the first 80 chars, and if any are greater than 127, it's binary.
// This is crude, but should be good enough.  Note that it fails on a
// zero-length file, as we want.
static Bool is_binary_file(Char* f)
{
   SysRes res = VG_(open)(f, VKI_O_RDONLY, 0);
   if (!res.isError) {
      UChar buf[80];
      Int fd = res.res;
      Int n  = VG_(read)(fd, buf, 80); 
      Int i;
      for (i = 0; i < n; i++) {
         if (buf[i] > 127)
            return True;      // binary char found
      }
      return False;
   } else {
      // Something went wrong.  This will only happen if we earlier
      // succeeded in opening the file but fail here (eg. the file was
      // deleted between then and now).
      VG_(printf)("valgrind: %s: unknown error\n", f);
      VG_(exit)(126);      // 126 == NOEXEC
   }
}

// If the do_exec fails we try to emulate what the shell does (I used
// bash as a guide).  It's worth noting that the shell can execute some
// things that VG_(do_exec)() (which subsitutes for the kernel's exec())
// will refuse to (eg. scripts lacking a "#!" prefix).
static Int do_exec_shell_followup(Int ret, HChar* exe_name,
                                  ExeInfo* info)
{
   Char*  default_interp_name = "/bin/sh";
   SysRes res;
   struct vg_stat st;

   if (VKI_ENOEXEC == ret) {
      // It was an executable file, but in an unacceptable format.  Probably
      // is a shell script lacking the "#!" prefix;  try to execute it so.

      // Is it a binary file?  
      if (is_binary_file(exe_name)) {
         VG_(printf)("valgrind: %s: cannot execute binary file\n", exe_name);
         VG_(exit)(126);      // 126 == NOEXEC
      }

      // Looks like a script.  Run it with /bin/sh.  This includes
      // zero-length files.

      info->interp_name = VG_(strdup)("ume.desf.1", default_interp_name);
      info->interp_args = NULL;
      if (info->argv && info->argv[0] != NULL)
         info->argv[0] = (char *)exe_name;

      ret = do_exec_inner(info->interp_name, info);

      if (0 != ret) {
         // Something went wrong with executing the default interpreter
         VG_(printf)("valgrind: %s: bad interpreter (%s): %s\n",
                     exe_name, info->interp_name, VG_(strerror)(ret));
         VG_(exit)(126);      // 126 == NOEXEC
      }

   } else if (0 != ret) {
      // Something else went wrong.  Try to make the error more specific,
      // and then print a message and abort.
   
      // Was it a directory?
      res = VG_(stat)(exe_name, &st);
      if (!res.isError && VKI_S_ISDIR(st.st_mode)) {
         VG_(printf)("valgrind: %s: is a directory\n", exe_name);
      
      // Was it not executable?
      } else if (0 != VG_(check_executable)(NULL, exe_name, 
                                            False/*allow_setuid*/)) {
         VG_(printf)("valgrind: %s: %s\n", exe_name, VG_(strerror)(ret));

      // Did it start with "#!"?  If so, it must have been a bad interpreter.
      } else if (is_hash_bang_file(exe_name)) {
         VG_(printf)("valgrind: %s: bad interpreter: %s\n",
                     exe_name, VG_(strerror)(ret));

      // Otherwise it was something else.
      } else {
         VG_(printf)("valgrind: %s: %s\n", exe_name, VG_(strerror)(ret));
      }
      // 126 means NOEXEC;  I think this is Posix, and that in some cases we
      // should be returning 127, meaning NOTFOUND.  Oh well.
      VG_(exit)(126);
   }
   return ret;
}


// This emulates the kernel's exec().  If it fails, it then emulates the
// shell's handling of the situation.
// See ume.h for an indication of which entries of 'info' are inputs, which
// are outputs, and which are both.
/* returns: 0 = success, non-0 is failure */
Int VG_(do_exec)(const HChar* exe_name, ExeInfo* info)
{
   Int ret;
   
   info->interp_name = NULL;
   info->interp_args = NULL;

   ret = do_exec_inner(exe_name, info);

   if (0 != ret) {
      Char* exe_name_casted = (Char*)exe_name;
      ret = do_exec_shell_followup(ret, exe_name_casted, info);
   }
   return ret;
}

#endif /* defined(VGO_linux) */

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
