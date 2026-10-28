/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* fjalar_mc_main.h:

The functions that Fjalar adds to Memcheck, which mc_fjalar.h declares.
They use mc_main.c's static functions and macros, so mc_main.c includes
this file, after the definitions of those, rather than this file being
compiled on its own.  No other file may include it, because it defines
functions.

This file relies on mc_main.c's #includes and definitions, such as DEBUG,
kvasir_with_dyncomp, and set_tag.  It includes only the headers that
mc_main.c needs for this file's functions and for nothing else.

*/

#include "pub_tool_vki.h"  // needed for VKI_PROT_ defines
#include "fjalar_core_decls.h"  // for VG_(am_is_valid_for_valgrind), VG_(get_tag_ptr_for_guest_offset)

void mc_set_addressable_vbyte ( Addr a, UChar vbyte )
{
  // set_vbits8 does nothing to a byte that is not addressable.
  set_vabits2(a, VA_BITS2_UNDEFINED);
  set_vbits8(a, vbyte);
}

Bool mc_check_writable (Addr a, SizeT len, Addr* bad_addr) {
  return is_mem_addressable (a, len, bad_addr) ;
}

Bool mc_check_readable ( Addr a, SizeT len, Addr* bad_addr ) {
  if (is_mem_defined( a, len, bad_addr, NULL) != MC_Ok) return False;
  // Unfortunately, the test above lets through references to memory
  // marked executable.  Thanks to Philippe Waroquiers of the Valgrind
  // team for a way to detect this case.
  int vResult = VG_(am_is_valid_for_client)(a, len, VKI_PROT_READ) |
                VG_(am_is_valid_for_valgrind)(a, len, VKI_PROT_READ);
  return vResult != 0;
}

// PG - pgbovine - Returns true if ANY of the v-bits are set for the
// bytes in question.  (Less stringent than mc_check_readable)
char mc_are_some_bytes_initialized(Addr a, SizeT len) {
  SizeT i;
  UChar abit;

  DEBUG("mc_are_some_bytes_initialized\n");
  for (i = 0; i < len; i++) {
    abit = get_vabits2 (a);
    if((abit == VA_BITS2_PARTDEFINED) || (abit == VA_BITS2_DEFINED)) {
      return 1;
    }
    a++;
  }
  return 0;
 }

// Marks the bytes at dst addressable, gives each one the V bits of the
// corresponding byte of the register, and gives all of them the
// register's DynComp tag.
void mc_copy_guest_reg_state ( ThreadId tid, Int guestOffset, Addr dst )
{
  UWord vbits;
  SizeT b;
  VG_(get_shadow_regs_area)(tid, (UChar*)&vbits, 1/*shadowNo*/,
                            guestOffset, sizeof(Addr));
  for (b = 0; b < sizeof(Addr); b++) {
    mc_set_addressable_vbyte(dst + b, vbits >> (b * 8));
  }
  if (kvasir_with_dyncomp) {
    // DynComp keeps one tag per register, at the register's offset.
    UInt tag = *VG_(get_tag_ptr_for_guest_offset)(tid, guestOffset);
    for (b = 0; b < sizeof(Addr); b++) {
      set_tag(dst + b, tag);
    }
  }
}
