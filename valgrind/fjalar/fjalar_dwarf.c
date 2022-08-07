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

/* fjalar_dwarf:
   Aspects of the DWARF debugging information that are particularly
   relevant for fjalar.
*/

#include "my_libc.h"

#include "fjalar_dwarf.h"
#include "pub_tool_basics.h"      // for VG_ macros
#include "pub_tool_libcprint.h"   // for VG_ printf macros
#include "pub_tool_libcassert.h"  // for tl_assert

// A conversion between DWARF location atoms and a string representation
const char*
location_expression_to_string(enum dwarf_location_atom op) {

  switch(op) {
  case DW_OP_addr:
    return "DW_OP_addr";
  case DW_OP_deref:
    return "DW_OP_deref";
  case DW_OP_const1u:
    return "DW_OP_const1u";
  case DW_OP_const1s:
    return "DW_OP_const1s";
  case DW_OP_const2u:
    return "DW_OP_const2u";
  case DW_OP_const2s:
    return "DW_OP_const2s";
  case DW_OP_const4u:
    return "DW_OP_const4u";
  case DW_OP_const4s:
    return "DW_OP_const4s";
  case DW_OP_const8u:
    return "DW_OP_const8u";
  case DW_OP_const8s:
    return "DW_OP_const8s";
  case DW_OP_constu:
    return "DW_OP_constu";
  case DW_OP_consts:
    return "DW_OP_consts";
  case DW_OP_dup:
    return "DW_OP_dup";
  case DW_OP_drop:
    return "DW_OP_drop";
  case DW_OP_over:
    return "DW_OP_over";
  case DW_OP_pick:
    return "DW_OP_pick";
  case DW_OP_swap:
    return "DW_OP_swap";
  case DW_OP_rot:
    return "DW_OP_rot";
  case DW_OP_xderef:
    return "DW_OP_xderef";
  case DW_OP_abs:
    return "DW_OP_abs";
  case DW_OP_and:
    return "DW_OP_and";
  case DW_OP_div:
    return "DW_OP_div";
  case DW_OP_minus:
    return "DW_OP_minus";
  case DW_OP_mod:
    return "DW_OP_mod";
  case DW_OP_mul:
    return "DW_OP_mul";
  case DW_OP_neg:
    return "DW_OP_neg";
  case DW_OP_not:
    return "DW_OP_not";
  case DW_OP_or:
    return "DW_OP_or";
  case DW_OP_plus:
    return "DW_OP_plus";
  case DW_OP_plus_uconst:
    return "DW_OP_plus_uconst";
  case DW_OP_shl:
    return "DW_OP_shl";
  case DW_OP_shr:
    return "DW_OP_shr";
  case DW_OP_shra:
    return "DW_OP_shra";
  case DW_OP_xor:
    return "DW_OP_xor";
  case DW_OP_bra:
    return "DW_OP_bra";
  case DW_OP_eq:
    return "DW_OP_eq";
  case DW_OP_ge:
    return "DW_OP_ge";
  case DW_OP_gt:
    return "DW_OP_gt";
  case DW_OP_le:
    return "DW_OP_le";
  case DW_OP_lt:
    return "DW_OP_lt";
  case DW_OP_ne:
    return "DW_OP_ne";
  case DW_OP_skip:
    return "DW_OP_skip";
  case DW_OP_lit0:
    return "DW_OP_lit0";
  case DW_OP_lit1:
    return "DW_OP_lit1";
  case DW_OP_lit2:
    return "DW_OP_lit2";
  case DW_OP_lit3:
    return "DW_OP_lit3";
  case DW_OP_lit4:
    return "DW_OP_lit4";
  case DW_OP_lit5:
    return "DW_OP_lit5";
  case DW_OP_lit6:
    return "DW_OP_lit6";
  case DW_OP_lit7:
    return "DW_OP_lit7";
  case DW_OP_lit8:
    return "DW_OP_lit8";
  case DW_OP_lit9:
    return "DW_OP_lit9";
  case DW_OP_lit10:
    return "DW_OP_lit10";
  case DW_OP_lit11:
    return "DW_OP_lit11";
  case DW_OP_lit12:
    return "DW_OP_lit12";
  case DW_OP_lit13:
    return "DW_OP_lit13";
  case DW_OP_lit14:
    return "DW_OP_lit14";
  case DW_OP_lit15:
    return "DW_OP_lit15";
  case DW_OP_lit16:
    return "DW_OP_lit16";
  case DW_OP_lit17:
    return "DW_OP_lit17";
  case DW_OP_lit18:
    return "DW_OP_lit18";
  case DW_OP_lit19:
    return "DW_OP_lit19";
  case DW_OP_lit20:
    return "DW_OP_lit20";
  case DW_OP_lit21:
    return "DW_OP_lit21";
  case DW_OP_lit22:
    return "DW_OP_lit22";
  case DW_OP_lit23:
    return "DW_OP_lit23";
  case DW_OP_lit24:
    return "DW_OP_lit24";
  case DW_OP_lit25:
    return "DW_OP_lit25";
  case DW_OP_lit26:
    return "DW_OP_lit26";
  case DW_OP_lit27:
    return "DW_OP_lit27";
  case DW_OP_lit28:
    return "DW_OP_lit28";
  case DW_OP_lit29:
    return "DW_OP_lit29";
  case DW_OP_lit30:
    return "DW_OP_lit30";
  case DW_OP_lit31:
    return "DW_OP_lit31";
  case DW_OP_reg0:
    return "DW_OP_reg0";
  case DW_OP_reg1:
    return "DW_OP_reg1";
  case DW_OP_reg2:
    return "DW_OP_reg2";
  case DW_OP_reg3:
    return "DW_OP_reg3";
  case DW_OP_reg4:
    return "DW_OP_reg4";
  case DW_OP_reg5:
    return "DW_OP_reg5";
  case DW_OP_reg6:
    return "DW_OP_reg6";
  case DW_OP_reg7:
    return "DW_OP_reg7";
  case DW_OP_reg8:
    return "DW_OP_reg8";
  case DW_OP_reg9:
    return "DW_OP_reg9";
  case DW_OP_reg10:
    return "DW_OP_reg10";
  case DW_OP_reg11:
    return "DW_OP_reg11";
  case DW_OP_reg12:
    return "DW_OP_reg12";
  case DW_OP_reg13:
    return "DW_OP_reg13";
  case DW_OP_reg14:
    return "DW_OP_reg14";
  case DW_OP_reg15:
    return "DW_OP_reg15";
  case DW_OP_reg16:
    return "DW_OP_reg16";
  case DW_OP_reg17:
    return "DW_OP_reg17";
  case DW_OP_reg18:
    return "DW_OP_reg18";
  case DW_OP_reg19:
    return "DW_OP_reg19";
  case DW_OP_reg20:
    return "DW_OP_reg20";
  case DW_OP_reg21:
    return "DW_OP_reg21";
  case DW_OP_reg22:
    return "DW_OP_reg22";
  case DW_OP_reg23:
    return "DW_OP_reg23";
  case DW_OP_reg24:
    return "DW_OP_reg24";
  case DW_OP_reg25:
    return "DW_OP_reg25";
  case DW_OP_reg26:
    return "DW_OP_reg26";
  case DW_OP_reg27:
    return "DW_OP_reg27";
  case DW_OP_reg28:
    return "DW_OP_reg28";
  case DW_OP_reg29:
    return "DW_OP_reg29";
  case DW_OP_reg30:
    return "DW_OP_reg30";
  case DW_OP_reg31:
    return "DW_OP_reg31";
  case DW_OP_breg0:
    return "DW_OP_breg0";
  case DW_OP_breg1:
    return "DW_OP_breg1";
  case DW_OP_breg2:
    return "DW_OP_breg2";
  case DW_OP_breg3:
    return "DW_OP_breg3";
  case DW_OP_breg4:
    return "DW_OP_breg4";
  case DW_OP_breg5:
    return "DW_OP_breg5";
  case DW_OP_breg6:
    return "DW_OP_breg6";
  case DW_OP_breg7:
    return "DW_OP_breg7";
  case DW_OP_breg8:
    return "DW_OP_breg8";
  case DW_OP_breg9:
    return "DW_OP_breg9";
  case DW_OP_breg10:
    return "DW_OP_breg10";
  case DW_OP_breg11:
    return "DW_OP_breg11";
  case DW_OP_breg12:
    return "DW_OP_breg12";
  case DW_OP_breg13:
    return "DW_OP_breg13";
  case DW_OP_breg14:
    return "DW_OP_breg14";
  case DW_OP_breg15:
    return "DW_OP_breg15";
  case DW_OP_breg16:
    return "DW_OP_breg16";
  case DW_OP_breg17:
    return "DW_OP_breg17";
  case DW_OP_breg18:
    return "DW_OP_breg18";
  case DW_OP_breg19:
    return "DW_OP_breg19";
  case DW_OP_breg20:
    return "DW_OP_breg20";
  case DW_OP_breg21:
    return "DW_OP_breg21";
  case DW_OP_breg22:
    return "DW_OP_breg22";
  case DW_OP_breg23:
    return "DW_OP_breg23";
  case DW_OP_breg24:
    return "DW_OP_breg24";
  case DW_OP_breg25:
    return "DW_OP_breg25";
  case DW_OP_breg26:
    return "DW_OP_breg26";
  case DW_OP_breg27:
    return "DW_OP_breg27";
  case DW_OP_breg28:
    return "DW_OP_breg28";
  case DW_OP_breg29:
    return "DW_OP_breg29";
  case DW_OP_breg30:
    return "DW_OP_breg30";
  case DW_OP_breg31:
    return "DW_OP_breg31";
  case DW_OP_regx:
    return "DW_OP_regx";
  case DW_OP_fbreg:
    return "DW_OP_fbreg";
  case DW_OP_bregx:
    return "DW_OP_bregx";
  case DW_OP_piece:
    return "DW_OP_piece";
  case DW_OP_deref_size:
    return "DW_OP_deref_size";
  case DW_OP_xderef_size:
    return "DW_OP_xderef_size";
  case DW_OP_nop:
    return "DW_OP_nop";
  case DW_OP_push_object_address:
    return "DW_OP_push_object_address";
  case DW_OP_call2:
    return "DW_OP_call2";
  case DW_OP_call4:
    return "DW_OP_call4";
  case DW_OP_call_ref:
    return "DW_OP_call_ref";
  default:
    printf("Invalid location_atom sent to location_expression_to_string: %u", op);
    tl_assert(0);
    return(0);    // to stop compiler warning
  }
}
