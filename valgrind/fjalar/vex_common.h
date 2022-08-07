/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2007 Stephen McCamant,
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* vex_common.h:

   This file contains VEX-related things that should IMO be in the VEX
   headers or tool-visible parts of Valgrind, but aren't.
*/

#ifndef VEX_COMMON_H
#define VEX_COMMON_H

#if defined(VGA_x86)
#include "libvex_guest_x86.h"
typedef VexGuestX86State   VexGuestArchState;
#elif defined(VGA_amd64)
#include "libvex_guest_amd64.h"
typedef VexGuestAMD64State VexGuestArchState;
#endif

#if VEX_HOST_WORDSIZE == 4
#define IRConst_Word  IRConst_I32
#define IRConst_UWord IRConst_U32
#define Ity_Word      Ity_I32
#define Ity_UWord     Ity_U32
#elif VEX_HOST_WORDSIZE == 8
#define IRConst_Word  IRConst_I64
#define IRConst_UWord IRConst_U64
#define Ity_Word      Ity_I64
#define Ity_UWord     Ity_U64
#else
#error Unknown word size
#endif

#endif /* VEX_COMMON_H */
