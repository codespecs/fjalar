/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2026 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* Fjalar's replacement for Binutils' include/libiberty.h.  Fjalar does not
   link with libiberty; this file defines only what the copies of Binutils
   files use.  See sysdep.h in this directory.  */

#ifndef FJALAR_BINUTILS_LIBIBERTY_H
#define FJALAR_BINUTILS_LIBIBERTY_H

#include "ansidecl.h"

#define ARRAY_SIZE(a) (sizeof (a) / sizeof ((a)[0]))

#endif /* FJALAR_BINUTILS_LIBIBERTY_H */
