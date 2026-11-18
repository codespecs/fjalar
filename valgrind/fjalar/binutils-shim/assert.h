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

/* Fjalar's replacement for <assert.h>, for the copies of Binutils files.
   A Valgrind tool uses tl_assert instead of the C library's assert.  See
   sysdep.h in this directory.  */

#ifndef FJALAR_BINUTILS_ASSERT_H
#define FJALAR_BINUTILS_ASSERT_H

#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"

#define assert(expr) tl_assert (expr)

#endif /* FJALAR_BINUTILS_ASSERT_H */
