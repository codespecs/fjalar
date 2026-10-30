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

/* Definitions that the headers of the copies of Binutils files, such as
   elfcomm.h and dwarf.h, need.  Binutils' sysdep.h provides them, but
   Fjalar's own files include those headers without sysdep.h.  Fjalar's
   replacement for sysdep.h, in this directory, includes this file, and so
   does fjalar_dwarf.h.  */

#ifndef FJALAR_BINUTILS_H
#define FJALAR_BINUTILS_H

/* Binutils' sysdep.h defines it as long long if that is wider than long.  */
#define HOST_WIDEST_INT long

/* elfcomm.c defines error and warn, which print a message.  Valgrind's core
   defines a global error function too, in coregrind/m_gdbserver/utils.c,
   so rename them.  */
#define error fjalar_binutils_error
#define warn fjalar_binutils_warn

#endif /* FJALAR_BINUTILS_H */
