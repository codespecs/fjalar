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

/* Fjalar's replacement for the system <wchar.h>, which conflicts with
   my_libc.h.  readelf.c includes it, but uses nothing in it, because
   HAVE_MBSTATE_T is not defined.  See sysdep.h in this directory.  */
