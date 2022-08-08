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

/* fjalar_runtime.h:

Contains functions that interact with the Valgrind core after
initialization and provides run-time functionality that is useful for
tools.

*/

#ifndef FJALAR_RUNTIME_H
#define FJALAR_RUNTIME_H

//#include "tool.h"
#include "typedata.h"
#include "generate_fjalar_entries.h"
#include "fjalar_include.h"

//#define MAXIMUM_ARRAY_SIZE_TO_EXPAND 10

int probeAheadDiscoverHeapArraySize(Addr startAddr, UInt typeSize);

#endif
