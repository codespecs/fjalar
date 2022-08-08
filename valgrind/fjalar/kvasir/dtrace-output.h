/*
   This file is part of Kvasir, a C/C++ front end for the Daikon
   dynamic invariant detector built upon the Fjalar framework

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* dtrace-output.h:
   Functions for outputting Kvasir runtime variable values
   to a Daikon-compatible .dtrace file
*/

#ifndef DTRACE_OUTPUT_H
#define DTRACE_OUTPUT_H

#include "../fjalar_include.h"

void printDtraceForFunction(FunctionExecutionState* f_state, char isEnter);

#endif
