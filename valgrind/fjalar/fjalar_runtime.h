/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

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

#include "tool.h"
#include "typedata.h"
#include "generate_fjalar_entries.h"

//#define MAXIMUM_ARRAY_SIZE_TO_EXPAND 10

void updateAllFunctionEntryNames();

int probeAheadDiscoverHeapArraySize(Addr startAddr, UInt typeSize);
int returnArrayUpperBoundFromPtr(VariableEntry* var, Addr varLocation);
int getBytesBetweenElts(VariableEntry* var);

#define addressIsAllocated(addressInQuestion, numBytes) addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 1)
#define addressIsInitialized(addressInQuestion, numBytes) addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 0)

char addressIsAllocatedOrInitialized(Addr addressInQuestion, unsigned int numBytes, char allocatedOrInitialized);
char are_some_bytes_init(Addr addressInQuestion, unsigned int numBytes);

void fixBuffering(FILE *fp);

#endif
