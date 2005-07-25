/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Philip Guo, MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* kvasir_runtime.h:
   Contains the type definitions for Kvasir runtime interactions with Valgrind
*/

#ifndef KVASIR_RUNTIME_H
#define KVASIR_RUNTIME_H

#include "tool.h"
#include "typedata.h"
#include "generate_daikon_data.h"
#include "kvasir_main.h"

//#define SHOW_DEBUG

// Runtime entries for function entrances and exits
// used mainly by fn_stack in kvasir_main.c
typedef struct _Entry {
     Char* name; // Function name
     Addr  EBP; // %ebp as calculated from %esp at function entrance time
     Addr startPC; // the starting PC address of the function
     Addr  lowestESP; // The LOWEST value of %ESP that is encountered
                      // while we are in this function -
                      // We need this to see how deep a function penetrates
                      // into the stack to see what is safe to dereference
                      // when this function exits
     // Return values of function exit -
     // These should NOT be valid on the stack, they should
     // only be valid right after popping an entry off the
     // stack upon function exit:
     // (TODO: What does this mean?  Is this still valid?)

     // As of Valgrind 3.0, we now keep V-bits for all of these
     // in the shadow memory:
     int EAX; // %EAX
     int EDX; // %EDX
     double FPU; // FPU %st(0)

     // This is a copy of the portion of the Valgrind stack
     // that is above EBP - it holds function formal parameter
     // values that was passed into this function upon entrance.
     // We reference this virtualStack at function exit in order
     // to print out the SAME formal parameter values upon exit
     // as upon entrance.
     char* virtualStack;
     int virtualStackByteSize; // Number of 1-byte entries in virtualStack

     VarList* localArrayVariablesPtr; // Pointer to the list that the corresponding
                                      // DaikonFunctionInfo structure contains

} FunctionEntry;


void handleFunctionEntrance(FunctionEntry* e);
void handleFunctionExit(FunctionEntry* e);

//char okayToPrintThisProgramPoint(DaikonFunctionInfo* daikonFuncPtr);
void updateAllDaikonFunctionInfoEntries();
void updateAllGlobalVariableNames();

void outputFormalParamsAndGlobals(FunctionEntry* e, DaikonFunctionInfo* daikonFuncPtr, char isEnter);
void outputReturnValue(FunctionEntry* e, DaikonFunctionInfo* daikonFuncPtr);
void outputObjectAndClassPPTs(FunctionEntry* e, DaikonFunctionInfo* daikonFuncPtr, char isEnter);

FunctionEntry* returnFunctionEntryWithAddress(Addr a);
DaikonVariable* returnGlobalArrayOrStructVariableWithAddress(Addr a, int* arrayFound);

int probeAheadDiscoverHeapArraySize(Addr startAddr, UInt typeSize);
int returnArrayUpperBoundFromPtr(DaikonVariable* var, Addr varLocation);
int getBytesBetweenElts(DaikonVariable* var);

#define addressIsAllocated(addressInQuestion, numBytes) addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 1)
#define addressIsInitialized(addressInQuestion, numBytes) addressIsAllocatedOrInitialized(addressInQuestion, numBytes, 0)

char addressIsAllocatedOrInitialized(Addr addressInQuestion, unsigned int numBytes, char allocatedOrInitialized);
char are_some_bytes_init(Addr addressInQuestion, unsigned int numBytes);

#endif
