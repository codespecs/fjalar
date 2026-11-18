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

/* fjalar_mc_translate.h:

The functions that Fjalar adds to Memcheck's instrumenter, which
mc_translate.h declares.  They use mc_translate.c's definition of MCEnv
and its static functions, so mc_translate.c includes this file, after
the definitions of those, rather than this file being compiled on its
own.  No other file may include it, because it defines functions.

Fjalar's other code uses MCEnv only through these functions, so that
MCEnv and Memcheck's other definitions stay in mc_translate.c, where
upstream changes to them merge.

*/

// Adds st to the superblock that Memcheck is building.  cat is the
// category that --fjalar-print-ir prints with st.
void mc_stmt ( HChar cat, MCEnv* mce, IRStmt* st )
{
   stmt(cat, mce, st);
}

// Returns a new temporary of type ty, to hold a DynComp tag.
IRTemp newTemp_DC ( MCEnv* mce, IRType ty )
{
   return newTemp(mce, ty, DC);
}

// Returns Memcheck's shadow type for ty, which is the integer type of
// the same size.  DynComp uses it for sizes, but its tags are always
// Ity_Word.
IRType shadowTypeV_DC ( IRType ty )
{
   return shadowTypeV(ty);
}

// Sets the fields of dce that come from mce, which is Memcheck's state
// for the same superblock.
void init_DCEnv_from_MCEnv ( DCEnv* dce, MCEnv* mce )
{
   dce->mce     = mce;
   dce->bb      = mce->sb;
   dce->layout  = mce->layout;
   dce->hWordTy = mce->hWordTy;
   dce->trace   = mce->trace;
}
