/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2009 Julian
  Seward, jseward@acm.org)

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

#ifndef DYNCOMP_TRANSLATE_H
#define DYNCOMP_TRANSLATE_H

#include "mc_translate.h"

#include "libvex.h"              // for all Vex stuff

IRTemp findShadowTmp_DC ( DCEnv* dce, IRTemp orig );
IRExpr* expr2tags_DC ( DCEnv* dce, IRExpr* e );
void do_shadow_PUT_DC ( DCEnv* dce,  Int offset,
                        IRAtom* atom, IRAtom* vatom );
void do_shadow_PUTI_DC ( DCEnv* dce, IRPutI *puti );
void do_shadow_STle_DC ( DCEnv* dce, IRAtom* addr, IRAtom* data );
IRAtom* do_shadow_cond_exit_DC (DCEnv* dce, IRExpr* guard);

void do_shadow_CAS_DC ( DCEnv* dce, IRCAS* cas );

void do_shadow_Dirty_DC ( DCEnv* dce, IRDirty* d );

#endif
