/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

  Copyright (C) 2004-2005 Philip Guo, MIT CSAIL Program Analysis Group

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

#include "tool.h"

// WARNING! Some comments may be bogus because I've copied-and-pasted
// from MemCheck

typedef  IRExpr  IRAtom;

/* Carries around state during DynComp instrumentation. */
struct _DCEnv;

typedef
   struct _DCEnv {
      /* MODIFIED: the bb being constructed.  IRStmts are added. */
      IRBB* bb;

      /* MODIFIED: a table [0 .. #temps_in_original_bb-1] which maps
         original temps to their current their current shadow temp.
         Initially all entries are IRTemp_INVALID.  Entries are added
         lazily since many original temps are not used due to
         optimisation prior to instrumentation.  Note that floating
         point original tmps are shadowed by integer tmps of the same
         size, and Bit-typed original tmps are shadowed by the type
         Ity_I8.  See comment below. */
      IRTemp* tmpMap;
      Int     n_originalTmps; /* for range checking */

      /* MODIFIED: indicates whether "bogus" literals have so far been
         found.  Starts off False, and may change to True. */
      Bool    bogusLiterals;

      /* READONLY: the guest layout.  This indicates which parts of
         the guest state should be regarded as 'always defined'. */
      VexGuestLayout* layout;
      /* READONLY: the host word type.  Needed for constructing
         arguments of type 'HWord' to be passed to helper functions.
         Ity_I32 or Ity_I64 only. */
      IRType hWordTy;
   }
   DCEnv;

IRTemp findShadowTmp_DC ( DCEnv* dce, IRTemp orig );
IRExpr* expr2tags_DC ( DCEnv* dce, IRExpr* e );
void do_shadow_PUT_DC ( DCEnv* dce,  Int offset,
                        IRAtom* atom, IRAtom* vatom );
void do_shadow_PUTI_DC ( DCEnv* dce,
                         IRArray* descr, IRAtom* ix, Int bias, IRAtom* atom );
void do_shadow_STle_DC ( DCEnv* dce,
                         IRAtom* addr, UInt bias,
                         IRAtom* data );
IRAtom* do_shadow_cond_exit_DC (DCEnv* dce, IRExpr* guard);

#endif
