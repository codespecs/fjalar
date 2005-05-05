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

#ifndef DYNCOMP_MAIN_H
#define DYNCOMP_MAIN_H

#include "tool.h"

// Don't do anything with tags equal to 0 because they are invalid
#define IS_ZERO_TAG(tag) (0 == tag)

__inline__ void clear_all_tags_in_range( Addr a, SizeT len );
__inline__ void allocate_new_unique_tags ( Addr a, SizeT len );
__inline__ void copy_tags(  Addr src, Addr dst, SizeT len );

__inline__ UInt get_tag ( Addr a );
__inline__ void set_tag ( Addr a, UInt tag );

void val_uf_union_tags_in_range(Addr a, SizeT len);
__inline__ void val_uf_union_tags_at_addr(Addr a1, Addr a2);
__inline__ UInt val_uf_find_leader(UInt tag);

#endif
