/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

// Implementation of generic union-find data structure
// with union-by-rank and path-compression
// Based on http://www.cs.rutgers.edu/~chvatal/notes/uf.html

#ifndef UNION_FIND_H
#define UNION_FIND_H

typedef struct _uf_object uf_object;

// 12/16 bytes total
struct _uf_object {
  uf_object* parent;         // 4/8 bytes
  // The tag which corresponds to this uf_object
  // (0 means invalid tag)
  unsigned int tag;          // 4 bytes

  unsigned short rank;       // 2 bytes
                             // 2 bytes for alignment
};

// the name of the equivalence class is the pointer to the root of the tree
typedef uf_object* uf_name;

// given a pointer to an object held in the ADT
// returns the name of the equivalence class to which the object belongs;
uf_name uf_find(uf_object *object);

// given a pointer to an object not held in the ADT,
// adds the new object to the data structure as a single-element equivalence class;
// Also sets new_object->tag to t
void uf_make_set(uf_object *new_object, unsigned int t);

// given names of two elements, merges the sets of the two elements into one
// and returns the new leader (uf_name)
uf_name uf_union(uf_object *obj1, uf_object *obj2);

#endif //UNION_FIND_H
