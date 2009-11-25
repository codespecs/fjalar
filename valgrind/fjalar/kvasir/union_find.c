/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2005 Julian
  Seward, jseward@acm.org)

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

#include "union_find.h"
#include "kvasir_main.h"
#include "../my_libc.h"

uf_name uf_find(uf_object *object) {
  uf_object *root, *next;

  // Find the root:
  for(root=object; root->parent!=root; root=root->parent);

  // Path-compression:
  if(!dyncomp_no_path_compression) {
    for(next=object->parent; next!=root; object=next, next=object->parent) {
      object->parent=root;
    }
  }

  return root;
}

void uf_make_set(uf_object *new_object, unsigned int t) {
  new_object->parent = new_object;
  new_object->rank = 0;
  new_object->tag = t;
}

// Returns the new leader (uf_name)
// Stupid question: Is there any problems that arise
// when uf_union is called multiple times on the same objects?
// I don't think so, right?
uf_name uf_union(uf_object *obj1, uf_object *obj2) {
  uf_name class1 = uf_find(obj1);
  uf_name class2 = uf_find(obj2);
  
  // Union-by-rank:

  // If class1 == class2, then obj1 and obj2 are already
  // in the same set so don't do anything! (Is this correct?)
  if (class1 == class2) {
    return class1;
  }

  if(class1->rank < class2->rank) {
    class1->parent = class2;
    return class2;
  }
  else {
    class2->parent = class1;
    if(class1->rank == class2->rank) {
      (class1->rank)++;
    }
    return class1;
  }
}
