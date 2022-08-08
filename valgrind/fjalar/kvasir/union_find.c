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

#include "../my_libc.h"

#include "union_find.h"
#include "kvasir_main.h"

// caller guarantees that object is non-NULL
uf_name uf_find(uf_object *object) {
  uf_object *root, *next;

  // Find the root:
  for(root=object; root->parent!=root; root=root->parent);

  // Path-compression:
  for(next=object->parent; next!=root; object=next, next=object->parent) {
    object->parent=root;
  }

  DYNCOMP_TPRINTF("[DynComp] uf_find: %p, %u, %p, %u \n", object, object->tag, root, root->tag);
  return root;
}

// parent might not be NULL; should we free it?
// no - these objects are allocated two different ways:
// for values: they are not allocated individually, but within a large
// block of objects - just go ahead and overwrite
// for variables: they are allocated individually, but this routine is
// always called with a freshly allocated pointer.
void uf_make_set(uf_object *new_object, unsigned int t) {
  DYNCOMP_TPRINTF("[DynComp] uf_make_set: %p, %u\n", new_object, t);
  new_object->parent = new_object;
  new_object->rank = 0;
  new_object->tag = t;
}

// caller guarantees that obj1 and obj2 are non-NULL
// Returns the new leader (uf_name)
// Stupid question: Is there any problems that arise
// when uf_union is called multiple times on the same objects?
// I don't think so, right?
uf_name uf_union(uf_object *obj1, uf_object *obj2) {
  uf_name class1 = uf_find(obj1);
  uf_name class2 = uf_find(obj2);
  DYNCOMP_TPRINTF("[DynComp] union_find1: %p, %u, %p, %u %d\n", obj1, obj1->tag, class1, class1->tag, class1->rank);
  DYNCOMP_TPRINTF("[DynComp] union_find2: %p, %u, %p, %u %d\n", obj2, obj2->tag, class2, class2->tag, class2->rank);
  
  // Union-by-rank:

  // If class1 == class2, then obj1 and obj2 are already
  // in the same set so don't do anything! (Is this correct?)
  if (class1 == class2) {
    return class1;
  }

  if (class1->rank < class2->rank) {
    class1->parent = class2;
    return class2;
  } else {
    class2->parent = class1;
    if (class1->rank == class2->rank) {
      (class1->rank)++;
    }
    return class1;
  }
}
