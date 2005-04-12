// Implementation of generic union-find data structure
// with union-by-rank and path-compression
// Based on http://www.cs.rutgers.edu/~chvatal/notes/uf.html
// Philip Guo

// Augmented with a reference count for every uf_object
// which denotes how many other uf_objects point to it

#include "union_find.h"
#include <limits.h>

// The reference count saturates at USHRT_MAX and does not
// decrement if it ever reaches that high:
static inline void inc_ref_count(uf_object *obj) {
  if (obj->ref_count < USHRT_MAX) {
    (obj->ref_count)++;
  }
}

static inline void dec_ref_count(uf_object *obj) {
  if (obj->ref_count < USHRT_MAX) {
    (obj->ref_count)--;
  }
}

uf_name uf_find(uf_object *object) {
  uf_object *root, *next;

  // Find the root:
  for(root=object; root->parent!=root; root=root->parent);

  // Path-compression:
  for(next=object->parent; next!=root; object=next, next=object->parent) {
    object->parent=root;
    inc_ref_count(root);
    dec_ref_count(next);
  }

  return root;
}

void uf_make_set(uf_object *new_object) {
  new_object->parent = new_object;
  new_object->rank = 0;
  new_object->ref_count = 0;
}

// Returns the new leader (uf_name)
uf_name uf_union(uf_object *obj1, uf_object *obj2) {
  uf_name class1 = uf_find(obj1);
  uf_name class2 = uf_find(obj2);

  // Union-by-rank:
  if(class1->rank < class2->rank) {
    class1->parent = class2;
    inc_ref_count(class2);
    return class2;
  }
  else {
    class2->parent = class1;
    inc_ref_count(class1);
    if(class1->rank == class2->rank) {
      (class1->rank)++;
    }
    return class1;
  }
}
