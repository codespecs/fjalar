// Implementation of generic union-find data structure
// with union-by-rank and path-compression
// Based on http://www.cs.rutgers.edu/~chvatal/notes/uf.html
// Philip Guo

// Augmented with a reference count for every uf_object
// which denotes how many other uf_objects point to it

#ifndef UNION_FIND_H
#define UNION_FIND_H

typedef struct _uf_object uf_object;

// 12 bytes total
struct _uf_object {
  uf_object* parent;         // 4 bytes
  unsigned short rank;       // 2 bytes
  unsigned short ref_count;  // 2 bytes
  // The tag which corresponds to this uf_object
  // (0 means invalid tag)
  unsigned int tag;          // 4 bytes
};

// the name of the equivalence class is the pointer to the root of the tree
typedef uf_object* uf_name;

// given a pointer to an object held in the ADT
// returns the name of the equivalence class to which the object belongs;
uf_name uf_find(uf_object *object);

// given a pointer to an object not held in the ADT,
// adds the new object to the data structure as a single-element equivalence class;
// Also sets new_object->tag to t
void uf_make_set(uf_object *new_object, unsigned int t, char saturate);

// given names of two elements, merges the sets of the two elements into one
// and returns the new leader (uf_name)
uf_name uf_union(uf_object *obj1, uf_object *obj2);

#endif //UNION_FIND_H
