// Implementation of generic union-find data structure
// with union-by-rank and path-compression
// Based on http://www.cs.rutgers.edu/~chvatal/notes/uf.html
// Philip Guo

#ifndef UNION_FIND_H
#define UNION_FIND_H

// Comment this out if you do not want to utilize reference counting
#define USE_REF_COUNT

typedef struct _uf_object uf_object;

// 10 bytes total (12 bytes with ref_count)
struct _uf_object {
  uf_object* parent;         // 4 bytes
  // The tag which corresponds to this uf_object
  // (0 means invalid tag)
  unsigned int tag;          // 4 bytes

  unsigned short rank;       // 2 bytes

#ifdef USE_REF_COUNT

  // ref_count serves two purposes (this is a bit tricky): It both
  // refers to the number of other uf_object entries whose parent
  // field points to this particular uf_object, and it refers to the
  // number of times the tag associated with this entry appears
  // anywhere in the program (the same locations where tags reside for
  // the garbage collection algorithm: memory, registers, and per
  // program point). Notice that when a uf_object is a singleton set,
  // its own parent points to itself, but we do NOT count that as a
  // ref_count of 1 since ref_count refers to the number of OTHER
  // uf_object entries that point to this one.
  unsigned short ref_count;  // 2 bytes
#endif
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


#ifdef USE_REF_COUNT

// 'Lock' the value of ref_count at (USHRT_MAX - 1) if it ever reaches
// that high (highly unlikely, though).  USHRT_MAX is a reserved
// sentinel value for uf_object entries that are on the free list

#define INC_REF_COUNT(obj) if (obj->ref_count < (USHRT_MAX - 1))        \
    ((obj->ref_count)++)

// Tricky!  Don't decrement ref_count below 0 and have it underflow!
// This could happen if you are in a singleton set (you are your own
// parent) so your ref_count is 0, but someone requests that your
// parents ref_count decrement, thus bringing your ref_count to -1,
// which is actually USHRT_MAX since ref_count is unsigned ... that
// would be BAD!
#define DEC_REF_COUNT(obj) if ((obj->ref_count) &&                      \
                               (obj->ref_count < (USHRT_MAX - 1)))      \
    ((obj->ref_count)--)
#else
#define INC_REF_COUNT(obj)
#define DEC_REF_COUNT(obj)
#endif


#endif //UNION_FIND_H
