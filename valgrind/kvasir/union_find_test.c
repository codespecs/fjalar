// Test of union-find data structure
// by Philip Guo

#include "union_find.h"

#define SIZE 7
const char names[SIZE] = "abcdefg";

void print_sets(uf_object* obj_array, int size) {
  int i;
  for (i = 0; i < size; i++) {
    uf_object* cur_obj = obj_array + i;
    printf("%c) value: %p, ref_count: %hu, leader: %p\n",
           names[i],
           cur_obj,
           cur_obj->ref_count,
           uf_find(cur_obj));
  }
  printf("\n");
}

int main() {
  // Treat this as an array of 7 uf_objects
  uf_object obj_array[SIZE];

  int i;

  // Give them nice names:
  uf_object* a = obj_array;
  uf_object* b = obj_array + 1;
  uf_object* c = obj_array + 2;
  uf_object* d = obj_array + 3;
  uf_object* e = obj_array + 4;
  uf_object* f = obj_array + 5;
  uf_object* g = obj_array + 6;

  for (i = 0; i < SIZE; i++) {
    uf_make_set(obj_array + i);
  }
  printf("{a} {b} {c} {d} {e} {f} {g}\n");
  print_sets(obj_array, SIZE);

  uf_union(a, b);
  printf("{a, b} {c} {d} {e} {f} {g}\n");
  print_sets(obj_array, SIZE);

  uf_union(c, d);
  printf("{a, b} {c, d} {e} {f} {g}\n");
  print_sets(obj_array, SIZE);

  uf_union(e, f);
  printf("{a, b} {c, d} {e, f} {g}\n");
  print_sets(obj_array, SIZE);

  uf_union(g, f);
  printf("{a, b} {c, d} {e, f, g}\n");
  print_sets(obj_array, SIZE);

  uf_union(c, a);
  printf("{a, b, c, d} {e, f, g}\n");
  print_sets(obj_array, SIZE);

  return 0;
}
