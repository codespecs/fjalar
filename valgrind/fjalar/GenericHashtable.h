/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

   GenericHashtable created by:
     Copyright (C) 2004 Brian Demsky, MIT CSAIL

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

// implements a generic hash table

#include "pub_tool_basics.h"

#ifndef GENHASHTABLE
#define GENHASHTABLE
#define geninitialnumbins 4999
#define genSMALLinitialnumbins 97 // PG

struct genhashtable {
  unsigned int (*hash_function)(void *);
  int (*comp_function)(void *,void *);
  struct genpointerlist ** bins;
  long counter;
  int currentsize;
  Bool string_type;
  struct genpointerlist *list;
  struct genpointerlist *last;
};


struct genpointerlist {
  void * src;
  void * object;
  struct genpointerlist * next;

  struct genpointerlist * inext;
  struct genpointerlist * iprev;
};


struct geniterator {
  struct genpointerlist * ptr;
  int finished; // boolean
};

struct genhashtable * genallocatehashtable(unsigned int (*hash_function)(void *),int (*comp_function)(void *,void *));
struct genhashtable * genallocateSMALLhashtable(unsigned int (*hash_function)(void *),int (*comp_function)(void *,void *));
void genfreehashtable(struct genhashtable * ht);
void genfreehashtableandvalues(struct genhashtable * ht);

void * getnext(struct genhashtable *,void *);
int genputtable(struct genhashtable *, void *, void *);
int genputstringtable(struct genhashtable *, const char *, void *);
void * gengettable(struct genhashtable *, void *);
int gencontains(struct genhashtable *, void *);
unsigned int genhashfunction(struct genhashtable *,void *);

int hashsize(struct genhashtable * ht);
void genfreekey(struct genhashtable *ht, void *);
struct geniterator * gengetiterator(struct genhashtable *ht);
void * gennext(struct geniterator *it);
void genfreeiterator(struct geniterator *it);
#endif
