/*
   This file is part of Kvasir, a Valgrind skin that implements the
   C language front-end for the Daikon Invariant Detection System

   Copyright (C) 2004 Brian Demsky, MIT CSAIL

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdlib.h>
#include <values.h>
#include "GenericHashtable.h"
#include "tool_asm.h" //#include "vg_constants_skin.h"
//#include "dmalloc.h"

extern void  VG_(free)           ( void* p );
extern void* VG_(calloc)         ( unsigned int n, unsigned int bytes_per_elem );

int genputtable(struct genhashtable *ht, void * key, void * object) {
  unsigned int bin=genhashfunction(ht,key);
  struct genpointerlist * newptrlist=(struct genpointerlist *) VG_(calloc)(1,sizeof(struct genpointerlist));
  newptrlist->src=key;
  newptrlist->object=object;
  newptrlist->next=ht->bins[bin];
  newptrlist->inext=NULL;
  /* maintain linked list of ht entries for iteration*/
  if (ht->last==NULL) {
    ht->last=newptrlist;
    ht->list=newptrlist;
    newptrlist->iprev=NULL;
  } else {
    ht->last->inext=newptrlist;
    newptrlist->iprev=ht->last;
    ht->last=newptrlist;
  }
  ht->bins[bin]=newptrlist;
  ht->counter++;
  if(ht->counter>ht->currentsize&&ht->currentsize!=MAXINT) {
    /* Expand hashtable */
    long newcurrentsize=(ht->currentsize<(MAXINT/2))?ht->currentsize*2:MAXINT;
    long oldcurrentsize=ht->currentsize;
    //    VG_(printf)("genputtable() - resize - old: %u, new: %u\n", oldcurrentsize, newcurrentsize);
    struct genpointerlist **newbins=(struct genpointerlist **) VG_(calloc)(1,sizeof (struct genpointerlist *)*newcurrentsize);
    struct genpointerlist **oldbins=ht->bins;
    long j,i;
    for(j=0;j<newcurrentsize;j++) newbins[j]=NULL;
    ht->currentsize=newcurrentsize;
    for(i=0;i<oldcurrentsize;i++) {
      struct genpointerlist * tmpptr=oldbins[i];
      while(tmpptr!=NULL) {
        int hashcode=genhashfunction(ht, tmpptr->src);
        struct genpointerlist *nextptr=tmpptr->next;
        tmpptr->next=newbins[hashcode];
        newbins[hashcode]=tmpptr;
        tmpptr=nextptr;
      }
    }
    ht->bins=newbins;
    VG_(free)(oldbins);
  }
  return 1;
}

int hashsize(struct genhashtable *ht) {
  return ht->counter;
}

void * gengettable(struct genhashtable *ht, void * key) {
  struct genpointerlist * ptr=ht->bins[genhashfunction(ht,key)];
  while(ptr!=NULL) {
    if (((ht->comp_function==NULL)&&(ptr->src==key))||((ht->comp_function!=NULL)&&(*ht->comp_function)(ptr->src,key)))
      return ptr->object;
    ptr=ptr->next;
  }
  //  printf("XXXXXXXXX: COULDN'T FIND ENTRY FOR KEY %p\n",key);
  return NULL;
}

void * getnext(struct genhashtable *ht, void * key) {
  struct genpointerlist * ptr=ht->bins[genhashfunction(ht,key)];
  while(ptr!=NULL) {
    if (((ht->comp_function==NULL)&&(ptr->src==key))||((ht->comp_function!=NULL)&&(*ht->comp_function)(ptr->src,key))) {
      if (ptr->inext!=NULL) {
	return ptr->inext->src;
      } else {
	  return NULL;
      }
    }
    ptr=ptr->next;
  }
  //  printf("XXXXXXXXX: COULDN'T FIND ENTRY FOR KEY %p...\n Likely concurrent removal--bad user!!!\n",key);
  return NULL;
}

int gencontains(struct genhashtable *ht, void * key) {
  struct genpointerlist * ptr=ht->bins[genhashfunction(ht,key)];
  //printf("In gencontains2\n");fflush(NULL);
  while(ptr!=NULL) {
    if (((ht->comp_function==NULL)&&(ptr->src==key))||((ht->comp_function!=NULL)&&(*ht->comp_function)(ptr->src,key)))
      return 1;
    ptr=ptr->next;
  }
  return 0;
}


void genfreekey(struct genhashtable *ht, void * key) {
  struct genpointerlist * ptr=ht->bins[genhashfunction(ht,key)];

  if (((ht->comp_function==NULL)&&(ptr->src==key))||((ht->comp_function!=NULL)&&(*ht->comp_function)(ptr->src,key))) {
    ht->bins[genhashfunction(ht,key)]=ptr->next;

    if (ptr==ht->last)
      ht->last=ptr->iprev;

    if (ptr==ht->list)
      ht->list=ptr->inext;

    if (ptr->iprev!=NULL)
      ptr->iprev->inext=ptr->inext;
    if (ptr->inext!=NULL)
      ptr->inext->iprev=ptr->iprev;

    VG_(free)(ptr);
    ht->counter--;
    return;
  }
  while(ptr->next!=NULL) {
    if (((ht->comp_function==NULL)&&(ptr->next->src==key))||((ht->comp_function!=NULL)&&(*ht->comp_function)(ptr->next->src,key))) {
      struct genpointerlist *tmpptr=ptr->next;
      ptr->next=tmpptr->next;
      if (tmpptr==ht->list)
	ht->list=tmpptr->inext;
      if (tmpptr==ht->last)
	ht->last=tmpptr->iprev;
      if (tmpptr->iprev!=NULL)
	tmpptr->iprev->inext=tmpptr->inext;
      if (tmpptr->inext!=NULL)
	tmpptr->inext->iprev=tmpptr->iprev;
      VG_(free)(tmpptr);
      ht->counter--;
      return;
    }
    ptr=ptr->next;
  }
  //  printf("XXXXXXXXX: COULDN'T FIND ENTRY FOR KEY %p\n",key);
}

unsigned int genhashfunction(struct genhashtable *ht, void * key) {
  if (ht->hash_function==NULL)
    return ((long unsigned int)key) % ht->currentsize;
  else
    return ((*ht->hash_function)(key)) % ht->currentsize;
}

struct genhashtable * genallocatehashtable(unsigned int (*hash_function)(void *),int (*comp_function)(void *, void *)) {
  struct genhashtable *ght=(struct genhashtable *) VG_(calloc)(1,sizeof(struct genhashtable));
  //  VG_(printf)("genallocate() - allocate - initial: %u\n", geninitialnumbins);
  struct genpointerlist **gpl=(struct genpointerlist **) VG_(calloc)(1,sizeof(struct genpointerlist *)*geninitialnumbins);
  int i;
  for(i=0;i<geninitialnumbins;i++)
    gpl[i]=NULL;
  ght->hash_function=hash_function;
  ght->comp_function=comp_function;
  ght->currentsize=geninitialnumbins;
  ght->bins=gpl;
  ght->counter=0;
  ght->list=NULL;
  ght->last=NULL;
  return ght;
}

// PG - Copy-and-paste to create smaller hash tables to not waste as much space.
struct genhashtable * genallocateSMALLhashtable(unsigned int (*hash_function)(void *),int (*comp_function)(void *, void *)) {
  struct genhashtable *ght=(struct genhashtable *) VG_(calloc)(1,sizeof(struct genhashtable));
  //  VG_(printf)("genallocatesmall() - allocate - initial: %u\n", genSMALLinitialnumbins);
  struct genpointerlist **gpl=(struct genpointerlist **) VG_(calloc)(1,sizeof(struct genpointerlist *)*genSMALLinitialnumbins);
  int i;
  for(i=0;i<genSMALLinitialnumbins;i++)
    gpl[i]=NULL;
  ght->hash_function=hash_function;
  ght->comp_function=comp_function;
  ght->currentsize=genSMALLinitialnumbins;
  ght->bins=gpl;
  ght->counter=0;
  ght->list=NULL;
  ght->last=NULL;
  return ght;
}

void genfreehashtable(struct genhashtable * ht) {
  int i;
  for (i=0;i<ht->currentsize;i++) {
    if (ht->bins[i]!=NULL) {
      struct genpointerlist *genptr=ht->bins[i];
      while(genptr!=NULL) {
	struct genpointerlist *tmpptr=genptr->next;
	VG_(free)(genptr);
	genptr=tmpptr;
      }
    }
  }
  //  VG_(printf)("genfreetable()\n");
  VG_(free)(ht->bins);
  VG_(free)(ht);
}

// Do not use this if you are not storing pointers to heap-allocated
// objects in the hash table
void genfreehashtableandvalues(struct genhashtable * ht) {
  int i;
  for (i=0;i<ht->currentsize;i++) {
    if (ht->bins[i]!=NULL) {
      struct genpointerlist *genptr=ht->bins[i];
      while(genptr!=NULL) {
	struct genpointerlist *tmpptr=genptr->next;
        VG_(free)(genptr->object); // Also free the object in the hash table
	VG_(free)(genptr);
	genptr=tmpptr;
      }
    }
  }
  VG_(free)(ht->bins);
  VG_(free)(ht);
}

struct geniterator * gengetiterator(struct genhashtable *ht) {
  struct geniterator *gi=(struct geniterator*)VG_(calloc)(1,sizeof(struct geniterator));
  gi->ptr=ht->list;
  return gi;
}

void * gennext(struct geniterator *it) {
  struct genpointerlist *curr=it->ptr;
  if (curr==NULL)
    return NULL;
  if (it->finished&&(curr->inext==NULL))
    return NULL;
  if (it->finished) {
    it->ptr=curr->inext;
    return it->ptr->src;
  }
  if(curr->inext!=NULL)
    it->ptr=curr->inext;
  else
    it->finished=1; /* change offsetting scheme */
  return curr->src;
}

void genfreeiterator(struct geniterator *it) {
  VG_(free)(it);
}
