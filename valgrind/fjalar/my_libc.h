/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/* Headers for replacement implementations of libc-like functions that
   aren't provided in Valgrind's core. */

#ifndef MY_LIBC_H
#define MY_LIBC_H

/* These aren't in libc, but I find myself using them a lot, so this is
   a good place to define them once and for all. -SMcC */
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

#include "config.h"
#include "sys/types.h"
#include <stdarg.h>
#include <stdbool.h>

#define _(String) (String)

#define PARAMS(args)		args
#define VPARAMS(args)		args
#define VA_START(VA_LIST, VAR)	va_start(VA_LIST, VAR)

#define VA_OPEN(AP, VAR)		{ va_list AP; va_start(AP, VAR); { struct Qdmy
#define VA_CLOSE(AP)			} va_end(AP); }
#define VA_FIXEDARG(AP, TYPE, NAME)	struct Qdmy

/* alloca.h */
extern void *alloca (size_t __size);
#define alloca(size)   __builtin_alloca (size)

/* ctype.h */
int isalnum(int c);
int isalpha(int c);
int isdigit(int c);
int isspace(int c);
int isxdigit(int c);

/* errno.h */

extern int errno;

/* search.h */

struct tree_iter_t;
typedef int (*__compar_fn_t) (const void *, const void *);

typedef enum
{
  preorder,
  postorder,
  endorder,
  leaf
}
VISIT;

/* Search for an entry matching the given KEY in the tree pointed to
   by *ROOTP and insert a new element if not found.  */
void *tsearch (const void *__key, void **__rootp,
	       __compar_fn_t __compar);

/* Search for an entry matching the given KEY in the tree pointed to
   by *ROOTP.  If no matching entry is available return NULL.  */
void *tfind (const void *__key, void *const *__rootp,
	     __compar_fn_t __compar);

/* Remove the element matching KEY from the tree pointed to by *ROOTP.  */
void *tdelete (const void *__restrict __key,
	       void **__restrict __rootp,
	       __compar_fn_t __compar);

/* Retrieve an pre-order traversal tree iterator for tree pointed to by *VROOT */
struct tree_iter_t *titer(const void *__vroot);

/* Are there any more nodes left in the tree? */
int titer_hasnext(struct tree_iter_t *__it);

/* Retrieve the key of the next element in the tree */
void *titer_next(struct tree_iter_t *__it);

/* Free the tree iterator */
void titer_destroy(struct tree_iter_t *__it);

typedef void (*__action_fn_t) (const void *__nodep, VISIT __value,
                               int __level);

/* Walk through the whole tree and call the ACTION callback for every node
   or leaf.  */
extern void twalk (const void *__root, __action_fn_t __action);


/* Callback type for function to free a tree node.  If the keys are atomic
   data this function should do nothing.  */
typedef void (*__free_fn_t) (void *__nodep);


/* Destroy the whole tree, call FREEFCT for each node or leaf.  */
extern void tdestroy (void *__root, __free_fn_t __freefct);

/* stddef.h */

#ifdef __GNUC__
typedef __PTRDIFF_TYPE__ ptrdiff_t;
typedef __SIZE_TYPE__ size_t;
#if !defined(__cplusplus)
typedef __WCHAR_TYPE__ wchar_t;
#endif
#else
typedef signed long ptrdiff_t;
typedef unsigned long size_t;
typedef int wchar_t;
#endif

#undef NULL
#if defined(__cplusplus)
#define NULL 0
#else
#define NULL (void*)0
#endif

#undef offsetof
#define offsetof(type,member) ((size_t) &((type*)0)->member)

/* stdio.h */

/* The possibilities for the third argument to `fseek'.
   These values should not be changed.  */
#define SEEK_SET	0	/* Seek from beginning of file.  */
#define SEEK_CUR	1	/* Seek from current position.  */
#define SEEK_END	2	/* Seek from end of file.  */
struct __stdio_file;
typedef struct __stdio_file FILE;

extern FILE *stdin, *stdout, *stderr;

FILE *fopen (const char *path, const char *mode);
FILE *fdopen(int filedes, const char *mode);
FILE *fd_open(const char *path, const char *mode, int *out_fd);
int fflush(FILE *stream);
int fclose(FILE *stream);

int feof(FILE *stream);
int ferror(FILE *stream);

int fgetc(FILE *stream);
char *fgets(char *s, int size, FILE *stream);
size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);

#undef putc
#undef putchar
int putc(int c, FILE *stream);
int putchar(int c);
/* putc and putchar are traditionally macros, but defining them as
   functions too seems maximally compatible. */
#define putc(c,stream) fputc(c,stream)
#define putchar(c) fputc(c,stdout)
int fputc(int c, FILE *stream);
int fputs(const char *s, FILE *stream);
int puts(const char *s);
size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);

int printf(const char *format, ...) __attribute__((__format__(__printf__,1,2)));
int fprintf(FILE *stream, const char *format, ...) __attribute__((__format__(__printf__,2,3)));
int sprintf(char *str, const char *format, ...) __attribute__((__format__(__printf__,2,3)));
int snprintf(char *str, size_t size, const char *format, ...) __attribute__((__format__(__printf__,3,4)));

int vprintf(const char *format, va_list ap) __attribute__((__format__(__printf__,1,0)));
int vfprintf(FILE *stream, const char *format, va_list ap) __attribute__((__format__(__printf__,2,0)));
int vsprintf(char *str, const char *format, va_list ap) __attribute__((__format__(__printf__,2,0)));
int vsnprintf(char *str, size_t size, const char *format, va_list ap) __attribute__((__format__(__printf__,3,0)));

int fseek(FILE *stream, long offset, int whence);
long ftell(FILE *stream);

#define EOF (-1)

/* stdlib.h */

// rename from abort to avoid conflict with coregrind::abort (markro)
void my_abort(void);

long int strtol(const char *nptr, char **endptr, int base);
unsigned long int strtoul(const char *nptr, char **endptr, int base);
int atoi(const char* s);

/* string.h */

char *strtok(char *s, const char *delim);
const char* my_strerror(int errnum);

/* unistd.h */

int mkfifo(const char *fn, __mode_t mode);

/* bfd/bfd-in.h */

#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
/* Return TRUE if the start of STR matches PREFIX, FALSE otherwise.  */
static inline bool
startswith (const char *str, const char *prefix)
{
  return VG_(strncmp) (str, prefix, VG_(strlen) (prefix)) == 0;
}

#endif /* MY_LIBC_H */
