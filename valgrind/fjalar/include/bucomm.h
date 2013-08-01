/* bucomm.h -- binutils common include file.
   Copyright 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000,
   2002, 2003 Free Software Foundation, Inc.

   This file is part of GNU Binutils.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.  */

#ifndef _BUCOMM_H
#define _BUCOMM_H

#include <stdarg.h>

#include "ansidecl.h"

#include "config.h"
#include "bin-bugs.h"

#ifdef USE_BINARY_FOPEN
#include "fopen-bin.h"
#else
#include "fopen-same.h"
#endif

#ifdef NEED_DECLARATION_STRSTR
extern char *strstr ();
#endif

#ifdef HAVE_SBRK
#ifdef NEED_DECLARATION_SBRK
extern char *sbrk ();
#endif
#endif

#ifdef NEED_DECLARATION_GETENV
extern char *getenv ();
#endif

#ifdef NEED_DECLARATION_ENVIRON
extern char **environ;
#endif

#ifndef O_RDONLY
#define O_RDONLY 0
#endif

#ifndef O_RDWR
#define O_RDWR 2
#endif

#ifndef SEEK_SET
#define SEEK_SET 0
#endif
#ifndef SEEK_CUR
#define SEEK_CUR 1
#endif
#ifndef SEEK_END
#define SEEK_END 2
#endif

#if defined(__GNUC__) && !defined(C_ALLOCA)
# undef alloca
# define alloca __builtin_alloca
#else
# if defined(HAVE_ALLOCA_H) && !defined(C_ALLOCA)
#  include <alloca.h>
# else
#  ifndef alloca /* predefined by HP cc +Olibcalls */
#   if !defined (__STDC__) && !defined (__hpux)
char *alloca ();
#   else
void *alloca ();
#   endif /* __STDC__, __hpux */
#  endif /* alloca */
# endif /* HAVE_ALLOCA_H */
#endif

# define gettext(Msgid) (Msgid)
# define dgettext(Domainname, Msgid) (Msgid)
# define dcgettext(Domainname, Msgid, Category) (Msgid)
# define textdomain(Domainname) while (0) /* nothing */
# define bindtextdomain(Domainname, Dirname) while (0) /* nothing */
# define _(String) (String)
# define N_(String) (String)

/* bucomm.c */
void bfd_nonfatal
  PARAMS ((const char *));

void bfd_fatal
  PARAMS ((const char *)) ATTRIBUTE_NORETURN;

void report
  PARAMS ((const char *, va_list));

void fatal
  PARAMS ((const char *, ...)) ATTRIBUTE_PRINTF_1 ATTRIBUTE_NORETURN;

void non_fatal
  PARAMS ((const char *, ...)) ATTRIBUTE_PRINTF_1;

void set_default_bfd_target
  PARAMS ((void));

void list_matching_formats
  PARAMS ((char **));

void list_supported_targets
  PARAMS ((const char *, FILE *));

void list_supported_architectures
  PARAMS ((const char *, FILE *));

int display_info
  PARAMS ((void));
  
void print_arelt_descr
  PARAMS ((FILE *, bfd *, bfd_boolean));

char *make_tempname
  PARAMS ((char *));

bfd_vma parse_vma
  PARAMS ((const char *, const char *));

extern char *program_name;

/* filemode.c */
void mode_string
  PARAMS ((unsigned long, char *));

/* version.c */
extern void print_version
  PARAMS ((const char *));

/* rename.c */
extern void set_times
  PARAMS ((const char *, const struct stat *));

extern int smart_rename
  PARAMS ((const char *, const char *, int));

/* libiberty.  */
PTR xmalloc
  PARAMS ((size_t));

PTR xrealloc
  PARAMS ((PTR, size_t));

#endif /* _BUCOMM_H */
