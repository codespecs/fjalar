/*
  This file is part of DynComp, a dynamic comparability analysis tool
  for C/C++ based upon the Valgrind binary instrumentation framework
  and the Valgrind MemCheck tool (Copyright (C) 2000-2009 Julian
  Seward, jseward@acm.org)

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   MIT CSAIL Program Analysis Group

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.
*/

/* vgpreloaded wrapper functions used to modify dyncomp's
   behavior. These run on the guest CPU, so they need to use client
   requests if they want to modify DynComp's behavior beyond what
   regular code can do. */

#include "pub_tool_clreq.h"

/* Return a word-sized value with the same value as the argument, but
   a different tag, via loopholes in DynComp's checking. Perhaps this
   is excessively clever, but adding a client request would be a
   pain. -SMcC */
static long tag_launder_long(long x) {
    unsigned long y = 0;
    unsigned i;
    for (i = 0; i < 8*sizeof(long); i++) {
	if (x & (1UL << i))
	    y |= 1UL << i;
    }
    return (long)y;
}

/* glibc's __libc_start_main does something like "foo = argv[argc +
   1]", but it's unintuitive for argc and argv to always be
   comparable, so hide this by tag laundring. This computation is done
   to determine the value of the environment pointer passed by the
   kernel, but versions of glibc differ in whether the value is
   assigned to environ in a dynamically linked libc (environ was
   actually already set up by the dynamic linker, so it's somewhat
   superfluous).
   Note that argc and argv will often still end up comparable if the
   program actually looks at its arguments, since it's common to index
   argv by a value derived from argc. */
int I_WRAP_SONAME_FNNAME_ZU(NONE, main)(int argc, char **argv, char **env);
int I_WRAP_SONAME_FNNAME_ZU(NONE, main)(int argc, char **argv, char **env) {
    OrigFn fn;
    int result;
    VALGRIND_GET_ORIG_FN(fn);
    argc = tag_launder_long(argc);
    argv = (char **)tag_launder_long((long)argv);
    env = (char **)tag_launder_long((long)env);
    CALL_FN_W_WWW(result, fn, argc, argv, env);
    return result;
}

/* For ostream operators that do integer->ASCII conversion, make a
   fresh tag for the argument so that interactions caused by having a
   single digit lookup table don't cause every value printed to be
   considered as interacting. */

/* std::basic_ostream<char, std::char_traits<char> >::operator<<(int) */
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEi)
                             (void *this_ptr, int arg);
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEi)
                             (void *this_ptr, int arg) {
    OrigFn fn;
    void *result;
    VALGRIND_GET_ORIG_FN(fn);
    arg = tag_launder_long(arg);
    CALL_FN_W_WW(result, fn, this_ptr, arg);
    return result;
}

/* std::basic_ostream<...>::operator<<(unsigned int) */
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEj)
                             (void *this_ptr, unsigned int arg);
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEj)
                             (void *this_ptr, unsigned int arg) {
    OrigFn fn;
    void *result;
    VALGRIND_GET_ORIG_FN(fn);
    arg = tag_launder_long(arg);
    CALL_FN_W_WW(result, fn, this_ptr, arg);
    return result;
}

/* std::basic_ostream<char, std::char_traits<char> >::operator<<(long) */
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEl)
                             (void *this_ptr, long arg);
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEl)
                             (void *this_ptr, long arg) {
    OrigFn fn;
    void *result;
    VALGRIND_GET_ORIG_FN(fn);
    arg = tag_launder_long(arg);
    CALL_FN_W_WW(result, fn, this_ptr, arg);
    return result;
}

/* std::basic_ostream<...>::operator<<(unsigned long) */
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEm)
                             (void *this_ptr, unsigned long arg);
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEm)
                             (void *this_ptr, unsigned long arg) {
    OrigFn fn;
    void *result;
    VALGRIND_GET_ORIG_FN(fn);
    arg = tag_launder_long(arg);
    CALL_FN_W_WW(result, fn, this_ptr, arg);
    return result;
}

/* std::basic_ostream<char, std::char_traits<char> >::operator<<(short) */
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEs)
                             (void *this_ptr, short arg);
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEs)
                             (void *this_ptr, short arg) {
    OrigFn fn;
    void *result;
    VALGRIND_GET_ORIG_FN(fn);
    arg = tag_launder_long(arg);
    CALL_FN_W_WW(result, fn, this_ptr, arg);
    return result;
}

/* std::basic_ostream<...>::operator<<(unsigned short) */
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEt)
                             (void *this_ptr, unsigned short arg);
void *I_WRAP_SONAME_FNNAME_ZU(libstdcZpZpZa, _ZNSolsEt)
                             (void *this_ptr, unsigned short arg) {
    OrigFn fn;
    void *result;
    VALGRIND_GET_ORIG_FN(fn);
    arg = tag_launder_long(arg);
    CALL_FN_W_WW(result, fn, this_ptr, arg);
    return result;
}

// (comment added 2006)  
/* XXX Should support float, double, long double, and long long too,
   but I'm not confident how to pass them through CALL_FN safely, nor
   be 64-bit clean. */
