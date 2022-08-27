##
#  This file is part of Fjalar, a dynamic analysis framework for C/C++
#  programs.
#
#  Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
#  Programming Languages and Software Engineering Group
#
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License as
#  published by the Free Software Foundation; either version 2 of the
#  License, or (at your option) any later version.
##

include $(top_srcdir)/Makefile.tool.am

#Fjalar has no 'tests' subdir
SUBDIRS = .

# PG - Build Fjalar with Kvasir (in the kvasir sub-directory)

## Build Fjalar at a higher optimisation level
# PG - don't do optimizations for the sake of debugging, instead add debugging info.
# Also disable the -Wmissing-prototypes warnings to prevent extra annoyances

#AM_CFLAGS_X86_LINUX   += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall
#AM_CFLAGS_X86_LINUX   := $(AM_CFLAGS_X86_LINUX: -O2=-O0) -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall -Wno-format -Wno-format-zero-length -Wno-pointer-sign -Wno-long-long

# AM_CFLAGS_AMD64_LINUX += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall

# get all binutil .h files from include; get config.h from .. (markro)
EXTRA_CFLAGS =  -Iinclude -I../VEX/pub -I../include -I..

# for debugging versions
#EXTRA_CFLAGS +=  -O0 -finstrument-functions
EXTRA_CFLAGS +=  -O0

# Compile fjalar without -Wcast-qual
CFLAGS   += -Wno-cast-qual
CXXFLAGS += -Wno-cast-qual

# Compile fjalar without --fno-common (gcc version 10 default)
CFLAGS   += -fcommon
CXXFLAGS += -fcommon

#----------------------------------------------------------------------------
# Headers
#----------------------------------------------------------------------------

pkginclude_HEADERS = \
	memcheck.h

noinst_HEADERS = \
	mc_include.h

#----------------------------------------------------------------------------
# fjalar-<platform>
#----------------------------------------------------------------------------

noinst_PROGRAMS  = fjalar-@VGCONF_ARCH_PRI@-@VGCONF_OS@
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += fjalar-@VGCONF_ARCH_SEC@-@VGCONF_OS@
endif

FJALAR_SOURCES_COMMON = \
	mc_leakcheck.c \
	mc_malloc_wrappers.c \
	mc_main.c mc_main_asm.c \
	mc_translate.c \
	mc_machine.c \
	mc_errors.c \
	fjalar_dwarf.c \
	fjalar_main.c \
	fjalar_runtime.c \
	fjalar_select.c \
	generate_fjalar_entries.c \
	GenericHashtable.c \
	fjalar_traversal.c \
	readelf.c \
	dwarf.c \
	libiberty/dwarfnames.c \
	elfcomm.c \
	typedata.c \
	disambig.c \
	my_libc.c \
	my_libc_float.c \
	tsearch.c \
	kvasir/kvasir_main.c \
	kvasir/decls-output.c \
	kvasir/dtrace-output.c \
	kvasir/union_find.c \
	kvasir/dyncomp_main.c \
	kvasir/dyncomp_runtime.c \
	kvasir/dyncomp_translate.c

fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_SOURCES      = \
    $(FJALAR_SOURCES_COMMON)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS       =   $(LTO_CFLAGS) \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0) $(EXTRA_CFLAGS)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_PRI_CAPS@)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_PRI_CAPS@)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_PRI@ \
	$(LINK) \
	$(fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS) \
	$(fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS)

if VGCONF_HAVE_PLATFORM_SEC
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_SOURCES      = \
    $(FJALAR_SOURCES_COMMON)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS       = $(LTO_CFLAGS) \
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0) $(EXTRA_CFLAGS)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_SEC_CAPS@)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_SEC_CAPS@)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_SEC@ \
	$(LINK) \
	$(fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS) \
	$(fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS)
endif

#----------------------------------------------------------------------------
# vgpreload_fjalar-<platform>.so
#----------------------------------------------------------------------------



noinst_PROGRAMS += vgpreload_fjalar-@VGCONF_ARCH_PRI@-@VGCONF_OS@.so
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += vgpreload_fjalar-@VGCONF_ARCH_SEC@-@VGCONF_OS@.so
endif

if VGCONF_OS_IS_DARWIN
noinst_DSYMS = $(noinst_PROGRAMS)
endif

# mc_replace_strmem.c runs on the simulated CPU, and is built with
# AM_CFLAGS_PSO_* (see $(top_srcdir)/Makefile.all.am).
VGPRELOAD_FJALAR_SOURCES_COMMON = mc_replace_strmem.c kvasir/dyncomp_wrappers.c

vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_SOURCES      = \
	$(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0)
vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_CFLAGS       = \
	$(AM_CFLAGS_PSO_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0) $(EXTRA_CFLAGS)
vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_DEPENDENCIES = \
	$(LIBREPLACEMALLOC_@VGCONF_PLATFORM_PRI_CAPS@)
vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@) \
	$(LIBREPLACEMALLOC_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)

if VGCONF_HAVE_PLATFORM_SEC
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_SOURCES      = \
	$(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0)
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_CFLAGS       = \
	$(AM_CFLAGS_PSO_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0) $(EXTRA_CFLAGS)
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_DEPENDENCIES = \
	$(LIBREPLACEMALLOC_@VGCONF_PLATFORM_SEC_CAPS@)
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@) \
	$(LIBREPLACEMALLOC_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
endif

