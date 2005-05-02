#include $(top_srcdir)/Makefile.tool.am

# PG - Manually include only the parts that I want from Makefile.tool.am
#      because I don't want to include any sub-directories

SUBDIRS = .

include $(top_srcdir)/Makefile.all.am
include $(top_srcdir)/Makefile.tool-flags.am
include $(top_srcdir)/Makefile.tool-inplace.am

## Build Memcheck at a higher optimisation level
# PG - don't do optimizations for the sake of debugging, instead add debugging info.
# Also disable the -Wmissing-prototypes warnings to prevent extra annoyances
AM_CFLAGS += -g -fno-omit-frame-pointer -Iinclude -Wno-missing-prototypes
#AM_CFLAGS += -O2

# PG - Change the name of the shared library
val_PROGRAMS = vgtool_kvasir.so vgpreload_kvasir.so

vgpreload_kvasir_so_SOURCES = \
	mac_replace_strmem.c
vgpreload_kvasir_so_DEPENDENCIES = $(top_builddir)/coregrind/lib_replace_malloc.a
vgpreload_kvasir_so_LDFLAGS = -shared -Wl,-z,interpose,-z,initfirst \
	-Wl,--whole-archive \
	$(top_builddir)/coregrind/lib_replace_malloc.a \
	-Wl,--no-whole-archive

vgtool_kvasir_so_SOURCES = \
	mac_leakcheck.c \
	mac_malloc_wrappers.c \
	mac_needs.c \
	mc_errcontext.c \
	mc_main.c \
	mc_translate.c \
	union_find.c \
	dyncomp_main.c \
	dyncomp_translate.c \
	kvasir_main.c \
	generate_daikon_data.c \
	kvasir_runtime.c \
	decls-output.c \
	dtrace-output.c \
	GenericHashtable.c \
	disambig.c \
	readelf.c \
	typedata.c

vgtool_kvasir_so_LDFLAGS = -shared

mcincludedir = $(includedir)/valgrind

mcinclude_HEADERS = \
	memcheck.h

noinst_HEADERS =	\
	mac_shared.h	\
	mc_asm.h	\
	mc_include.h	\
	mc_translate.h

mac_replace_strmem.o: CFLAGS += -fno-omit-frame-pointer
