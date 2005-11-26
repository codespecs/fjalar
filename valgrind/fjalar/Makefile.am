#include $(top_srcdir)/Makefile.tool.am

# PG - Build Fjalar with Kvasir (in the kvasir sub-directory)

SUBDIRS = .

include $(top_srcdir)/Makefile.all.am
include $(top_srcdir)/Makefile.tool-flags.am
include $(top_srcdir)/Makefile.tool-inplace.am

## Build Memcheck at a higher optimisation level
# PG - don't do optimizations for the sake of debugging, instead add debugging info.
# Also disable the -Wmissing-prototypes warnings to prevent extra annoyances
AM_CFLAGS += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall -Wno-missing-prototypes

# Use this for speed boost
#AM_CFLAGS += -O3 -fomit-frame-pointer -Iinclude -Wno-missing-prototypes

# PG - Change the name of the shared library
val_PROGRAMS = vgtool_fjalar.so vgpreload_fjalar.so

vgpreload_fjalar_so_SOURCES = \
	mac_replace_strmem.c
vgpreload_fjalar_so_DEPENDENCIES = $(top_builddir)/coregrind/lib_replace_malloc.a
vgpreload_fjalar_so_LDFLAGS = -shared -Wl,-z,interpose,-z,initfirst \
	-Wl,--whole-archive \
	$(top_builddir)/coregrind/lib_replace_malloc.a \
	-Wl,--no-whole-archive

vgtool_fjalar_so_SOURCES = \
	mac_leakcheck.c \
	mac_malloc_wrappers.c \
	mac_needs.c \
	mc_errcontext.c \
	mc_main.c \
	mc_translate.c \
	fjalar_main.c \
	fjalar_runtime.c \
	fjalar_select.c \
	generate_fjalar_entries.c \
	GenericHashtable.c \
	fjalar_traversal.c \
	readelf.c \
	typedata.c \
	disambig.c \
	kvasir/kvasir_main.c \
	kvasir/decls-output.c

vgtool_fjalar_so_LDFLAGS = -shared

mcincludedir = $(includedir)/valgrind

mcinclude_HEADERS = \
	memcheck.h

noinst_HEADERS =	\
	mac_shared.h	\
	mc_asm.h	\
	mc_include.h	\
	mc_translate.h

mac_replace_strmem.o: CFLAGS += -fno-omit-frame-pointer
