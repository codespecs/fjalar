include $(top_srcdir)/Makefile.tool.am

# PG - Build Fjalar with Kvasir (in the kvasir sub-directory)

## Build Fjalar at a higher optimisation level
# PG - don't do optimizations for the sake of debugging, instead add debugging info.
# Also disable the -Wmissing-prototypes warnings to prevent extra annoyances
AM_CFLAGS_X86_LINUX   += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall
AM_CFLAGS_AMD64_LINUX += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall

SUBDIRS +=

noinst_PROGRAMS = 
noinst_DSYMS = 
if VGCONF_PLATFORMS_INCLUDE_X86_LINUX
noinst_PROGRAMS += fjalar-x86-linux vgpreload_fjalar-x86-linux.so
endif
if VGCONF_PLATFORMS_INCLUDE_AMD64_LINUX
noinst_PROGRAMS += fjalar-amd64-linux vgpreload_fjalar-amd64-linux.so
if VGCONF_PLATFORMS_INCLUDE_X86_DARWIN
noinst_PROGRAMS += fjalar-x86-darwin vgpreload_fjalar-x86-darwin.so
noinst_DSYMS    +=                   vgpreload_fjalar-x86-darwin.so
endif
if VGCONF_PLATFORMS_INCLUDE_AMD64_DARWIN
noinst_PROGRAMS += fjalar-amd64-darwin vgpreload_fjalar-amd64-darwin.so
noinst_DSYMS    +=                       vgpreload_fjalar-amd64-darwin.so
endif
  
endif
# PG - no PPC


VGPRELOAD_FJALAR_SOURCES_COMMON = mc_replace_strmem.c kvasir/dyncomp_wrappers.c

vgpreload_fjalar_x86_linux_so_SOURCES      = $(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_x86_linux_so_CPPFLAGS     = $(AM_CPPFLAGS_X86_LINUX)
vgpreload_fjalar_x86_linux_so_CFLAGS       = $(AM_CFLAGS_X86_LINUX) $(AM_CFLAGS_PIC)
vgpreload_fjalar_x86_linux_so_CCASFLAGS    = $(AM_CCASFLAGS_X86_LINUX)
vgpreload_fjalar_x86_linux_so_DEPENDENCIES = $(LIBREPLACEMALLOC_X86_LINUX)
vgpreload_fjalar_x86_linux_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_X86_LINUX) \
	$(LIBREPLACEMALLOC_LDFLAGS_X86_LINUX)

vgpreload_fjalar_amd64_linux_so_SOURCES      = $(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_amd64_linux_so_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_LINUX)
vgpreload_fjalar_amd64_linux_so_CFLAGS       = $(AM_CFLAGS_AMD64_LINUX) $(AM_CFLAGS_PIC)
vgpreload_fjalar_amd64_linux_so_CCASFLAGS    = $(AM_CCASFLAGS_AMD64_LINUX)
vgpreload_fjalar_amd64_linux_so_DEPENDENCIES = $(LIBREPLACEMALLOC_AMD64_LINUX)
vgpreload_fjalar_amd64_linux_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_AMD64_LINUX) \
	$(LIBREPLACEMALLOC_LDFLAGS_AMD64_LINUX)

vgpreload_fjalar_x86_darwin_so_SOURCES      = $(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_x86_darwin_so_CPPFLAGS     = $(AM_CPPFLAGS_X86_DARWIN)
vgpreload_fjalar_x86_darwin_so_CFLAGS       = $(AM_CFLAGS_X86_DARWIN) $(AM_CFLAGS_PIC)
vgpreload_fjalar_x86_darwin_so_CCASFLAGS    = $(AM_CCASFLAGS_X86_DARWIN)
vgpreload_fjalar_x86_darwin_so_DEPENDENCIES = $(LIBREPLACEMALLOC_X86_DARWIN)
vgpreload_fjalar_x86_darwin_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_X86_DARWIN) \
	$(LIBREPLACEMALLOC_LDFLAGS_X86_DARWIN)

vgpreload_fjalar_amd64_darwin_so_SOURCES      = $(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_amd64_darwin_so_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_DARWIN)
vgpreload_fjalar_amd64_darwin_so_CFLAGS       = $(AM_CFLAGS_AMD64_DARWIN) $(AM_CFLAGS_PIC)
vgpreload_fjalar_amd64_darwin_so_CCASFLAGS    = $(AM_CCASFLAGS_AMD64_DARWIN)
vgpreload_fjalar_amd64_darwin_so_DEPENDENCIES = $(LIBREPLACEMALLOC_AMD64_DARWIN)
vgpreload_fjalar_amd64_darwin_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_AMD64_DARWIN) \
	$(LIBREPLACEMALLOC_LDFLAGS_AMD64_DARWIN)


FJALAR_SOURCES_COMMON = \
	mc_leakcheck.c \
	mc_malloc_wrappers.c \
	mc_main.c \
	mc_translate.c \
	mc_machine.c \
	mc_errors.c \
	fjalar_main.c \
	fjalar_runtime.c \
	fjalar_select.c \
	generate_fjalar_entries.c \
	GenericHashtable.c \
	fjalar_traversal.c \
	readelf.c \
	typedata.c \
	disambig.c \
	my_libc.c \
	tsearch.c \
	kvasir/kvasir_main.c \
	kvasir/decls-output.c \
	kvasir/dtrace-output.c \
	kvasir/union_find.c \
	kvasir/dyncomp_main.c \
	kvasir/dyncomp_runtime.c \
	kvasir/dyncomp_translate.c

fjalar_x86_linux_SOURCES      = $(FJALAR_SOURCES_COMMON)
fjalar_x86_linux_CPPFLAGS     = $(AM_CPPFLAGS_X86_LINUX)
fjalar_x86_linux_CFLAGS       = $(AM_CFLAGS_X86_LINUX) 
fjalar_x86_linux_CCASFLAGS    = $(AM_CCASFLAGS_X86_LINUX)
fjalar_x86_linux_DEPENDENCIES = $(COREGRIND_LIBS_X86_LINUX)
fjalar_x86_linux_LDADD        = $(TOOL_LDADD_X86_LINUX)
fjalar_x86_linux_LDFLAGS      = $(TOOL_LDFLAGS_X86_LINUX)

fjalar_amd64_linux_SOURCES      = $(FJALAR_SOURCES_COMMON)
fjalar_amd64_linux_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_LINUX)
fjalar_amd64_linux_CFLAGS       = $(AM_CFLAGS_AMD64_LINUX)
fjalar_amd64_linux_CCASFLAGS    = $(AM_CCASFLAGS_AMD64_LINUX)
fjalar_amd64_linux_DEPENDENCIES = $(COREGRIND_LIBS_AMD64_LINUX)
fjalar_amd64_linux_LDADD        = $(TOOL_LDADD_AMD64_LINUX)
fjalar_amd64_linux_LDFLAGS      = $(TOOL_LDFLAGS_AMD64_LINUX)

memcheck_x86_darwin_SOURCES      = $(MEMCHECK_SOURCES_COMMON)
memcheck_x86_darwin_CPPFLAGS     = $(AM_CPPFLAGS_X86_DARWIN)
memcheck_x86_darwin_CFLAGS       = $(AM_CFLAGS_X86_DARWIN) -O2
memcheck_x86_darwin_CCASFLAGS    = $(AM_CCASFLAGS_X86_DARWIN)
memcheck_x86_darwin_DEPENDENCIES = $(COREGRIND_LIBS_X86_DARWIN)
memcheck_x86_darwin_LDADD        = $(TOOL_LDADD_X86_DARWIN)
memcheck_x86_darwin_LDFLAGS      = $(TOOL_LDFLAGS_X86_DARWIN)

memcheck_amd64_darwin_SOURCES      = $(MEMCHECK_SOURCES_COMMON)
memcheck_amd64_darwin_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_DARWIN)
memcheck_amd64_darwin_CFLAGS       = $(AM_CFLAGS_AMD64_DARWIN) -O2
memcheck_amd64_darwin_CCASFLAGS    = $(AM_CCASFLAGS_AMD64_DARWIN)
memcheck_amd64_darwin_DEPENDENCIES = $(COREGRIND_LIBS_AMD64_DARWIN)
memcheck_amd64_darwin_LDADD        = $(TOOL_LDADD_AMD64_DARWIN)
memcheck_amd64_darwin_LDFLAGS      = $(TOOL_LDFLAGS_AMD64_DARWIN)

mcincludedir = $(includedir)/valgrind

mcinclude_HEADERS = \
	memcheck.h

noinst_HEADERS =	\
	mc_include.h

mc_replace_strmem.o: CFLAGS = -fno-omit-frame-pointer

mc_main.o: CFLAGS += -fomit-frame-pointer
