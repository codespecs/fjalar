include $(top_srcdir)/Makefile.tool.am

# PG - Build Fjalar with Kvasir (in the kvasir sub-directory)

## Build Memcheck at a higher optimisation level
# PG - don't do optimizations for the sake of debugging, instead add debugging info.
# Also disable the -Wmissing-prototypes warnings to prevent extra annoyances
AM_CFLAGS_X86_LINUX   += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall
AM_CFLAGS_AMD64_LINUX += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall

noinst_PROGRAMS =
if VGP_X86_LINUX
noinst_PROGRAMS += fjalar-x86-linux vgpreload_fjalar-x86-linux.so
endif
if VGP_AMD64_LINUX
noinst_PROGRAMS += fjalar-amd64-linux vgpreload_fjalar-amd64-linux.so
endif
# PPC not supported yet

VGPRELOAD_FJALAR_SOURCES_COMMON = mac_replace_strmem.c kvasir/dyncomp_wrappers.c

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


FJALAR_SOURCES_COMMON = \
	mac_leakcheck.c \
	mac_malloc_wrappers.c \
	mc_main.c \
	mac_shared.c \
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

mcincludedir = $(includedir)/valgrind

mcinclude_HEADERS = \
	memcheck.h

noinst_HEADERS =	\
	mac_shared.h	\
	mc_include.h

mac_replace_strmem.o: CFLAGS += -fno-omit-frame-pointer

mc_main.o: CFLAGS += -fomit-frame-pointer
