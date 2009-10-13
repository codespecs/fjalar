include $(top_srcdir)/Makefile.tool.am

# PG - Build Fjalar with Kvasir (in the kvasir sub-directory)

## Build Fjalar at a higher optimisation level
# PG - don't do optimizations for the sake of debugging, instead add debugging info.
# Also disable the -Wmissing-prototypes warnings to prevent extra annoyances
#AM_CFLAGS_X86_LINUX   += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall

# AM_CFLAGS_X86_LINUX   := $(AM_CFLAGS_X86_LINUX: -O2=-O0) -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall -Wno-format -Wno-format-zero-length -Wno-pointer-sign -Wno-long-long
# AM_CFLAGS_AMD64_LINUX += -g -O0 -fno-omit-frame-pointer -Iinclude -W -Wall

EXTRA_CFLAGS =  -Iinclude -I../VEX/pub -I../include

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
	mc_main.c \
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

fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_SOURCES      = $(FJALAR_SOURCES_COMMON)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0) $(EXTRA_CFLAGS)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_PRI_CAPS@)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_PRI_CAPS@)
fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
if VGCONF_HAVE_PLATFORM_SEC
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_SOURCES      = $(FJALAR_SOURCES_COMMON)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0) $(EXTRA_CFLAGS)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_SEC_CAPS@)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_SEC_CAPS@)
fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
endif

mc_main.o: CFLAGS += -fomit-frame-pointer

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

VGPRELOAD_FJALAR_SOURCES_COMMON = mc_replace_strmem.c kvasir/dyncomp_wrappers.c

vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_SOURCES      = \
	$(VGPRELOAD_FJALAR_SOURCES_COMMON)
vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0)
vgpreload_fjalar_@VGCONF_ARCH_PRI@_@VGCONF_OS@_so_CFLAGS       = \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@: -O2=-O0) $(AM_CFLAGS_PIC: -O2=-O0) $(EXTRA_CFLAGS)
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
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@: -O2=-O0) $(AM_CFLAGS_PIC: -O2=-O0) $(EXTRA_CFLAGS)
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_DEPENDENCIES = \
	$(LIBREPLACEMALLOC_@VGCONF_PLATFORM_SEC_CAPS@)
vgpreload_fjalar_@VGCONF_ARCH_SEC@_@VGCONF_OS@_so_LDFLAGS      = \
	$(PRELOAD_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@) \
	$(LIBREPLACEMALLOC_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
endif

mc_replace_strmem.o: CFLAGS += -fno-omit-frame-pointer