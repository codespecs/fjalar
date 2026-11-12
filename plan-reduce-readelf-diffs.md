# Plan: reduce Fjalar's differences from Binutils' readelf code

Goal: make future Binutils upgrades (see `plan-upgrade-readelf.md`) cheaper by
shrinking Fjalar's diff against the pristine Binutils files.  Merge conflicts
happen where Fjalar's diff and upstream's diff touch nearby lines, so every
Fjalar-changed line that does not need to be in a vendored file is a future
conflict.

## Current state (against pristine 2.39)

Output of `./merge-binutils.sh --trial 2.47` on 2026-11-11, at `265fd112`
(after Phase 1):

| File        | Changes | Added | Removed | Conflicts |
| ----------- | ------: | ----: | ------: | --------: |
| `dwarf.c`   |     347 |  1163 |     171 |       112 |
| `readelf.c` |     153 |   610 |     110 |        45 |
| `elfcomm.c` |       3 |    17 |       0 |         0 |
| `elfcomm.h` |       2 |     4 |       0 |         0 |
| `dwarf.h`   |       1 |     3 |       0 |         1 |
| `bucomm.h`  |       1 |     2 |       0 |         1 |
| total       |     507 |  1799 |     281 |       159 |

"Changes" is the number of runs of consecutive changed lines.  "Conflicts"
is the number of conflicts in a merge of 2.47.  The `include/` files no
longer differ from pristine 2.39.

### Baseline (before Phase 1)

Output of `./merge-binutils.sh --trial 2.47` on 2026-10-25, at `b7cb6ced`:

| File                 | Changes | Added | Removed | Conflicts |
| -------------------- | ------: | ----: | ------: | --------: |
| `dwarf.c`            |     418 |  1331 |     292 |       128 |
| `readelf.c`          |     260 |   791 |     222 |        59 |
| `elfcomm.c`          |      13 |    38 |       8 |         1 |
| `dwarf.h`            |       5 |    23 |       0 |         1 |
| `elfcomm.h`          |       4 |    15 |       1 |         1 |
| `bucomm.h`           |       1 |     2 |       0 |         1 |
| `include/` (4 files) |      12 |    12 |      12 |         0 |
| total                |     713 |  2212 |     535 |       191 |

Whitespace differences were already removed (#134).

### Categories of changes

The baseline's changed lines fell into these categories, roughly in
decreasing order of how cheaply they can be eliminated.  Phase 1 removed
categories 1 and 5 and most of 3, 4, and 7; each category says what
remains.

1. **libc -> Valgrind substitutions**: `malloc`/`free`/`strlen`/`strnlen`/
   `strcmp`/`strrchr`/`memset`/`memcpy` -> `VG_(...)`, `assert` ->
   `tl_assert`, `abort` -> `my_abort`.  About 140 one-line changes.
   Removed by Phase 1.
2. **Output suppression**: `printf`/`putchar` -> `FJALAR_DPRINTF` in
   `readelf.c` (89 lines); `if (fjalar_debug_dump)` inserted before
   `printf` in `dwarf.c` (122 lines); side-effecting arguments hoisted
   out of `printf` calls; an `ok_to_print` parameter threaded through
   `display_block`, `read_and_print_leb128`, `display_discr_list`, and
   `get_type_signedness`.  Phase 2 removes this category.
3. **Warning fixes**: `%d` -> `%u` and similar format changes (at least 24
   lines, from Valgrind's `-Wformat-signedness`), added casts, `const`, and
   `return 0;  // stop compiler warning` after `my_abort()`.  Phase 1
   removed most of them; the real fixes and the format changes in lines
   that Phase 2 changes remain.
4. **Cosmetic edits**: spelling corrections (#75), commented-out code, the
   `entry` -> `ab_entry` rename, explanatory comment blocks.  Phase 1
   removed the spelling corrections and some of the commented-out code.  The rename
   remains, because it avoids shadowing Fjalar's `entry` parameter (category
   10), and the comment blocks remain until Phase 3 moves them.
5. **Include and configuration changes**: replacing `sysdep.h`/`libiberty.h`
   includes with Fjalar includes, `ngettext`/`PATH_MAX` definitions, the
   `startswith` and `BFD_VMA_FMT` workarounds for the system `bfd.h`, and the
   commented-out `#include "libiberty.h"` in three `include/` headers.
   Removed by Phase 1, except the `PTR` definition in `dwarf.c`, which only
   Fjalar's `xmalloc` and its relatives use (category 7).
6. **Visibility changes**: `static` removed from functions that Fjalar calls
   (`slurp_rela_relocs`, `get_32bit_elf_symbols`, `get_TAG_name`, the
   `init_dwarf_regnames_*` functions, ...) and from the `do_*` flags, plus
   forward declarations to avoid `-Wmissing-prototypes`.
7. **Duplicated infrastructure**: `error`/`warn` reimplemented in each of
   `readelf.c`, `dwarf.c`, and `elfcomm.c` (and `report_leb_status` turned into
   a macro in `dwarf.h`); `xmalloc`/`xcalloc`/`xrealloc` defined in `dwarf.c`.
   Phase 1 removed the `error`/`warn` copies; `xmalloc` and its relatives
   remain.
8. **Fjalar code appended to or replacing upstream code**:
   `fjalar_process_file` (about 200 lines at the end of `readelf.c`), a
   rewritten `display_debug_loc` with the original under `#if 0`, and a
   replaced loop in `process_section_contents`.
9. **`#if 0` blocks**: 36 in `readelf.c` and 31 in `dwarf.c`, for code that
   Fjalar does not need, that targets other architectures, or that is
   guarded by a `do_*` flag that Fjalar never sets.  `elfcomm.c` and
   `elfcomm.h` each have one, around the archive code.
10. **Harvesting hooks and semantic changes**: calls into `typedata.c` and
    friends; the `entry`/`pass2`/`ok_to_harvest`/`ll` parameters threaded
    through `decode_location_expression`, `read_and_display_attr_value`, and
    `read_and_display_attr`; DWARF 5 restrictions; location-list and
    location-view handling.  These are Fjalar's reason for existing, but their
    footprint can shrink.

Some of category 3 and 4 is already gone upstream (for example, 2.47 fixes
"microprocesspr" and "formating", and no longer uses `BFD_VMA_FMT`), so the
2.47 merge resolves those changes by itself.

Some changes stay on purpose.  The Fjalar copyright notices at the top of
`readelf.c`, `dwarf.c`, and `elfcomm.c` record that Fjalar modified those
files, which section 2(a) of the GPL version 2 requires; do not remove them
to shrink the diff.

## Strategy

Do all the reductions before the 2.47 upgrade, as a series of small PRs
against the current 2.39-based code.  Each PR is a refactoring that is
verifiable on its own, whereas merge conflicts can only be verified all
together.  Each PR preserves behavior, except for any output change that it
intends and its description states, such as PR 3's fix of the LEB128
messages (see "Order and expected payoff").  Each PR also lowers the
conflict count of the 2.47 merge and of every later merge.

Measure after each PR.  The trial-merge numbers decide only how far to take
Phase 4 and the parameter-threading step of Phase 3, not whether to do the
other phases.

## Phase 0: measurement and verification tools

Status: done.  Both tools have landed, in #188 and #185.

1. `./merge-binutils.sh --trial NEWVER` reports the size of Fjalar's changes
   to the old version (as in the table above) and the number of conflicts
   that a merge of NEWVER would have, per file.  It merges in memory with
   `git merge-tree`, so it changes neither the work tree nor any ref, and it
   measures uncommitted changes to tracked files too.  It ignores untracked
   files, so `git add` a newly vendored file before measuring.  It takes a
   few seconds.  With NEWVER equal to the old version, it reports only the
   size of the changes.
2. `./compare-debug-output.sh DIR` compiles the C and C++ programs in
   `valgrind/fjalar/tests/` several ways, runs Fjalar with `--no-dyncomp` and
   `--decls-only` on each of them with no debugging option, with
   `--fjalar-debug-dump`, and with `--fjalar-debug`, and compares the
   output with a baseline that an earlier run saved.  Category 2 changes in
   particular must leave this output identical, and `./test-kvasir.sh` only
   checks the `.decls` and `.dtrace` output.  Running each configuration
   separately catches a `printf` that is now guarded by the wrong flag.

Verification for every later PR:

- `./compare-warnings.sh --binutils BEFORE.log AFTER.log` and
  `./compare-warnings.sh BEFORE.log AFTER.log` report no new warnings, where
  the two logs are from full builds before and after the change.  (The
  `--binutils` run alone misses some warnings; see Phase 1.)
- `./test-kvasir.sh` results are unchanged.
- `./compare-debug-output.sh DIR`, with a baseline saved in DIR before the
  change, shows no differences, except intended ones.  If it shows intended
  ones, check that it shows nothing else, then run
  `./compare-debug-output.sh --update DIR` to make the new output the
  baseline for the next PR.
- `./check-hook-counts.sh` reports no changes, or each one is explained (the
  script needs updating when hooks move; see Phase 3).
- CI passes on Ubuntu and Rocky Linux.

## Phase 1: shim headers and mechanical reverts

Status: done, in three stacked pull requests:  #226 (PR 2), #227 (PR 3),
and #228 (PR 4).

- **Shim headers** (#226).  `valgrind/fjalar/binutils-shim/` precedes
  `include` on the `-I` path in `fjalar.am`.  It is not under
  `valgrind/fjalar/include/`, because `merge-binutils.sh` treats every file
  there as a copy of a Binutils file and would merge upstream's version into
  it.  Its `sysdep.h`, the first include of `readelf.c`, `dwarf.c`, and
  `elfcomm.c`, includes `my_libc.h` and the `pub_tool_*.h` headers, defines
  `ngettext`, and maps each libc function that the vendored files call to its
  Valgrind equivalent with a function-like macro (`#define strlen(s)
  VG_(strlen) (s)`, `abort` -> `my_abort`, ...).  Its `assert.h` maps
  `assert` to `tl_assert`.  Its `bfd.h` replaces the system one (see "The
  shim `bfd.h`" below).  Its `filenames.h`, `getopt.h`, `libiberty.h`, and
  `wchar.h` let the upstream include lines stay unchanged.  `ansidecl.h` is
  vendored into `valgrind/fjalar/include/`, where `merge-binutils.sh` merges
  it.  With the shim in place, #226 reverted the libc substitutions
  (category 1) and the include changes (category 5).
- **One `error`/`warn`** (#227).  Valgrind's core library defines a global
  `error` function, in `coregrind/m_gdbserver/utils.c`, which prints a
  message and then `longjmp`s to the gdbserver's top level, and
  `libcoregrind` is linked into every tool.  So `fjalar.am` renames
  upstream's `error` with `-Derror=fjalar_binutils_error` in
  `BINUTILS_SHIM_CFLAGS`, which applies to every file, unlike a `#define` in
  a header.  `readelf.c` and `dwarf.c` use `elfcomm.c`'s `error` and `warn`,
  and `dwarf.h` has upstream's `report_leb_status` again; `fjalar_dwarf.h`
  includes `my_libc.h` before `dwarf.h`, because `report_leb_status` uses `_`
  and `error`.  That fixed a bug in Fjalar's `report_leb_status` macro,
  which kept an old `%s:%lu:` message prefix but passed no arguments for it.
  The messages start with `fjalar: Error:` instead of `readelf.c: Error:` or
  `dwarf.c: Error:`.
- **Warning and cosmetic reverts** (#228).  The vendored files are compiled
  with the warnings that only they trigger disabled, `my_abort` is declared
  `noreturn`, and the warning-only edits, the #75 spelling corrections, and
  some commented-out code are reverted.  `include/elf/mips.h` is the pristine
  2.39 version again.  Real fixes stay, such as `%*s` -> `%.*s` in the
  `DW_MACINFO_*` output, which fixes an upstream bug that 2.47 still has
  (reporting it upstream is optional; see Phase 5).

Lessons:

- GCC's `#pragma GCC diagnostic ignored "-Wformat-signedness"` has no
  effect; only `-Wformat` can be ignored, which would disable all format
  checking.  So `fjalar.am` adds `-Wno-format-signedness` to the vendored
  object files, with GNU make target-specific variables.  The shim
  disables `-Wdiscarded-qualifiers` and `-Wunused-variable` with pragmas.
- Upstream's `error` and `warn` are declared `ATTRIBUTE_PRINTF_1`, so PR 3
  turns on format checking of all their calls.  That found one real bug,
  a Fjalar `%lu` -> `%u` change, and showed that another Fjalar format
  change (in `SAFE_BYTE_GET`) was wrong.
- `compare-warnings.sh --binutils` misses a warning whose location is a
  macro defined in a non-Binutils header, such as `_` in `my_libc.h`.
  Run it without `--binutils` too.
- The system `<wchar.h>` conflicts with `my_libc.h`, and `<sys/stat.h>`
  conflicts with Valgrind's `vki` headers if it is included first, so the
  shim has its own `wchar.h`, and its `bfd.h` declares `struct stat`
  instead of including `<sys/stat.h>`.
- `dwarf.h` has no include guard, so `fjalar_dwarf.h` includes it only when
  the shim `sysdep.h` has not been included.
- PR 3 shifts the heap addresses in the `--fjalar-debug` output by 0x1000,
  so `compare-debug-output.sh` reports differences there that are not
  behavior changes.
- PR 4 does not revert a format change in a line that Phase 2 also changes
  (a `printf` that became `FJALAR_DPRINTF`), nor the `entry` -> `ab_entry`
  rename, which avoids shadowing Fjalar's `entry` parameter (Phase 3).

### The shim `bfd.h`

The vendored files included the system's `bfd.h` (from the `binutils-dev`
or `binutils-devel` package), and through it the system's `ansidecl.h`,
`symcat.h`, and `diagnostics.h`.  So 2.39 code was compiled against whatever
Binutils version the distribution has: 2.46 on Ubuntu 26.04, and 2.41 on
Rocky Linux 10, the oldest in CI.  That version skew caused the `startswith`
rename (`bfd.h` gained `startswith` in 2.37), the `BFD_VMA_FMT` definitions
(`bfd.h` dropped it in 2.40), and #63, and every merge had to check each
`bfd.h` name that new code uses against the oldest `bfd.h` in CI.

The shim `bfd.h` is Fjalar-owned and about 50 lines.  It defines only what
the vendored files use: the types `bfd_vma`, `bfd_signed_vma`,
`bfd_size_type`, and `bfd_byte`, `BFD_VMA_FMT` while the code is 2.39,
`startswith`, and the few `bfd_architecture` names that `dwarf.h` mentions.
Fjalar maintains it by hand: when new upstream code uses a `bfd.h` name that
the shim lacks, compilation fails on every platform, and someone adds the
name.

The alternative of vendoring the full `bfd.h` was rejected.  `bfd.h` is
generated (from `bfd/bfd-in2.h` by `configure`, which substitutes
host-specific values such as `BFD_HOST_64BIT_LONG`), so `merge-binutils.sh`
cannot 3-way merge it, and the generated values describe one host.  It is
about 8000 lines for a handful of types, and it includes more headers that
would need vendoring too.

## Phase 2: output suppression without editing each `printf` (medium risk)

In the shim, redirect every standard-output function that the vendored files
call to a function.  For example:

```c
#define printf(...) fjalar_binutils_printf (FJALAR_BINUTILS_PRINTING, __VA_ARGS__)
```

The functions to redirect are `printf`, `putchar`, `putc`, `fputc`, `fputs`,
and `fprintf`.  `my_libc.h` defines `putchar(c)` as `fputc(c,stdout)` and
`putc(c,stream)` as `fputc(c,stream)`, so redirecting `fputc` covers both
macros; a shim that redefines either one must `#undef` it first.
`readelf.c` passes `stdout` to `fputs` (103 times), `fputc` (12), `putc` (6),
and `fprintf` (4), and `error` and `warn` in `elfcomm.c` pass `stderr`, so
the replacements of the functions that take a stream compare it with
`stdout` at run time and pass any other stream through unchanged.

The function prints only if its first argument is true.  Because it is a
function rather than a guarded statement, it evaluates its arguments
whether or not it prints, so side effects inside upstream `printf` arguments
happen as upstream intends, and no hoisting is needed.

`FJALAR_BINUTILS_PRINTING` differs per file, but all three files include the
same shim `sysdep.h`.  So `fjalar.am` defines it per object file with GNU make
target-specific variables, as it adds `-Wno-format-signedness`, and
`sysdep.h` reports an error if it is undefined:

- For `readelf.c`, it is `fjalar_debug`.
- For `dwarf.c`, it is a global flag that is `fjalar_debug_dump && pass2`
  within `process_debug_info` and `fjalar_debug_dump` elsewhere.
  `process_debug_info` sets the flag for each pass and restores its previous
  value on return, because callers such as `display_debug_aranges` call
  `load_debug_info`, which can run the first pass, and then print.  Every
  call of `read_and_display_attr_value` outside `process_debug_info` passes
  `PASS_2`, so `fjalar_debug_dump` is the right value there.
- For `elfcomm.c`, it is `fjalar_debug`.  Its only `printf` is in the archive
  code, which Fjalar disables (category 9).

This removes the `FJALAR_DPRINTF` substitutions, the `if (fjalar_debug_dump)`
guards, the `if (fjalar_debug_dump && pass2)` guards in
`read_and_display_attr`, the hoisted arguments, the `ok_to_print`
parameters, and the existing local `#define printf` trick in `dwarf.c`
(about 300 changed lines).

It also removes two related edits in `process_debug_info`.  Fjalar added
`|| (!fjalar_debug_dump)` to the test that sets `do_printing`, and it passes
`do_loc` to `read_and_display_attr` instead of upstream's
`do_loc || ! do_printing`, so that a DIE is harvested even when it is not
printed.  Fjalar never sets `dwarf_start_die` or `dwarf_cutoff_level`, so
without the added test `do_printing` is always true, and upstream's
argument equals `do_loc`.  Then `do_printing` guards only output, which the
redirection already suppresses, and both lines can be upstream's again.

The redirection also prevents output that a guard misses.  For example,
`display_loc_list` in `dwarf.c` printed "[without DW_AT_frame_base]" and
"(start == end)" (with `printf` and `fputs`) without any debugging option,
for some optimized programs (fixed in #187).

Risks and checks:

- Performance: arguments such as `dwarf_vmatoa (...)` are now evaluated even
  when not printing.  Measure Fjalar's startup time on a large binary.  If it
  is too slow, use a macro that skips evaluating the arguments, and keep the
  existing hoists only where arguments have side effects.
- An argument that is unsafe to evaluate in Fjalar's configuration (for
  example, it reads data that Fjalar did not load).  The Kvasir tests and the
  debug-dump comparison would show a crash or a difference.
- `-Wshadow` is on, so a file-scope flag cannot be shadowed by a local of the
  same name; use distinct names.

## Phase 3: move Fjalar code out of vendored files (medium risk, high payoff)

1. **`readelf.c`'s flags.**  Restore upstream's `static bool ... = false;`
   declarations of the `do_*` flags, `show_name`, and `check_all`, which
   Fjalar made non-`static` `int`s with comments such as "never true for
   Fjalar", and
   change `do_syms++` in `fjalar_process_file` to `do_syms = true;`.  No file
   other than `readelf.c` refers to these flags, so this step needs neither
   a wrapper (step 2) nor setters, and it can be done before the rest of the
   phase.  Upstream's own flags in `dwarf.c` (`do_debug_info`, ...) are
   declared in `dwarf.h` and need no change.
2. **Wrapper translation units.**  Compile `fjalar_readelf.c`, which
   `#include`s `readelf.c`, instead of compiling `readelf.c` directly; do the
   same for `dwarf.c` and `elfcomm.c`.  Edit `FJALAR_SOURCES_COMMON` in
   `fjalar.am` (not `Makefile.am`, which is regenerated).  Code before the
   `#include` (declarations, helpers) and after it (definitions that need the
   file's statics) lives in a Fjalar-owned file.  Then:
   - Restore `static` on every function (category 6).  Code in the wrapper
     is in the same translation unit as the vendored file, so it can call
     the `static` functions and set the `static` variables directly.  Only a
     function that another Fjalar file (such as `typedata.c` or
     `fjalar_main.c`) calls needs an extern accessor, which the wrapper
     defines after the `#include`.  This also removes the forward
     declarations that exist only for `-Wmissing-prototypes`, and the
     `dwarf.h` declarations of `init_dwarf_regnames_i386` and friends.
   - Move `fjalar_process_file` and the other appended Fjalar code to the
     wrapper.
   - Move `xmalloc`/`xcalloc`/`xrealloc` to the wrapper or to `my_libc.c`,
     with `void *` instead of `PTR`, and remove the `PTR` definition from
     `dwarf.c`.  Remove the `xcalloc` declaration added to `bucomm.h` if it
     is then unneeded.
3. **Replaced functions** (category 8).  Give Fjalar's `display_debug_loc`
   and the replaced `process_section_contents` loop their own names, in the
   wrapper, and change only the reference to them (the `debug_displays`
   table entry, or the call site).  The upstream versions stay unchanged and
   unused, instead of under a large `#if 0`.
4. **Compact hooks** (category 10).  Make each hook a single line that
   calls a helper defined in a Fjalar file, and keep the explanatory comments
   with the helper.  For example:
   - The 4 identical 8-line `harvest_debug_frame_entry` blocks after the
     `DW_CFA_advance_loc*` cases become one call each.
   - The 5 `genputtable` blocks (with their commented-out debug `printf`s)
     become one call each, such as
     `fjalar_record_line_row (&state_machine_regs);`.
   - `if (ok_to_harvest) harvest_x (entry, ...);` becomes one line.
   Never edit an upstream line to add a hook; put the hook on its own line.
   Update `check-hook-counts.sh` to count the new helper calls.
5. **Parameter threading** (category 10).  Consider replacing the `entry`,
   `pass2`, `ok_to_harvest`, and `ll` parameters, which change the signatures
   of 3 functions and about 15 call sites (many of them in code that never
   harvests, which passes `PASS_2, DO_NOT_HARVEST, 0, 0`), with file-scope
   state that `process_debug_info` and `display_loc_list` set.  The one
   recursive call that must not harvest (`DW_OP_entry_value`) saves and
   restores the state.  Upstream's own code uses file-scope state this way.
   This is the riskiest change in the plan; do it last, and only if the trial
   merge shows that these signatures and call sites cause conflicts.

## Phase 4: `#if 0` blocks (evaluate by the trial-merge numbers)

Each `#if 0` block adds two boundary lines, which conflict when upstream edits
near them.  After Phase 1, much of the disabled code compiles unchanged.

- Remove the `#if 0` around code that compiles and links with the shim:
  other architectures' tables and decoders, and code guarded by a `do_*` flag
  that Fjalar never sets (`do_sections`, `do_header`, `do_version`,
  `do_unwind`, `do_arch`, ...).  Suppress `-Wunused-function` in the shim.
  Measure the size increase of the Fjalar binary.
- Keep code disabled where it needs something Fjalar lacks: CTF, SFrame, the
  demangler, archive handling, debuginfod, `main`/`usage`/option parsing.
- Where several `#if 0` blocks are adjacent with only unneeded code between
  them, merge them into one.

Do this phase only to the extent that the trial merge shows the boundaries
cause conflicts.  Removing a block means linking in code that Fjalar never
runs, and newly compiled code might need more shim macros or `my_libc`
functions.

## Phase 5: related improvements

- **Report to Binutils (optional; the user's choice).**  Some of Fjalar's
  changes fix upstream bugs, such as `%*s` -> `%.*s` in the `DW_MACINFO_*`
  output and the remaining spelling errors.  Each one that upstream accepts
  disappears from Fjalar's diff at the next merge.  Reporting them is
  outward-facing, so it is not part of the plan's required work.
- **Prevent regressions.**  Add a CI job, or a check in
  `merge-binutils.sh --trial`, that reports the size of the diff against
  pristine Binutils, so that a growth is noticed in review.

## Phase 6: document the conventions

"Hints to modifying dwarf.c and readelf.c" in `doc/valgrind-merge.texinfo`
and `plan-upgrade-readelf.md` already say not to edit a vendored file to fix
a warning and not to replace a libc call.  After Phases 2 and 3, add the
remaining conventions to those hints and to the comment at the top of the
shim `sysdep.h`:

- Do not guard or replace a `printf` or other output call; the shim
  handles them, and their arguments are evaluated as upstream intends.
- Put Fjalar logic in the wrapper or in a Fjalar file; a hook in a vendored
  file is a single line that calls a helper.
- Prefer leaving upstream code compiled-but-unused to disabling it.

Also remove the texinfo hints' discussion of guarding `printf` calls and
hoisting their arguments, and the corresponding conflict-resolution
instruction in `plan-upgrade-readelf.md` ("Guard every new
`printf`/`putchar` ...; hoist side-effecting arguments").

## Order and expected payoff

| PR | Content                                               | Risk   | Estimate | Actual |
| -- | ----------------------------------------------------- | ------ | -------: | -----: |
| 1  | Phase 0 tools (done: #185, #188)                      | none   |        0 |      0 |
| 2  | Shim headers (incl. `bfd.h`), libc reverts (#226)     | low    |      220 |    430 |
| 3  | One `error`/`warn` (fixes the LEB message bug) (#227) | low    |       70 |     84 |
| 4  | Warning and cosmetic reverts (#228)                   | low    |       80 |    151 |
| 5  | `readelf.c`'s flags `static` again (Phase 3 step 1)   | low    |       25 |        |
| 6  | `printf` redirection                                  | medium |      300 |        |
| 7  | Wrapper translation units                             | medium |      330 |        |
| 8  | Replaced functions, compact hooks                     | medium |      200 |        |
| 9  | `#if 0` blocks, parameter threading                   | higher |        ? |        |

"Estimate" is a rough estimate of the changed lines that each PR removes
from the diff, counting a line that Fjalar replaced as one line; together
they are about half of Fjalar's baseline diff.  "Actual" is the decrease in
the number of added plus removed lines that the trial merge reports, which
counts a replaced line twice (once added, once removed), so it runs up to
twice the estimate.  Re-run the trial merge after each PR and record the
results here.  Then do the 2.47 upgrade.

Trial merges of 2.47 (`./merge-binutils.sh --trial 2.47`), cumulative:

| After               | Changes | Added | Removed | Conflicts |
| ------------------- | ------: | ----: | ------: | --------: |
| (baseline)          |     713 |  2212 |     535 |       191 |
| PR 2                |     570 |  1956 |     361 |       174 |
| PR 3                |     560 |  1876 |     357 |       172 |
| PR 4                |     509 |  1799 |     283 |       160 |
| master (`265fd112`) |     507 |  1799 |     281 |       159 |
