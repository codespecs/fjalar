# Plan: reduce Fjalar's differences from Binutils' readelf code

Goal: make future Binutils upgrades (see `plan-upgrade-readelf.md`) cheaper by
shrinking Fjalar's diff against the pristine Binutils files.  Merge conflicts
happen where Fjalar's diff and upstream's diff touch nearby lines, so every
Fjalar-changed line that does not need to be in a vendored file is a future
conflict.

## Current state (against pristine 2.39)

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

"Changes" is the number of runs of consecutive changed lines.  "Conflicts"
is the number of conflicts in a merge of 2.47.  Whitespace differences were
already removed (#134).

The changed lines fall into these categories, roughly in decreasing order of
how cheaply they can be eliminated:

1. **libc -> Valgrind substitutions**: `malloc`/`free`/`strlen`/`strnlen`/
   `strcmp`/`strrchr`/`memset`/`memcpy` -> `VG_(...)`, `assert` ->
   `tl_assert`, `abort` -> `my_abort`.  About 140 one-line changes.
2. **Output suppression**: `printf`/`putchar` -> `FJALAR_DPRINTF` in
   `readelf.c` (about 65 lines); `if (fjalar_debug_dump)` inserted before
   `printf` in `dwarf.c` (about 120 lines); side-effecting arguments hoisted
   out of `printf` calls; an `ok_to_print` parameter threaded through
   `display_block`, `read_and_print_leb128`, `display_discr_list`, and
   `get_type_signedness`.
3. **Warning fixes**: `%d` -> `%u` and similar format changes (at least 24
   lines, from Valgrind's `-Wformat-signedness`), added casts, `const`, and
   `return 0;  // stop compiler warning` after `my_abort()`.
4. **Cosmetic edits**: spelling corrections (#75), commented-out code, the
   `entry` -> `ab_entry` rename, explanatory comment blocks.
5. **Include and configuration changes**: replacing `sysdep.h`/`libiberty.h`
   includes with Fjalar includes, `ngettext`/`PATH_MAX` definitions, the
   `startswith` and `BFD_VMA_FMT` workarounds for the system `bfd.h`, and the
   commented-out `#include "libiberty.h"` in three `include/` headers.
6. **Visibility changes**: `static` removed from functions that Fjalar calls
   (`slurp_rela_relocs`, `get_32bit_elf_symbols`, `get_TAG_name`, the
   `init_dwarf_regnames_*` functions, ...) and from the `do_*` flags, plus
   forward declarations to avoid `-Wmissing-prototypes`.
7. **Duplicated infrastructure**: `error`/`warn` reimplemented in each of
   `readelf.c`, `dwarf.c`, and `elfcomm.c` (and `report_leb_status` turned into
   a macro in `dwarf.h`); `xmalloc`/`xcalloc`/`xrealloc` defined in `dwarf.c`.
8. **Fjalar code appended to or replacing upstream code**:
   `fjalar_process_file` (about 200 lines at the end of `readelf.c`), a
   rewritten `display_debug_loc` with the original under `#if 0`, and a
   replaced loop in `process_section_contents`.
9. **`#if 0` blocks**: about 65 in each of `readelf.c` and `dwarf.c`, for code
   that Fjalar does not need, that targets other architectures, or that is
   guarded by a `do_*` flag that Fjalar never sets.
10. **Harvesting hooks and semantic changes**: calls into `typedata.c` and
    friends; the `entry`/`pass2`/`ok_to_harvest`/`ll` parameters threaded
    through `decode_location_expression`, `read_and_display_attr_value`, and
    `read_and_display_attr`; DWARF 5 restrictions; location-list and
    location-view handling.  These are Fjalar's reason for existing, but their
    footprint can shrink.

Some of category 3 and 4 is already gone upstream (for example, 2.47 fixes
"microprocesspr" and "formating", and no longer uses `BFD_VMA_FMT`), so the
2.47 merge resolves those changes by itself.

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
   files, so `git add` a newly vendored file (such as `ansidecl.h` in Phase 1)
   before measuring.  It takes a few seconds.  With NEWVER equal to the old
   version, it reports only the size of the changes.
2. `./compare-debug-output.sh DIR` compiles the C and C++ programs in
   `valgrind/fjalar/tests/` several ways, runs Fjalar with `--no-dyncomp` and
   `--decls-only` on each of them with no debugging option, with
   `--fjalar-debug-dump`, and with `--fjalar-debug`, and compares the
   output with a baseline that an earlier run saved.  Category 2 changes in
   particular must leave this output identical, and `./test-kvasir.sh` only
   checks the `.decls` and `.dtrace` output.  Running each configuration
   separately catches a `printf` that is now guarded by the wrong flag.

Verification for every later PR:

- `./compare-warnings.sh --binutils BEFORE.log AFTER.log` reports no new
  warnings, where the two logs are from full builds before and after the
  change.
- `./test-kvasir.sh` results are unchanged.
- `./compare-debug-output.sh DIR`, with a baseline saved in DIR before the
  change, shows no differences, except intended ones.  If it shows intended
  ones, check that it shows nothing else, then run
  `./compare-debug-output.sh --update DIR` to make the new output the
  baseline for the next PR.
- `./check-hook-counts.sh` reports no changes, or each one is explained (the
  script needs updating when hooks move; see Phase 3).
- CI passes on Ubuntu and Rocky Linux.

## Phase 1: shim headers and mechanical reverts (low risk, high payoff)

Status: done, in three stacked pull requests:  #226 (PR 2: steps 1 and
2), #227 (PR 3: step 3), and #228 (PR 4: steps 4 and 5).  It chose option 3
for `bfd.h`.  Lessons:

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

1. **Shim headers.**  Create `valgrind/fjalar/binutils-shim/` and put it
   before `include` on the `-I` path in `fjalar.am`.  It must not be under
   `valgrind/fjalar/include/`, because `merge-binutils.sh` treats every file
   there as a copy of a Binutils file and would merge upstream's version into
   it.  Add:
   - `sysdep.h`: includes `my_libc.h` and the `pub_tool_*.h` headers, defines
     `ngettext` and `PATH_MAX`, and maps libc functions to Valgrind ones with
     function-like macros (`#define strlen(s) VG_(strlen) (s)`,
     `#define malloc(n) VG_(malloc) (__FILE__, n)`, `assert` -> `tl_assert`,
     `abort` -> `my_abort`, ...).  Because `sysdep.h` is the first include of
     `readelf.c`, `dwarf.c`, and `elfcomm.c`, the macros are in effect when
     the system `bfd.h` is included, so its inline `startswith` uses
     `VG_(strncmp)`, and the `startswith` rename workaround can go.
   - Empty or minimal `libiberty.h`, `getopt.h`, `filenames.h`, and whatever
     else the upstream include lines need, so that those lines stay
     unchanged.
   - Possibly `assert.h`, so that `#include <assert.h>` stays unchanged.
     (`-I` directories are searched for `<...>` includes too.  No other
     Fjalar file includes `<assert.h>`.)
   - `bfd.h`, if the decision in "Replacing the system `bfd.h`" below is to
     use a minimal shim.
2. **Revert the libc substitutions** (category 1) and the include changes
   (category 5) in `readelf.c`, `dwarf.c`, `elfcomm.c`, `elfcomm.h`, and the
   three `include/` headers.
3. **One `error`/`warn`** (category 7); see "The duplicate `error`
   definition" below.  This needs only the shim, not the wrapper files of
   Phase 3.
4. **Warnings** (category 3).  Disable, in the shim, the warnings that only
   vendored code triggers, such as
   `#pragma GCC diagnostic ignored "-Wformat-signedness"`, and revert the
   warning-only edits.  Declare `my_abort` with `__attribute__((noreturn))` so
   the `return 0;` lines can go.  Check each format change before reverting
   it: a few are real fixes.  For example, `%*s` -> `%.*s` in the
   `DW_MACINFO_*` output fixes an upstream bug that 2.47 still has; keep that
   one (reporting it upstream is optional; see Phase 5).  Others change
   meaning, such as `dwarf_vmatoa ("d", adv)` -> `"u"`; examine those
   individually.
5. **Cosmetic reverts** (category 4).  Revert the #75 spelling corrections in
   vendored files (upstream has fixed some of them; the rest are harmless),
   delete commented-out code, and restore `include/elf/mips.h` to the
   pristine 2.39 version: its `unsigned long` fields are a pre-2.39 version
   of upstream's `uint32_t` fields, which a previous merge apparently failed
   to update.

### The duplicate `error` definition

Investigation results:

- Valgrind's core library defines a global `error` function, in
  `coregrind/m_gdbserver/utils.c`, which prints a message and then
  `longjmp`s to the gdbserver's top level.  `libcoregrind` is linked into
  every tool, so a global `error` in Fjalar would clash with it, or, worse,
  Fjalar would call the gdbserver's `error` by mistake.  That is why
  Fjalar's `elfcomm.c` makes upstream's `error` `static`, and why
  `readelf.c` and `dwarf.c` each define their own `static` `error` and
  `warn`.  (`nm` of a built `fjalar-amd64-linux` shows three local `error`
  symbols, two local `warn` symbols, and the gdbserver's global `error`.)
- With no global `error`, nothing declares it, so upstream's
  `static inline report_leb_status` in `dwarf.h` does not compile.
  `dwarf.h` is included not only by `dwarf.c` but also, through
  `fjalar_dwarf.h`, by Fjalar's own files.  Fjalar turned
  `report_leb_status` into a macro, so that `error` is looked up where the
  macro is used, in `dwarf.c`, where the `static` `error` is visible.  This
  is the "duplicate 'error' definition problem" that the comment mentions.
- The macro is also buggy.  It was copied from an older Binutils version, in
  which the messages started with `%s:%lu:` and were given a file name and a
  line number.  The macro keeps the `%s:%lu:` but passes no arguments, so if
  a LEB128 read in `read_and_print_leb128` runs off the end of the data or
  overflows, `error` reads two nonexistent arguments, which is undefined
  behavior and probably a crash.

Fix:

1. In the shim, rename the symbols with `#define error fjalar_binutils_error`
   and `#define warn fjalar_binutils_warn`.  Then nothing clashes with the
   gdbserver's `error`.
2. Make `fjalar_dwarf.h` include the shim (or a small header that contains
   only the renames) before `elfcomm.h` and `dwarf.h`, so that Fjalar's own
   files see the same names.
3. Use upstream's global `error` and `warn` in `elfcomm.c`, which work
   through `my_libc`'s `fprintf` and `vfprintf`.  Delete the copies in
   `readelf.c` and `dwarf.c`.  Restore upstream's declarations in
   `elfcomm.h` (vendor `include/aout/ar.h`, which the same `#if 0` block
   disables, or keep only that include disabled) and upstream's
   `report_leb_status` in `dwarf.h`.  This also fixes the macro's bug.
4. The messages change from `readelf.c: Error: ...` or `dwarf.c: Error: ...`
   to upstream's `fjalar: Error: ...` (`program_name` is `"fjalar"`).  Check
   that no test depends on the old prefix.

This removes about 70 changed lines from `readelf.c`, `dwarf.c`,
`elfcomm.c`, `elfcomm.h`, and `dwarf.h`.

### Replacing the system `bfd.h`

`readelf.c`, `dwarf.c`, and `elfcomm.c` include the system's `bfd.h` (from
the `binutils-dev` or `binutils-devel` package), and through it the system's
`ansidecl.h`, `symcat.h`, and `diagnostics.h`.  So 2.39 code is compiled
against whatever Binutils version the distribution has: 2.46 on Ubuntu 26.04,
and 2.41 on Rocky Linux 10, the oldest in CI.  That version skew is the
reason for the `startswith` rename (`bfd.h` gained `startswith` in 2.37), the
`BFD_VMA_FMT` definitions (`bfd.h` dropped it in 2.40), and #63.  It is also
the reason that `doc/valgrind-merge.texinfo` tells the merger to check every
`bfd.h` name that new code uses against the oldest `bfd.h` in CI.

The vendored files use very little of `bfd.h`: the types `bfd_vma`,
`bfd_signed_vma`, and `bfd_size_type`, `BFD_VMA_FMT`, `startswith`,
`ARRAY_SIZE`, and `ATTRIBUTE_*` (from `ansidecl.h`), plus a few `bfd_arch_*`
and `bfd_mach_*` names and functions in code that Fjalar disables.  2.47's
`readelf.c` and `dwarf.c` use even less: `bfd_vma` 3 times, `bfd_byte`
twice, and a few names in code that Fjalar disables.

The options:

1. **Keep using the system `bfd.h`** (the status quo).
   - Pro: no work, and no Fjalar-maintained replacement.
   - Con: every new distribution release can break the build (as in #63),
     and every merge must check new `bfd.h` uses against the oldest `bfd.h`
     in CI.  Users and CI images need `binutils-dev`.  The workarounds stay
     in the vendored files.
2. **Vendor the full `bfd.h` of the same Binutils version.**
   - Pro: the header matches the vendored code, so there is no skew, and
     upstream code compiles unchanged.  No `binutils-dev` dependency.
   - Con: `bfd.h` is generated (from `bfd/bfd-in2.h` by `configure`, which
     substitutes host-specific values such as `BFD_HOST_64BIT_LONG`), so
     `merge-binutils.sh` cannot 3-way merge it.  Each upgrade must regenerate
     it, for example from the build tree of `build-binutils-readelf.sh`, and
     the generated values describe a 64-bit host, which may be wrong for a
     32-bit secondary-platform build.  It is about 8000 lines for a handful of
     types, and it includes more headers (`symcat.h`, `diagnostics.h`) that
     would need vendoring too.
3. **A minimal Fjalar-owned `bfd.h` in `binutils-shim/`** (recommended),
   which shadows the system one because the shim directory comes first on
   the `-I` path.  It defines only what the vendored files use (the types,
   `BFD_VMA_FMT` while the code is 2.39, `startswith` with `VG_()`
   functions, and the few `bfd_architecture` names that `dwarf.h` mentions).
   Also vendor the real `include/ansidecl.h` into `valgrind/fjalar/include/`,
   where `merge-binutils.sh` merges it automatically; the 2.47 trial merge
   already lists it as needed.
   - Pro: no skew and no `binutils-dev` dependency, about 50 lines, no
     generated file, and the `startswith`, `BFD_VMA_FMT`, and #63
     workarounds leave the vendored files.  2.47 needs even less of it.
   - Con: Fjalar maintains it by hand.  When new upstream code uses a `bfd.h`
     name that the shim lacks, compilation fails and someone adds the name;
     but that failure is immediate and obvious, unlike the current failures,
     which appear only on some distributions.

With option 2 or 3, remove the `binutils-dev` instructions from
`doc/valgrind-merge.texinfo` and `README`, the `bfd.h` version report from
`.github/workflows/ci.yml`, and the "Newer `bfd.h` definitions" hint.

## Phase 2: output suppression without editing each `printf` (medium risk)

In the shim, redirect every standard-output function that the vendored files
call (`printf`, `putchar`, `fputs` to `stdout`, ...) to a function, for
example:

```c
#define printf(...) fjalar_binutils_printf (FJALAR_BINUTILS_PRINTING, __VA_ARGS__)
```

The function prints only if its first argument is true.  Because it is a
function rather than a guarded statement, it evaluates its arguments
whether or not it prints, so side effects inside upstream `printf` arguments
happen as upstream intends, and no hoisting is needed.
`FJALAR_BINUTILS_PRINTING` is `fjalar_debug` for `readelf.c` and a global
flag for `dwarf.c` that is `fjalar_debug_dump && pass2` within
`process_debug_info` and `fjalar_debug_dump` elsewhere.  `process_debug_info`
sets the flag for each pass and restores its previous value on return,
because callers such as `display_debug_aranges` call `load_debug_info`, which
can run the first pass, and then print.

This removes the `FJALAR_DPRINTF` substitutions, the `if (fjalar_debug_dump)`
guards, the hoisted arguments, the `ok_to_print` parameters, and the existing
local `#define printf` trick in `dwarf.c` (about 300 changed lines).

It also prevents output that a guard misses.  For example, `display_loc_list`
in `dwarf.c` printed "[without DW_AT_frame_base]" and "(start == end)" (with
`printf` and `fputs`) without any debugging option, for some optimized
programs (fixed in #187).

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

1. **Wrapper translation units.**  Compile `fjalar_readelf.c`, which
   `#include`s `readelf.c`, instead of compiling `readelf.c` directly; do the
   same for `dwarf.c` and `elfcomm.c`.  Edit `FJALAR_SOURCES_COMMON` in
   `fjalar.am` (not `Makefile.am`, which is regenerated).  Code before the
   `#include` (declarations, helpers) and after it (definitions that need the
   file's statics) lives in a Fjalar-owned file.  Then:
   - Restore `static` on every function and flag (category 6); the wrapper
     defines extern accessors or setters after the `#include`.  This also
     removes the forward declarations that exist only for
     `-Wmissing-prototypes`, and the `dwarf.h` declarations of
     `init_dwarf_regnames_i386` and friends.
   - Restore upstream's `do_*` declarations; the "never true for Fjalar"
     comments move into the setter.
   - Move `fjalar_process_file` and the other appended Fjalar code to the
     wrapper.
   - Move `xmalloc`/`xcalloc`/`xrealloc` to the wrapper or to `my_libc.c`, and
     remove the `xcalloc` declaration added to `bucomm.h` if it is then
     unneeded.
2. **Replaced functions** (category 8).  Give Fjalar's `display_debug_loc`
   and the replaced `process_section_contents` loop their own names, in the
   wrapper, and change only the reference to them (the `debug_displays`
   table entry, or the call site).  The upstream versions stay unchanged and
   unused, instead of under a large `#if 0`.
3. **Compact hooks** (category 10).  Make each hook a single line that
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
4. **Parameter threading** (category 10).  Consider replacing the `entry`,
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
runs, and newly compiled code may need more shim macros or `my_libc`
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

Update "Hints to modifying dwarf.c and readelf.c" in
`doc/valgrind-merge.texinfo`, and the comment at the top of the shim
`sysdep.h`:

- Do not edit a vendored file to fix a warning; disable the warning in the
  shim.
- Do not replace a libc call or `printf`; the shim handles them.
- Put Fjalar logic in the wrapper or in a Fjalar file; a hook in a vendored
  file is a single line that calls a helper.
- Prefer leaving upstream code compiled-but-unused to disabling it.

Also update `plan-upgrade-readelf.md`: several of its conflict-resolution
instructions (replace libc calls with `VG_(...)`, guard every new `printf`,
hoist side-effecting arguments) become unnecessary.

## Order and expected payoff

| PR | Content                                               | Risk   | Lines saved |
| -- | ----------------------------------------------------- | ------ | ----------: |
| 1  | Phase 0 tools (done: #185, #188)                      | none   |           0 |
| 2  | Shim headers (incl. `bfd.h`), libc reverts (#226)     | low    |         220 |
| 3  | One `error`/`warn` (fixes the LEB message bug) (#227) | low    |          70 |
| 4  | Warning and cosmetic reverts (#228)                   | low    |          80 |
| 5  | `printf` redirection                                  | medium |         300 |
| 6  | Wrapper translation units                             | medium |         330 |
| 7  | Replaced functions, compact hooks                     | medium |         200 |
| 8  | `#if 0` blocks, parameter threading                   | higher |           ? |

"Lines saved" is a rough estimate of the changed lines that each PR removes
from the diff; together they are about half of Fjalar's current diff.  Re-run
the trial merge after each PR and record the conflict counts here.  Then do
the 2.47 upgrade.

Trial merges of 2.47 (`./merge-binutils.sh --trial 2.47`), cumulative:

| After      | Changes | Added | Removed | Conflicts |
| ---------- | ------: | ----: | ------: | --------: |
| (baseline) |     713 |  2212 |     535 |       191 |
| PR 2       |     570 |  1956 |     361 |       174 |
| PR 3       |     560 |  1876 |     357 |       172 |
| PR 4       |     509 |  1799 |     283 |       160 |
