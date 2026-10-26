# Plan: reduce Fjalar's differences from its version of Valgrind

The goal is to make the next Valgrind merges (`merge-valgrind.sh`, see
`doc/valgrind-merge.texinfo` and `plan-upgrade-valgrind.md`) produce fewer
conflicts and fewer silently lost changes.  Every line in which Fjalar's
copy of an upstream file differs from upstream is a potential conflict and
an item that `compare-fjalar-changes.sh` reports and that a person must
check.  This plan reduces the differences between Fjalar and the Valgrind
version that Fjalar is based on, **3.23.0** (`valgrind/REVISION`), not the
latest Valgrind.

## Ordering

Do this work before the 3.23.0 -> 3.27.1 upgrade (`plan-upgrade-valgrind.md`).
Every difference removed here is one fewer conflict to resolve in that
merge.  This work is independent of the Binutils/readelf upgrade
(`plan-upgrade-readelf.md`), except that both touch the build and the
warning baseline, so do not run the two at the same time.

## Status

| Step | Pull request | State |
| --- | --- | --- |
| Version string in `configure.ac` (not a numbered step) | #181 | Landed |
| Step 0 | — | Not started; the CI whitespace check of Step 2 waits for it |
| Step 1 | #182 | Landed |
| Step 2 | #183 | Landed, without the CI check |
| Step 3 | #184 | Open |
| Steps 4-9 | — | Not started |

PR #184 also fixes 2 bugs that the commented-out lines it deletes had hidden
(`MC_(instrument)` leaked `dce.tmpMap`, and Fjalar rejected Memcheck's
malloc-replacement options such as `--alignment`), and it rewords Fjalar's
header block in the 9 Memcheck copies that carry one.

## How the differences were measured

The base tree is the one that `merge-valgrind.sh` builds as
`refs/valgrind-merge/base`:  upstream `VALGRIND_3_23_0` at `valgrind/`,
plus upstream `memcheck/` (without `docs/`, `tests/`, and `Makefile.am`) at
`valgrind/fjalar/`.  The diff is
`git diff --diff-filter=a <base> HEAD -- valgrind`, which omits the files
that only Fjalar has (Fjalar's own sources and Binutils-derived files).
Measured at commit 821648e0:

| Part | Files | Lines added | Lines removed | Same, ignoring whitespace (`-w`) |
| --- | ---: | ---: | ---: | --- |
| All | 43 | 3590 | 1334 | +2827 / -571 |
| Memcheck copies in `valgrind/fjalar/` | 10 | 1493 | 1022 | +997 / -526 |
| `valgrind/memcheck/tests/` | 4 | 1387 | 4 | +1387 / -4 |
| Everything else (Coregrind, VEX, include, build, tests) | 29 | 710 | 308 | +443 / -41 |

The largest differences, by kind:

- **Accidental file-type and mode changes (about 1390 lines).**  4 files
  that are symbolic links upstream are regular files in Fjalar
  (`memcheck/tests/{amd64,x86}/pcmpgt.cpp`,
  `memcheck/tests/linux/strlcat_strlcpy.{c,stderr.exp}`); 3 files have an
  extra execute bit; `valgrind/.clang-format` and
  `valgrind/.git-blame-ignore-revs` are missing.
- **Whitespace (about 1530 lines).**  Trailing whitespace was stripped and
  tabs were changed to spaces, mostly in `guest_x86_helpers.c`,
  `libvex_ir.h`, `scheduler.c`, `mc_translate.c`, and `mc_main.c`.  No tool
  in the repository prevents this; editors do it on save.
- **Variable renames in `mc_main.c` (331 lines).**  `line` -> `ocline`,
  `str` -> `fstr`/`astr`, made in 892545f9 (2016) to silence shadowing
  warnings caused by a readelf merge.
- **`VG_(printf)` -> `printf` in Memcheck copies (181 lines).**
  `printf` is Fjalar's `my_libc` function, which writes unbuffered to file
  descriptor 1 (standard output); `VG_(printf)` writes to Valgrind's log
  (standard error, unless `--log-fd` or `--log-file` says otherwise).  All
  of these calls are in panic, debugging, and IR-tracing code.
- **`complainIfUndefined` calls commented out (77 lines in
  `mc_translate.c`).**
- **Fjalar copyright headers added to Memcheck copies (69 lines).**
- **`#ifndef _NO_DYNCOMP` wrappers (72 lines).**  `_NO_DYNCOMP` is never
  defined.
- **Code moved out of upstream files.**  About 200 lines of type
  definitions, inline functions, and macros were moved from
  `mc_translate.c` to the Fjalar file `mc_translate.h`, so upstream changes
  to them can never merge automatically.
- **Register accessors in Coregrind (about 240 lines** in `m_machine.c`,
  `pub_tool_machine.h`, `pub_core_machine.h`) and **guest-layout fields in
  VEX (about 140 lines** in `libvex.h`, `guest_amd64_helpers.c`,
  `guest_x86_helpers.c`).
- **Genuine DynComp/Fjalar hooks**:  the extra shadow area, DynComp calls in
  `MC_(instrument)` and in the `make_mem_*` functions, `CHECK_SP` calls,
  and the Fjalar entry points in `mc_main.c`.

## Principles

1. Prefer, in order:  no change to the upstream file; Fjalar code in a
   Fjalar-owned file; a minimal hook (ideally one line, adjacent to as
   little upstream text as possible) in the upstream file.
2. In upstream files, keep upstream's text byte for byte, including
   whitespace, names, comments, copyright years, and typos.  Send fixes of
   upstream bugs or typos upstream instead.
3. Fjalar supports only amd64-linux (#121), but keep the functionality of
   its x86-only changes.  Where a step replaces an amd64 change by Fjalar
   code, replace the corresponding x86 change the same way, so that x86
   keeps working (untested, as now).  Do not keep PPC-only Fjalar changes.
4. Each step is behavior-preserving, except where the step says otherwise
   (Step 4 moves some debugging messages from standard output to
   Valgrind's log, as upstream does).  Verify each PR with `make build`,
   `./check-regtest.sh`, `make fjalar-test`, and `./test-kvasir.sh`
   (output identical to the output before the PR).  Also compare compiler
   warnings:  save the log of a full build (after `make very-clean`) before
   the PR and after it, and run
   `./compare-warnings.sh BEFORE.log AFTER.log`.
5. Do the mechanical, low-risk steps first:  they shrink the diff the
   most, and they make the remaining changes easy to see.

## Steps

### Step 0: a script that measures the differences

Not started.

Add `diff-from-valgrind.sh [GIT-DIFF-OPTION...]`, which builds the base
tree from `$INV/valgrind-old` exactly as `merge-valgrind.sh`'s
`upstream_commit` does (factor that function into a shared file, as
`binutils-common.sh` does for the Binutils scripts) and runs
`git diff --diff-filter=a <base> HEAD -- valgrind` with the given options
(for example, `--stat` or `-w`).  Record the diffstat in each PR
description below, so that reviewers see the reduction.

### Step 1: restore file types, modes, and missing files (PR 1)

Landed as #182.

- `./list-file-discrepancies.sh $INV/valgrind-old` lists all of them.
- Replace the 4 regular files by upstream's symbolic links, remove the 3
  extra execute bits, and restore `valgrind/.clang-format` and
  `valgrind/.git-blame-ignore-revs`.
- Check that `.gitignore` does not ignore the restored files, so that they
  stay tracked.

Removes about 1400 lines.  Risk: none (the files are upstream test inputs
and editor configuration).

### Step 2: restore upstream whitespace (PR 2)

Landed as #183, with the `.editorconfig` but without the CI check,
which needs Step 0's script.

For each upstream file that differs from the base:

```sh
git diff -w --diff-filter=a <base> HEAD -- FILE > FILE.patch
git show <base>:FILE > FILE
git apply --ignore-whitespace FILE.patch
```

Write `FILE.patch` in a scratch directory, not in the work tree.  Then
check that `git diff -w HEAD` is empty (no change other than whitespace)
and that `diff-from-valgrind.sh` and `diff-from-valgrind.sh -w` report the
same line counts.  Fjalar's own added lines keep their whitespace.

`git diff -w` cannot show a whitespace change that matters, so an empty
result does not prove that the step changed nothing that matters.  Review
`git diff HEAD` by hand for the whitespace that is significant:  tabs at
the start of recipe lines in `Makefile.am` files, and whitespace inside
string and character literals.  Then build.

To keep the whitespace from drifting again:

- Add a CI check, using `diff-from-valgrind.sh`, that fails if the diff of
  an upstream file changes when whitespace is ignored.  It needs a shallow
  clone of `VALGRIND_3_23_0`, which takes a few seconds.  This check is
  the real guard.
- Add a top-level `.editorconfig` that sets
  `trim_trailing_whitespace = false` for `valgrind/**` and turns it back on
  for Fjalar's own directories (`valgrind/fjalar/kvasir/**` and others).
  It helps only with editors that honor `.editorconfig` (for Emacs, the
  `editorconfig` package), so it reduces drift but does not prevent it.

Removes about 1530 lines.  Risk:  low, given the review of significant
whitespace described above.

### Step 3: revert cosmetic edits (PR 3)

Open as #184.

None of these changes behavior, except as noted:

- Typo fixes in upstream comments (`pub_tool_libcfile.h`, `memcheck.h`),
  the `apt` command lines in `docs/README`, and the blank lines of
  `Makefile.am`.
- Merge damage:  the copyright years that went backward
  (`mc_replace_strmem.c`, `mc_machine.c`), the misplaced `VSR51`..`VSR63`
  block and ACC comment in `mc_machine.c`, and
  "This file is part of" -> "This file is derived from".
- Commented-out `DEBUG` calls, `// (comment added 2009)`-style comments,
  and the commented-out `ppIRSB`, `LibVEX_Alloc`, and `VG_(printf)` lines.
  (The `if (verboze)` blocks that Fjalar added to `MC_(instrument)` are not
  dead code:  they print the IR trace.)
- `-j $(nproc)` in `auxprogs/Makefile.am` is not purely cosmetic:  in a
  Makefile, `$(nproc)` is an undefined variable, so upstream's recipe runs
  `make -j` with no job limit, and Fjalar's removal of it avoided that.
  Restore it anyway, because only `make auxchecks` uses the rule and
  Fjalar never runs that target.
- In `host_generic_reg_alloc2.c`, upstream's
  `} /* switch (vreg_lrs[j].reg_class) */`, inside whose comment Fjalar
  added a `{`.

### Step 4: revert unneeded source changes in the Memcheck copies (PR 4)

- **`printf` -> `VG_(printf)`** (181 lines) in all Memcheck copies.  Then
  remove `#include "my_libc.h"` from each file that no longer needs it.
  This is not purely mechanical:  the messages move from standard output
  to Valgrind's log, as in upstream.  That is an improvement, because the
  IR tracing in `mc_translate.c` mixes these messages with `ppIRStmt` and
  `ppIRExpr` output, which already goes to the log, so today the two halves
  of a trace line can go to different streams.  None of the messages
  appears in a normal run, so the Kvasir tests are unaffected; check that
  the IR trace (`--fjalar-debug --fjalar-print-ir`) reads correctly.
  After this change and Step 3, `mc_machine.c` differs from upstream only
  in Fjalar's copyright header.
- **Variable renames** (331 lines).  Restore upstream's `line` and `str`.
  Compare full-build logs with `./compare-warnings.sh` (see Principle 4)
  to check whether a shadowing warning reappears.  If it does, rename the Fjalar global that is shadowed, or stop
  including its header in `mc_main.c`, rather than renaming Memcheck's
  locals.
- **`DEBUG`**:  restore upstream's definition
  (`#define DEBUG(fmt, args...) //VG_(printf)(fmt, ## args)`) and upstream's
  `DEBUG` format arguments, and remove Fjalar's added `DEBUG` calls.  If
  someone uses `MAX_DEBUG_INFO` tracing of Memcheck, keep only the
  definition change (one hunk).
- **`#ifndef _NO_DYNCOMP`**:  `_NO_DYNCOMP` is never defined, so remove
  these wrappers from the Memcheck copies (72 lines).
- **`memcheck.h`**:  check whether `#include "valgrind.h"` works with
  Fjalar's include path; if so, revert to it.
- **Copyright headers**:  remove Fjalar's copyright header from every
  Memcheck copy that, without it, is identical to upstream, so that the
  merge never conflicts in that file.  After Steps 3 and 4, these should
  be `mc_errors.c`, `mc_malloc_wrappers.c`, `mc_leakcheck.c`,
  `mc_replace_strmem.c`, `mc_machine.c`, `mc_main_asm.c`, and (if the
  `#include` reverts) `memcheck.h`.  Keep the header in the files that
  Fjalar still modifies (`mc_main.c`, `mc_translate.c`, `mc_include.h`).
  If a later step makes another Memcheck copy identical to upstream, remove
  its header then.

### Step 5: replace scattered disabling by a single switch (PR 5)

- **`complainIfUndefined`**:  restore upstream's 30-odd calls, and the
  definitions of `complainIfUndefined` and `newShadowTmpV` (now inside
  `#ifdef DO_NOT_DEFINE_THIS`).  Instead, add one early `return;` at the
  top of `complainIfUndefined`, with a one-line comment that Fjalar does
  not check definedness.  This generates the same IR.  In the `Ist_Exit`
  case, keep Fjalar's `handle_possible_exit` call as a separate added line.
- **Leak checking and statistics at exit**:  `mc_fini`'s body,
  `mc_print_stats`, `show_client_block_stats`, and the profiling functions
  are inside `#ifdef UNDEFINED_FOO`, and the `init_prof_mem` call and
  `VG_(needs_print_stats)` are commented out.  Options cannot give the
  same effect, because upstream's `mc_fini` calls
  `MC_(print_malloc_stats)()`, which prints "HEAP SUMMARY" even with
  `--leak-check=no`.  Instead, restore upstream's code, and add
  `fjalar_finish(); return;` (with a one-line comment that Fjalar skips
  Memcheck's end-of-run reports) at the top of `mc_fini`, in place of
  Fjalar's `fjalar_finish()` call at its end.  The rest of `mc_fini` then
  still compiles, and it refers to the functions now inside
  `#ifdef UNDEFINED_FOO`, so they need no `#ifdef`.  Restoring the
  `init_prof_mem()` call is harmless, because `init_prof_mem` is empty
  unless `MC_PROFILE_MEMORY` is defined.  Restoring
  `VG_(needs_print_stats)` matters only with `--stats=yes`.  Check with
  `./test-kvasir.sh` that Kvasir's output does not change.
- **Warning silencers** (`(void)x;` casts, `#ifdef UNDEFINED_FOO` around
  `stats_ocacheL1_found_at_N`):  once the code that uses these variables
  and functions is restored, most of the warnings go away.  Silence the rest
  through flags for the Memcheck objects in `fjalar.am` or a
  `#pragma GCC diagnostic` in a Fjalar header, not by editing Memcheck.

### Step 6: move Fjalar code out of upstream files (PRs 6a-6d)

- **6a. `mc_include.h`.**  Move Fjalar's declarations, the `VGM_*`
  constants (which `mc_main.c` also defines, a duplicate), and the extra
  `#include`s into a new Fjalar header, such as `fjalar/mc_fjalar.h`.
  Restore `MC_ReadResult` to its upstream place in `mc_main.c`; change the
  exported `mc_check_readable` to return a type that does not need it, or
  declare it in the new header under another name.
- **6b. Fjalar's functions in `mc_main.c`** (`set_abit`,
  `set_abit_and_vbyte`, `mc_check_readable`, `mc_copy_guest_reg_state`, and
  others; about 130 lines).  They call `static` Memcheck functions, so move
  them to a Fjalar file and `#include` that file from `mc_main.c`, at the
  point where the block is now (after the definitions and forward
  declarations of the `static` functions that it calls), which keeps the
  change to `mc_main.c` to one line.  The file must not also be compiled
  on its own, which would define its functions twice, so give it a name
  that does not end in `.c` (such as `mc_main_fjalar.inc`) and do not list
  it in `FJALAR_SOURCES_COMMON` in `fjalar.am`.
- **6c. `mc_translate.c` definitions moved to `mc_translate.h`.**  Restore
  `MCEnv`, `TempMapEnt`, `HowUsed`, `DetailLevelByOp`, `stmt`, `assign`,
  the `binop`/`unop`/`mkU*` macros, and `IRAtom` to their upstream places in
  `mc_translate.c`, so that upstream changes to them merge.  Fjalar's code
  does not need the definitions:  DynComp (`kvasir/`) reads no field of
  `MCEnv`, and uses `MCEnv` only through `newTemp`, `stmt`, and `assign`;
  `fjalar_main.c` reads only `mce->layout`, and calls `stmt`.  So:
  - `mc_translate.h` declares `struct _MCEnv;`, as upstream's
    `mc_translate.c` already does near its top, and Fjalar's code refers to
    `struct _MCEnv*`.  (A `typedef struct _MCEnv MCEnv;` in the header
    would also work, because C11 allows repeating a typedef, but the
    forward declaration avoids depending on that.)  The header also
    declares `TempKind` and `IRAtom`, and its own copies of the trivial
    IR-building macros (`binop`, `unop`, `mkU*`, `mkexpr`).
  - `newTemp`, `shadowTypeV`, and `sameKindedAtoms` are already
    non-`static`.  Leave upstream's `static inline` `stmt` and `assign`
    unchanged, and add exported wrappers with distinctive names (such as
    `mc_stmt` and `mc_assign`) in Fjalar's part of `mc_translate.c`.
    Exporting functions named `stmt` and `assign` would put very generic
    names into a tool that also links Binutils and libiberty code.
  - Give `fjalar_main.c` the layout without reading `MCEnv`:  pass the
    `layout` argument of `MC_(instrument)` to Fjalar's entry and exit hooks
    instead of `mce`, or add an exported accessor.  After Step 7a,
    `fjalar_main.c` needs only `offset_SP`, `offset_FP`, `offset_IP`, and
    their sizes, which it could also get from `offsetof`.

  If DynComp later needs a field of `MCEnv`, add an accessor function
  rather than moving the definitions back to the header.  Shorten the
  comments on the `static` -> non-`static` changes to one line each.
- **6d. DynComp in `MC_(instrument)`.**  Move the loader-skipping logic and
  the `DCEnv` setup and teardown into functions in `dyncomp_translate.c`,
  so that each becomes one call.  For the per-statement hooks, consider
  replacing the eleven `if (do_dyncomp) ...` blocks inside the
  `switch` by a single `if (do_dyncomp) instrument_stmt_DC(&dce, st);`
  after the `switch`, with the `switch` on statement kinds in
  `dyncomp_translate.c`.  This changes the order of DynComp's statements
  relative to Memcheck's only if a `case` emits statements after its
  DynComp hook; check each case, and compare the IR
  (`--fjalar-debug --fjalar-print-ir`) before and after on the Kvasir
  tests.  Fall back to one-line hooks if
  the order matters.

### Step 7: shrink Coregrind, VEX, and include changes (PRs 7a-7d)

- **7a. Remove the guest-layout fields and `VEX_N_FXSTATE`.**
  `fjalar_main.c` uses `mce->layout->offset_xAX` and so on only to fill
  `fxState` for its two helper calls:  the entry helper
  (`enter_function`, 10 entries) and the exit helper (`exit_function`, 12
  entries).  Use `offsetof(VexGuestArchState, guest_...)` instead, as it
  already does for `guest_R8`, `guest_FTOP`, and `guest_FPREG`.  The
  registers `guest_RAX` through `guest_R15` are contiguous, so describe
  them as one `fxState` entry of 128 bytes.  Then the entry helper needs 2
  entries (that range and `guest_RIP`), and the exit helper needs 4 (that
  range, `guest_RIP`, `guest_FTOP`, and `guest_FPREG`); both fit in
  upstream's `VEX_N_FXSTATE` of 7.  Do the same in the x86 branches of
  both helper calls:  `guest_EAX` through `guest_EDI` are also contiguous
  (32 bytes, followed by `guest_CC_OP`, as on amd64), so the x86 entry
  helper needs 2 entries and the x86 exit helper 4.  This removes all of
  Fjalar's changes to `libvex.h`, `libvex_ir.h`, `guest_amd64_helpers.c`,
  and `guest_x86_helpers.c` (about 280 lines), and x86 keeps the same
  `fxState` coverage.  Check that no other Fjalar code
  uses the fields:  `git grep -n -a 'layout->\(offset\|sizeof\)_x'` (and the
  `XMM` and `R8`-`R15` fields).  `dyncomp_translate.c` uses only
  `offset_SP`, `offset_FP`, and `offset_IP`, which are upstream's.
- **7b. Move the register accessors out of `m_machine.c`.**  Reimplement
  `VG_(get_xAX)`, `VG_(get_shadow_xAX)`, `VG_(get_XMM_N)`,
  `VG_(get_shadow_XMM_N)`, `VG_(get_R8)`, and the rest in a Fjalar file,
  using the existing tool API `VG_(get_shadow_regs_area)(tid, buf,
  shadowNo, offset, size)` with `offsetof(VexGuestArchState, ...)`.  Give
  them Fjalar names (not `VG_(...)`).  `VG_(get_XMM_N)` and
  `VG_(get_shadow_XMM_N)` return pointers into the guest state, but
  `VG_(get_shadow_regs_area)` copies into a buffer, so their replacements
  return the value instead (for example, the low 64 bits as a `ULong`).
  Their two callers (`fjalar_main.c`, in the code that reads a function's
  floating-point return value) dereference the pointer at once, so they
  change easily.  Reimplement the x86 versions too
  (`VG_(get_FPU_stack_top)`, `VG_(get_shadow_FPU_stack_top)`, and
  `VG_(get_FPU_stack_top_tag)`, which read `guest_FTOP` and then the
  `guest_FPREG` element that it selects), in the same Fjalar file, under
  `#if defined(VGA_x86)`.  Drop the PPC parts (the `guest_GPR3` and
  `guest_GPR4` definitions of `VG_INT_RET_REG` and `VG_INT_RET2_REG`), the
  unused ones (`VG_(get_LR)`, `VG_(dump_state)`), and the declarations that
  duplicate upstream's (`VG_(get_SP)`, `VG_(get_IP)`, `VG_(set_IP)`,
  `VG_(set_SP)`).  Only `VG_(get_tag_ptr_for_guest_offset)` needs
  `vex_extra_shadow`, which a tool cannot reach; keep that one function in
  `m_machine.c` (about 6 lines), and declare it in `pub_core_machine.h` and
  in `fjalar_core_decls.h`.  The `fjalar_core_decls.stamp` rule in
  `fjalar.am` checks that each declaration in `fjalar_core_decls.h` agrees
  with the original, but only for the headers that the rule names
  (now `pub_core_aspacemgr.h` and `pub_core_mallocfree.h`).  Add
  `pub_core_machine.h` to the rule's prerequisites and to the `#include`s
  that it compiles.  This removes the `VG_INT_RET_REG`, `VG_XCX`, and
  similar macros from `pub_core_machine.h`, and all of Fjalar's changes to
  `pub_tool_machine.h`.
- **7c. File functions.**  Remove both of Fjalar's changes to
  `m_libcfile.c` and `pub_tool_libcfile.h`:
  - Move the declaration of `VG_(fcntl)`, which upstream defines and
    declares in `pub_core_libcfile.h` but does not export to tools, from
    `pub_tool_libcfile.h` to `fjalar_core_decls.h`.
  - Implement `mkdir` in Fjalar instead of in Coregrind.  `VG_(do_syscall)`
    is a core function, declared in `pub_core_syscall.h`; copy its
    declaration to `fjalar_core_decls.h`, get `__NR_mkdir` from
    `pub_tool_vkiscnums.h`, and define a Fjalar function (not named
    `VG_(...)`) that calls `VG_(do_syscall)(__NR_mkdir, path, mode, 0, 0,
    0, 0, 0, 0)`.  Its one caller is `kvasir_main.c`, which creates the
    `daikon-output` directory.  Then remove `VG_(mkdir)` from
    `m_libcfile.c` and `pub_tool_libcfile.h`.

  Add `pub_core_libcfile.h` and `pub_core_syscall.h` to the
  `fjalar_core_decls.stamp` rule, as in 7b.
- **7d. Remove the function-name printing in `host_amd64_defs.c`.**  It is
  a debugging aid that makes VEX depend on Coregrind, which forced the
  changes to `none/tests/Makefile.am` (linking `libcoregrind` into the
  libvex tests, `-nostartfiles`, no PIE) and to `none/tests/libvex_test.c`.
  Removing it removes all three diffs.  The cost is that VEX's back-end
  trace (`--trace-flags`) no longer names the target function of each
  call instruction, only its address.  DynComp's debugging output
  (`--dyncomp-debug`) names only the function of each block, which is not
  a replacement.  A developer who needs the names can map the addresses to
  functions with `nm` or `addr2line`.

### Step 8: minimize the changes that must remain (PR 8)

- **Extra shadow area**:  `vex_extra_shadow[4]` in `pub_core_threadstate.h`,
  the spill offset `* 7` in `host_generic_reg_alloc2.c` and
  `host_generic_reg_alloc3.c`, and the assertion in `scheduler.c`.  Keep
  them, but make each one a minimal change with a short comment that says
  why (the 4 extra shadow areas for DynComp tags), and drop the comments
  about who changed what from which number to which.  Consider defining the
  multiplier once (for example, in `libvex.h`) so a merge cannot update one
  of the three places and miss another; that adds a line but makes a silent
  inconsistency impossible.
- **Build system**:  keep `fjalar` in `TOOLS` and `fjalar/Makefile` in
  `configure.ac`.  Move the extra `rm -f config.guess config.sub
  Makefile.in` lines from `valgrind/Makefile.am` to the top-level Fjalar
  `Makefile`.  `AC_INIT` is upstream's again (codespecs/fjalar#181, whose
  description gives the reasons).
- **`tests/check_headers_and_includes`**:  keep `fjalar` in `%tool_dirs`.
  The `inst` entry is needed because Fjalar installs into `valgrind/inst`;
  installing elsewhere would remove it, but that is not worth changing for
  one line.
- **`mc_main.c` tool details**:  restore upstream's `VG_(details_name)`
  ... `VG_(details_bug_reports_to)` calls in `mc_pre_clo_init`, and make
  Kvasir's calls in `fjalar_tool_pre_clo_init` in `kvasir/kvasir_main.c`,
  which runs after them (through `fjalar_pre_clo_init`) and so overrides
  them.  The details are Kvasir's, not Fjalar's (`basic-tool` is another
  Fjalar tool), so `kvasir_main.c` is the right place.  Check that
  `basic-tool` still builds and prints sensible details (it would get
  Memcheck's unless it sets its own).  In a companion Daikon PR, change
  the release rule in Daikon's `Makefile`, which rewrites the
  `VG_(details_version)` line, to edit
  `fjalar/valgrind/fjalar/kvasir/kvasir_main.c` instead of
  `fjalar/valgrind/fjalar/mc_main.c`.  Either PR alone leaves the rule's
  pattern matching nothing:  after the Fjalar PR, `mc_main.c` has
  upstream's `VG_(details_version) (NULL);`, which the pattern does not
  match, and before it, `kvasir_main.c` has no such line.  So land the two
  PRs together (each description says "Land with" the other), and make
  the rule fail if its pattern matches nothing, so that a release made
  between the two landings fails instead of silently keeping the old
  version.
- **`CHECK_SP` in the `mc_new_mem_stack_*` functions** (about 30 one-line
  insertions):  leave them.  They are one-line insertions into code that
  upstream rarely changes, and the alternative (re-registering wrappers for
  every `VG_(track_new_mem_stack_*)` callback) is more code and more risk.
- **Upstream test sources** (`none/tests/bug234814.c`,
  `helgrind/tests/tc17_sembar.c`, `drd/tests/swapcontext.c`):  these fix
  builds with newer compilers.  Check whether a later upstream version
  made the same fixes.  If so, replace Fjalar's versions with upstream's
  exact text, so the merge applies cleanly; otherwise, report them
  upstream.

### Step 9: documentation

- Update the "Valgrind modifications" appendix of
  `doc/valgrind-merge.texinfo` and step 5 of `plan-upgrade-valgrind.md`,
  which list Fjalar's changes to Coregrind, to match what remains.
- Add `diff-from-valgrind.sh` to the merge procedure:  run it before and
  after a merge, and expect only the documented changes.

## Expected result

These are estimates, to be checked with `diff-from-valgrind.sh`.

| After step | Remaining differences (approximate) |
| --- | --- |
| Now | 43 files, 4924 changed lines |
| 1-2 | 34 files, about 2000 changed lines |
| 3-5 | about 25 files, about 900 changed lines |
| 6-8 | about 12 files, about 200 changed lines |

What remains is Fjalar's essential hooks:  the extra shadow area (4
files), the build integration (3 files), the extra-shadow tag accessor
(2 files:  `m_machine.c` and `pub_core_machine.h`), and the DynComp and
Fjalar hooks in `mc_main.c` and `mc_translate.c`.

## Not recommended

- **Compiling unmodified Memcheck files from `valgrind/memcheck/`** instead
  of keeping copies in `valgrind/fjalar/`.  `merge-valgrind.sh` already
  merges the copies, and a copy that is identical to upstream never
  conflicts, so this would save little and would complicate the build.
- **Running DynComp as a separate instrumentation pass** instead of
  interleaving it with Memcheck's.  It would remove the hooks from
  `MC_(instrument)`, but Memcheck would then instrument DynComp's helper
  calls, and the IR order would change; the risk is too high for the gain.

## Risks

- Step 5's early return from `mc_fini` must skip everything that Fjalar's
  `#ifdef` skips now, and nothing else; compare `./test-kvasir.sh`
  output.
- Step 6d could change the order of instrumentation statements; compare
  the IR before and after.
- Step 7a describes the same guest-state bytes to VEX with fewer, larger
  `fxState` entries.  The Kvasir tests check the formal-parameter and
  return values that depend on them.  Memcheck's `isAlwaysDefd` panics
  if an `fxState` range partly overlaps an always-defined part of the
  guest state.  In 3.23.0, the range `guest_RAX` through `guest_R15`
  overlaps none (the nearest, `guest_CC_OP`, follows `guest_R15`); after
  each Valgrind merge, check `.alwaysDefd` in `guest_amd64_helpers.c`
  again.
- Restoring upstream names (Step 4) could bring back warnings that
  `compare-warnings.sh` reports as new; fix them in Fjalar's headers.
