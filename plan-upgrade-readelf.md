# Plan: upgrade Fjalar's readelf code from Binutils 2.39 to 2.47

Reference procedure: `doc/valgrind-merge.texinfo`, chapter "Updating Readelf
from Binutils".  This plan applies that procedure to the current situation and
notes where it needs adjusting.

Below, `$FJALAR` is the Fjalar tree being upgraded (see step 1).

## Ordering: do this before the Valgrind upgrade

First do item 4 of the preparation in `plan-pre-upgrade.md` (whitespace
that matches Binutils 2.39, so that step 5's `git merge-file` reports no
whitespace-only conflicts); this plan assumes it.  Item 1 (enforcing the
expected regtest failures in CI) need not be done first.
Step 2 creates a local expected-failures list if this machine's OS has
none, and step 8 compares against it.  Until CI enforces the lists, that
local comparison is the only regtest check, because the CI regtest jobs
only report failures.

Do this upgrade, before `plan-upgrade-valgrind.md`, and finish it
completely (landed, CI green) before starting the Valgrind upgrade.  Reasons:

- It is smaller and self-contained: about a dozen files in `valgrind/fjalar/`,
  with conflicts concentrated in `dwarf.c` and `readelf.c`.
- Its failures are easy to attribute (spurious output or missing variables in
  Kvasir output).  Valgrind-merge failures are subtler (crashes, wrong
  comparability, DynComp panics), so it's better to start that merge from a
  known-good tree where any regression is clearly due to Valgrind.
- The Fjalar edits to `dwarf.c` from #73 and #76 (DWARF 3/4 and Rust
  support in Fjalar's harvesting code) are recent and will be the main
  conflict hotspots; it is easier to resolve them before the Valgrind merge
  adds its own churn.

Exception: if a user is currently blocked by something only newer Valgrind
fixes (e.g., an unsupported instruction or syscall on a new distro), do the
Valgrind upgrade first.  (DynComp panics such as #79 are not in this
category: DynComp is Fjalar code, and newer Valgrind is more likely to cause
new ones than to fix them.)

## Current state

- `valgrind/REVISION`: `BINUTILS_VERSION=2.39` (released 2022-08-05).
- Latest release on ftp.gnu.org: **2.47** (Fjalar never upgraded to any of 2.40-2.46.1).
- Fjalar does not run `readelf`; it compiles a modified copy of the
  `readelf` sources and uses the `harvest_*` hooks in `dwarf.c` to collect
  DWARF information.  Binutils-derived files in `valgrind/fjalar/`:
  - `readelf.c` (~23.4k lines, 39 `#if 0` regions), `dwarf.c` (~13.4k, 31
    `#if 0` regions), `dwarf.h`, `elfcomm.c/h`, `bucomm.h`, `demanguse.h`
  - `include/` (`dwarf2.def`, `dwarf2.h`, `demangle.h`, `ctf.h`, `ctf-api.h`,
    `safe-ctype.h`, `elf/*.h`)
  - `libiberty/dwarfnames.c`
- Fjalar code that consumes these files and may need adjustment if upstream
  data structures change: `fjalar_dwarf.c`, `typedata.c`,
  `generate_fjalar_entries.c`, `fjalar_main.c`, `kvasir/decls-output.c`.
- Fjalar-local edits must survive the merge.  They are already in the Fjalar
  copy, so applying the upstream 2.39->2.47 diff onto it preserves them; just
  don't clobber them while resolving conflicts.  The complete checklist is
  the Fjalar-vs-pristine-2.39 diffs created in step 3; that includes older
  edits and the edits made during the Valgrind 3.23 merge (`f15d19e3`, #72).
  Edits since the 2.39 merge include:
  - `55ae3f48` define PTR (#62)
  - `be9be5f0` fix for newer versions of bfd.h (#63)
  - `1ca71b1c` Support DWARF 3 (#73)
  - `d8723ef7` spelling corrections (#75)
  - `95516533` Support Rust and DWARF 3 & 4 (#76)
  - `a620e75a` Fix Fjalar hang on optimized code with location views (#89)
  - `89754787` Read DWARF registers through their guest-state offsets (#91)
  - `a6948b30` and `0d7bdabd` use `true`/`false`, not `TRUE`/`FALSE`, in
    `fjalar_process_file` in `readelf.c`
- Open PRs that change `dwarf.c` (as of 2026-10-20):  the formal-parameter
  location PRs #144 (record every `DW_OP_const*`), #145 (no tag tests around
  the `harvest_*` calls), #95 (unsupported DWARF location operations, which
  contains #144 and #145), and #146 (`DW_OP_piece`) and #147 (register
  locations that Fjalar cannot read), which contain #95; and #134
  (whitespace that matches Binutils 2.39; `plan-pre-upgrade.md` item 4),
  which also changes `readelf.c` and `bucomm.h`.  Land them before starting
  this upgrade, so that their changes are part of the Fjalar copy being
  merged into (and of the Fjalar-vs-2.39 diffs) rather than conflicting
  with the upgrade later.  Re-check the location PRs' `dwarf.c` changes
  while resolving conflicts, as for #73/#76.
  Whichever of #134 and each location PR lands second must keep the
  other's changes.  In particular, no line that a location PR adds or
  changes may differ from Binutils 2.39 only in whitespace; after all of
  them have landed, redo #134's procedure (in its description), which then
  changes nothing if all is well.

## Key decision: one jump or stepwise?

Eight releases is the largest gap so far (previous merges: 2.35.1 -> 2.36.1 ->
2.37 -> 2.39).  `dwarf.c` and `readelf.c` are where nearly all conflicts occur.

Decision: do not make a single 2.39 -> 2.47 jump.  Upgrade in three hops:
2.39 -> 2.42, 2.42 -> 2.45, and 2.45 -> 2.47.  If the 3-way merge
(`git merge-file`, step 5) of `dwarf.c` or `readelf.c` in some hop has more
conflicts than can reasonably be hand-merged, split that hop further (for
example, 2.39 -> 2.40 -> 2.42), down to one release per hop if necessary.
`./merge-binutils.sh --dry-run` (step 5) prints the number of conflicts
in each file without changing any.

Do steps 3-8 once per hop, on the same branch.  In those steps, "2.39" and
"2.47" stand for the hop's old and new versions, and `$BUNEWVER` is the
hop's new version (set it with, e.g., `BUNEWVER=2.42`).  The scripts take
the old version from `BINUTILS_VERSION` in `valgrind/REVISION`.  So at the
end of each hop, update `valgrind/REVISION` to the hop's new version (as
described in step 9) and commit, with commit message "Upgrade Binutils
(readelf) from 2.39 to 2.42" (for the first hop), before starting the
next hop.  Do steps 1, 2, and 9 only once.

The scripts that this plan uses are in the top-level directory of the
Fjalar tree.  The Binutils ones work in `/tmp/$USER/binutils/`.

## Key decision: no new features

Do not add support for new features (SFrame, zstd-compressed sections,
debuginfod, new architectures).  Put new unneeded code under
`#if 0 // This code is not needed for Fjalar.` so that future merges stay
small.

## Steps

1. **Preparation** (separate branch, e.g. `binutils-2.47`; do not combine with
   the Valgrind upgrade).
   - Work in a new clone, because each working directory is dedicated to
     one branch: clone Fjalar into, e.g., `$INV/fjalar-branch-binutils-2.47`
     and create the branch there.  Set `FJALAR` to that clone, e.g.,
     `FJALAR=$INV/fjalar-branch-binutils-2.47`; the commands below use it.
   - `git pull` both `fjalar` and `daikon`; ensure clean trees.
   - Make sure the system has `binutils-dev` / `binutils-devel` (for `bfd.h`).

2. **Baselines** (before touching any source).  Run these from the new
   clone (`cd $FJALAR`).
   - `(set -o pipefail; make build 2>&1 | tee build-before.log) && ./check-regtest.sh`
     (Valgrind regtest baseline; must report no unexpected failures).  The
     new clone is already clean; do not run `make clean` first, because it
     fails until `make build` has created `valgrind/Makefile`.
     `pipefail` makes a failed build stop the command, rather than `tee`'s
     success hiding it.  If this machine's OS has no
     `regtest-expected/<os>.txt`, create a local one with
     `./check-regtest.sh --log regtest-<os>.log --update` and don't commit it.
   - Keep `build-before.log` (ignored by git, as is every `*.log` file),
     whose compiler warnings step 7 compares with those of the merged
     code.
   - `make fjalar-test`.
   - Record the tool's symbols related to zstd, SFrame, and debuginfod, for
     step 8, in a file outside the tree, so that it is not committed:

     ```sh
     mkdir -p /tmp/$USER/binutils
     nm valgrind/fjalar/fjalar-amd64-linux | grep -iE 'zstd|sframe|debuginfod' \
       | awk '{print $3}' > /tmp/$USER/binutils/nm-before.txt
     ```

     (This lists only Valgrind core's own debuginfod support.)  `ldd` and
     `nm -u` would show nothing, because Valgrind tools are linked
     statically with `-nodefaultlibs` (`valgrind/Makefile.tool.am`).
   - Run the Kvasir tests with `./test-kvasir.sh 2>&1 | tee kvasir-before.log`
     (Kvasir baseline; record any pre-existing failures).  `./test-kvasir.sh`
     temporarily points `$DAIKONDIR/fjalar` at this tree (it restores the
     old link on exit, and refuses to run if `$DAIKONDIR/fjalar` is a
     directory rather than a symbolic link; then set `DAIKONDIR` to
     another, possibly nonexistent, directory).  Do not use
     `make daikon-test`: it ignores `$DAIKONDIR` and builds whatever
     `../daikon/fjalar` points to (by default `$INV/fjalar`, which is a
     different clone than `$FJALAR`).  Running
     `$INV/daikon/tests/kvasir-tests` directly has the same problem; if you
     do that, first check `readlink -f $INV/daikon/fjalar`.

3. **Create patch files.**  `./generate-binutils-patch-files.sh $BUNEWVER`
   downloads and verifies the old and new Binutils releases, extracts
   them in `/tmp/$USER/binutils/`, and writes these files to
   `/tmp/$USER/binutils/2.39-$BUNEWVER/`:
   - `include.patch`, the upstream changes to the files in `include/` and
     to `libiberty/dwarfnames.c`, which step 5 applies.  There is no patch
     file for Binutils' `binutils/` directory.  Fjalar's copies of files
     from that directory carry Fjalar edits, so step 5 merges each of them
     with `git merge-file` instead.
   - `*-binutils-vs-fjalar.diff`, Fjalar's changes to each
     Binutils-derived file, for visual verification while resolving
     conflicts.

4. **Check for new upstream dependencies.**  Before patching, check whether
   2.47's `readelf.c`/`dwarf.c`/`elfcomm.c` `#include` any header (under
   `include/`, `include/elf/`, or `binutils/`) that Fjalar does not yet have,
   and whether they call into new helper files (e.g. new code split out of
   `dwarf.c`).  Copy any new needed headers into `valgrind/fjalar/include/`
   and add any new needed `.c` files to `FJALAR_SOURCES_COMMON` in
   `valgrind/fjalar/fjalar.am`.  (Do not edit `valgrind/fjalar/Makefile.am`,
   which `generate-fjalar-makefile.sh` regenerates at each Valgrind merge.)
   (`demanguse.h` and the CTF headers were added this way in the 2.39 merge.)
   The extracted new release is in `/tmp/$USER/binutils/binutils-$BUNEWVER/`.
   If the code that needs a new header is disabled, disable the `#include`
   under `#if 0` instead.  Remove headers that upstream deleted.
   - Known case: Binutils 2.40 added `readelf --sframe`, which includes
     `sframe-api.h` and calls into libsframe.  Fjalar does not need it:
     disable that code with `#if 0 // This code is not needed for Fjalar.`
     (as was done for CTF) rather than vendoring libsframe.
   - New `include/elf/*.h` files (e.g. for new architectures) are not in
     `include.patch`, because `diff -ur` without `-N` lists them only as
     "Only in ..."; copy those that 2.47's `readelf.c` includes.
   - Binutils 2.40+ can decompress zstd-compressed debug sections.  Make
     sure that code compiles out cleanly with `HAVE_ZSTD` undefined, rather
     than pulling in libzstd.
   - `dwarf.c` and `readelf.c` include the *system* `bfd.h`
     (from `binutils-devel`/`binutils-dev`), which on the CI distros is
     older than 2.47.  Grep 2.47's versions of those files for bfd macros
     and functions (`bfd_*`, `BFD_*`, `startswith`, ...) and check that
     each exists in the oldest `bfd.h` used in CI.  On 2026-10-17, the CI
     containers had these versions (the regtest jobs' "System information"
     step logs them):
     - Ubuntu 26.04 (`daikon-ubuntu-jdk11-plus`): `binutils-dev`
       2.46-3ubuntu2.
     - Rocky Linux 10 (`daikon-rockylinux-jdk25-plus`): `binutils-devel`
       2.41-63.el10.

     So the oldest `bfd.h` in CI is from Binutils 2.41.
     2.47's code may use bfd definitions newer than that version.
     Anything missing needs a local definition, as #63 did.

5. **Apply `include.patch` and merge the files from Binutils' `binutils/`
   directory.**  First run `./merge-binutils.sh --dry-run $BUNEWVER`,
   which changes no file:  it prints what applying `include.patch` would
   print, and the number of conflicts that merging each file would have.
   Then run `./merge-binutils.sh $BUNEWVER`.  It applies `include.patch`
   with `patch --merge=diff3`, and merges each of Fjalar's copies of files
   from Binutils' `binutils/` directory with `git merge-file --diff3`.
   It refuses to run if those files have uncommitted changes, or if an
   earlier run left `.pre-merge` copies, and it prints how to undo the
   merge.

   Both `patch --merge=diff3` and `git merge-file --diff3` write
   conflicts inline as `<<<<<<<`/`|||||||`/`=======`/`>>>>>>>` markers
   instead of creating `.rej` files; find them with `git status` and
   `grep -rln '^<<<<<<<' valgrind/fjalar`.  Unlike `patch` with fuzz,
   `git merge-file` never applies a hunk at the wrong location.  The
   script copies each merged file to a `.pre-merge` file, for a visual
   merge tool, e.g., in `valgrind/fjalar/`:

   ```sh
   meld /tmp/$USER/binutils/binutils-$BUNEWVER/binutils/dwarf.c \
     dwarf.c dwarf.c.pre-merge
   ```

6. **Resolve conflicts** (expected mostly in `dwarf.c` and `readelf.c`),
   following "Hints to modifying dwarf.c and readelf.c":
   - Keep `#if 0 // This code is not needed for Fjalar.` blocks disabled;
     new upstream code that only prints (e.g. new section dumpers) should go
     inside such blocks or be guarded.
   - Guard every new `printf`/`putchar` with `fjalar_debug` /
     `fjalar_debug_dump` (or `FJALAR_DPRINTF`); hoist side-effecting
     arguments (e.g. `read_uleb128`, `READ_ULEB`, `SAFE_BYTE_GET_AND_INC`)
     out of guarded `printf`s.
   - Replace libc calls with `VG_(...)` equivalents and `assert` with
     `tl_assert`.
   - Make sure Fjalar's hooks in `dwarf.c` and `readelf.c` still run on
     every path.  The hooks are the calls to functions declared in
     `typedata.h`, `fjalar_dwarf.h`, `fjalar_include.h`, `fjalar_main.h`,
     and `GenericHashtable.h`, which build Fjalar's DWARF entries, symbol
     tables, and line-number table:  the `harvest_*` functions, and others
     such as `add_comp_unit`, `initialize_dwarf_entry_array`,
     `tag_is_formal_parameter`, and `genputtable` in `dwarf.c`, and
     `insertIntoFunctionSymbolTable`, `insertIntoVariableSymbolTable`, and
     `process_elf_binary_data` in `readelf.c`.  (`dwarf.c` also defines
     one, `dwarf_reg_name`.)  Re-check every
     call site (`harvest_formal_param_location_atom`,
     `harvest_location_list_entry`, `harvest_frame_base`,
     `harvest_debug_frame_entry`, etc.) against the restructured upstream
     code, so that no hook is dropped or moved to the wrong branch,
     especially for DWARF 5 forms and any new `DW_FORM_*`, `DW_AT_*`,
     `DW_OP_*` handling.  Re-check the DWARF 3/4 and Rust changes from
     #73/#76, the location-view change from #89, and #91's
     `dwarf_reg_name()`, which wraps `regname()` and which `fjalar_main.c`,
     `fjalar_traversal.c`, and `generate_fjalar_entries.c` call:  re-check
     it if upstream changed `regname()`'s signature or behavior.
   - Areas to expect to need attention in 2.40-2.47:
     - DWARF 5 handling in `dwarf.c` (`.debug_rnglists`, `.debug_loclists`,
       `.debug_str_offsets`, `.debug_addr`, `DW_FORM_*x` forms, `DW_OP_*`
       additions), the main reason to upgrade, and where the hook check
       above matters most.
     - debuginfod (`HAVE_LIBDEBUGINFOD`): already conditionally compiled;
       ensure it stays undefined.
     - New `readelf` command-line options or global flags: Fjalar sets
       `do_debug_*` and related globals itself; check `fjalar_main.c` and
       the top of `readelf.c` for renamed or newly required globals.
     - Changed data structures in `dwarf.h` (for example `debug_info`,
       `dwarf_section`, `separate_info`): update the Fjalar consumers listed
       in "Current state" if fields were renamed.
   - Review every new `if (fjalar_debug...)` guard for a side-effecting
     expression left inside it.
   - Before building, confirm that no conflict markers remain
     (`grep -rn '^\(<<<<<<<\|=======\|>>>>>>>\|||||||\)' .` prints nothing).
     Delete the `.pre-merge` copies once the merge is complete.
     `.gitignore` hides them from `git status`; find them with
     `find -name '*.pre-merge'`.

7. **Build and fix warnings/errors.**  `make -C $FJALAR build`, then
   iterate with `make -C $FJALAR/valgrind/fjalar`.  Fix "implicit
   declaration" and "undefined reference" errors (missed `VG_()` wrappers).
   Reduce new warnings from Valgrind's stricter flags where practical.
   To list them, recompile the Binutils-derived files, from `$FJALAR`.
   The incremental builds have already compiled those files, so a build
   that does not first remove Fjalar's object files prints none of their
   warnings.

   ```sh
   make -C $FJALAR/valgrind/fjalar clean
   (set -o pipefail; make -C $FJALAR/valgrind/fjalar 2>&1 | tee $FJALAR/build-after.log)
   $FJALAR/compare-warnings.sh --binutils $FJALAR/build-before.log $FJALAR/build-after.log
   ```

   `compare-warnings.sh` prints the warnings for the Binutils-derived files
   that are new (`>` lines) or gone (`<` lines), ignoring line numbers,
   which the merge changes.
   Also build against the system `bfd.h` on both Rocky Linux and Ubuntu
   (see step 4; the #63 workaround may need to change).
   Finally, run `make -C $FJALAR/valgrind/fjalar install`.
   `make -C valgrind/fjalar` does not install the tool, but
   `make fjalar-test` (step 8) runs the installed one,
   `valgrind/inst/bin/valgrind`.

8. **Test.**  Run these from `$FJALAR` (`cd $FJALAR`).
   - `./check-regtest.sh` — must report no unexpected failures, with no
     change to `regtest-expected/*.txt`.  This upgrade doesn't touch
     Valgrind, so any new failure is a bug in the merge (or an OS/compiler
     update; then re-run on the old sources to check).
   - `make fjalar-test`.
   - `./test-kvasir.sh 2>&1 | tee kvasir-after.log` — compare with
     `kvasir-before.log`; the tests must pass with no goal-file changes.
     Superfluous output in `.out` diffs, or in a Kvasir `.decls` or
     `.dtrace` file, usually means an unguarded `printf`.
   - The regression tests may not exercise the newer DWARF paths, so also
     run Kvasir on a small C program compiled with `-gdwarf-5` and with
     `-gdwarf-4`, using both the current gcc and clang, and confirm that the
     `.decls` output is identical between the two DWARF versions.
   - Run with `--fjalar-debug-dump=yes` on a DWARF 5 binary and compare
     against `readelf --debug-dump` from Binutils 2.47 for sanity.  The
     system `readelf` is older (2.46 on Ubuntu 26.04, 2.41 on Rocky Linux
     10), so build 2.47's:  `./build-binutils-readelf.sh $BUNEWVER` builds
     it (outside the extracted tree that step 5 merges from) and prints its
     path.
   - Before committing, run `./check-hook-counts.sh`.  It counts the calls
     of each hook (step 6) in the old and new `dwarf.c` and `readelf.c`,
     and prints each hook whose count changed, with the file and the old
     and new counts; explain each difference.  The old files are those of
     the commit where this branch started, even if the branch already has
     commits (as it does after the first hop).  The count omits `#if 0`
     regions and comments, so that it notices a hook that conflict
     resolution moved into disabled code.  It does include string literals,
     so a hook's name in a debugging message counts as a call; check any
     difference that involves one.
   - Check that no zstd, SFrame, or debuginfod code was compiled in: run
     the `nm` command of step 2 again, writing
     `/tmp/$USER/binutils/nm-after.txt`;
     `diff /tmp/$USER/binutils/nm-before.txt /tmp/$USER/binutils/nm-after.txt`
     must print nothing.  (A call into
     a system library such as libzstd or libsframe would instead have
     caused an "undefined reference" link error in step 7, because the
     tool is linked with `-nodefaultlibs`.)
   - Push the branch and confirm GitHub Actions CI passes (Ubuntu and
     Rocky Linux: build, regtest, and Kvasir jobs).

9. **Finish.**
   - Update `valgrind/REVISION`: the `# Binutils version 2.47, released ...`
     comment and `export BINUTILS_VERSION=2.47`.
   - Update copyright-year header lines in the Binutils-derived files if
     upstream changed them (previous Binutils merges did).
   - Note the upgrade in `$INV/daikon/doc/CHANGELOG.md` if user-visible (for
     example, better DWARF 5 support).
   - Update `doc/valgrind-merge.texinfo` in the same PR, while the merge is
     fresh, so that chapter "Updating Readelf from Binutils" matches the
     procedure actually used: anything learned (e.g. stale URLs, new hints
     such as the SFrame handling), and what this plan adds to the
     documented procedure:
     - working in a new clone (step 1);
     - merging in several hops (section "Key decision: one jump or
       stepwise?");
     - the checklist of upgrade-sensitive areas (step 6);
     - the DWARF 4 versus DWARF 5 comparison and the `nm` check for zstd,
       SFrame, and debuginfod code (step 8).
     The doc already uses the scripts of steps 3, 5, 7, and 8.  If the
     `git merge-file` merge of step 5 turned out worse than `patch` in
     practice, say why, and change `merge-binutils.sh` and the doc.
     Update the list of compiler warning flags if it changed.  Rebuild
     with `make doc` (which `test.sh` runs in CI) to confirm that the
     document still formats.
   - If step 2 created a local `regtest-expected/<os>.txt`, delete it
     before committing:  git does not ignore it, so `git add -A` would
     commit it.
   - Commit the doc and changelog updates (the whole branch is one PR, whose
     title is "Upgrade Binutils (readelf) from 2.39 to 2.47"); keep
     `include.patch` and the
     Fjalar-vs-binutils diffs for reference (perhaps attached to the PR).
     Delete `regtest-<os>.log`, `regtest-<os>-post.log`, and
     `regtest-<os>-observed.txt` (ignored by git).

## Risks

- Large upstream refactorings in `dwarf.c` (DWARF 5 / split-DWARF / debuginfod
  handling) could make the merge hard; this is the main reason for the 3-way
  merge and the stepwise upgrade.
- 2.47's `readelf.c`/`dwarf.c` may use bfd macros or functions that the
  older system `bfd.h` on the CI distros lacks (see step 4).  This may show
  up only on one distro, so CI on both Ubuntu and Rocky Linux matters.
- Silent loss of a Fjalar hook in a conflicted hunk would show up only as
  missing variables in Kvasir output, so the Kvasir regression tests are the
  essential check, together with the hook-count check (step 8).
- An unguarded side-effecting expression inside a guarded `printf` changes
  parsing only when debugging is off.  Mitigation: review every new guard
  (step 6).
- Code for zstd, SFrame, or debuginfod could be compiled in.  Mitigation:
  the `nm` check (step 8).  A call into a system library that Fjalar does
  not link fails the link (step 7).
- The later Valgrind upgrade may enable additional warning flags, which will
  hit `readelf.c`/`dwarf.c` again.  Expect a second round of warning fixes
  there; it does not mean this merge was done wrong.
