# Plan: upgrade Fjalar's readelf code from Binutils 2.39 to 2.47

Reference procedure: `doc/valgrind-merge.texinfo`, chapter "Updating Readelf
from Binutils".  This plan applies that procedure to the current situation and
notes where it needs adjusting.

Below, `$FJALAR` is the Fjalar tree being upgraded (see step 1).

## Ordering: do this before the Valgrind upgrade

This plan assumes that the whitespace of Fjalar's Binutils-derived files
matches Binutils 2.39 (#134), so that step 3's `git cherry-pick` reports
no whitespace-only conflicts.  CI enforces the expected regtest failures
(#175), so step 7's CI run checks the regression tests on both distributions.
Step 2 creates a local expected-failures list if this machine's OS has
none, and step 7 of the last hop compares against it.

Do this upgrade first, before `plan-upgrade-valgrind.md`, and finish it
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
- Fjalar code outside these files uses them only through a few functions:
  it calls `process_elf_binary_data` (defined in `readelf.c`, called from
  `fjalar_main.c`) and `dwarf_reg_name` (defined in `dwarf.c`, called from
  `fjalar_main.c`, `fjalar_traversal.c`, and `generate_fjalar_entries.c`),
  and the Fjalar code in `dwarf.c` and `readelf.c` calls Fjalar's hooks
  (step 5), whose parameter types are Fjalar's own.  `fjalar_dwarf.h`
  includes `dwarf.h`, but no file outside the Binutils-derived ones uses
  `dwarf.h`'s data structures (such as `debug_info`, `dwarf_section`, and
  `separate_info`) or its `dwarf_vma` type.  So if upstream changes those
  structures or types, only the Fjalar edits inside `dwarf.c` and
  `readelf.c` need adjusting, plus the signatures of those functions if
  they use the changed types.  However, every Fjalar file that includes
  `fjalar_dwarf.h`, directly or through `typedata.h` or `fjalar_include.h`,
  compiles `elfcomm.h` and `dwarf.h`.  So if those headers start to need
  a type or header that Valgrind's tool headers do not supply (such as
  `<stdint.h>`'s `uint64_t`), or define a name that clashes with them, the
  build of those files fails too.
- Fjalar-local edits must survive the merge.  They are already in the Fjalar
  copy, so merging the upstream 2.39->2.47 changes into it preserves them;
  just don't clobber them while resolving conflicts.  The complete checklist
  is the Fjalar-vs-pristine-2.39 diff created in step 3; that includes older
  edits and the edits made during the Valgrind 3.23 merge (`f15d19e3`, #72).
- Land the open PRs that change the Binutils-derived files before starting
  this upgrade, so that their changes are part of the Fjalar copy being
  merged into (and of the Fjalar-vs-2.39 diffs) rather than conflicting
  with the upgrade later.  To list them:

  ```sh
  gh pr list -R codespecs/fjalar --limit 1000 --json number,files --jq \
    '.[] | select((.files | length) >= 100
                  or any(.files[]; .path | test("^valgrind/fjalar/(readelf\\.c|dwarf\\.[ch]|elfcomm\\.[ch]|bucomm\\.h|demanguse\\.h|include/|libiberty/)")))
         | .number'
  ```

  `gh` returns only the first 100 files of each PR, so the command also
  lists every PR with 100 or more files; check those by hand.

  No line that such a PR adds or changes may differ from Binutils 2.39
  only in whitespace, which the landed #134 made Fjalar's copies match;
  after all of them have landed, redo #134's procedure (in its
  description), which then changes nothing if all is well.

## Key decision: one jump or stepwise?

Eight releases is the largest gap so far (previous merges: 2.35.1 -> 2.36.1 ->
2.37 -> 2.39).  `dwarf.c` and `readelf.c` are where nearly all conflicts occur.

Decision: do not make a single 2.39 -> 2.47 jump.  A trial merge of 2.47 on
2026-10-21 had 133 conflicts in `dwarf.c`, 59 in `readelf.c`, and 1 each in
`bucomm.h`, `dwarf.h`, `elfcomm.c`, and `elfcomm.h`; the include files merged
without conflicts.  Upgrade one release per hop, in eight hops: 2.39 ->
2.40 -> 2.41 -> 2.42 -> 2.43 -> 2.44 -> 2.45 -> 2.46.0 -> 2.47.  (The
2.46 release is named 2.46.0.)  Skip the point releases 2.43.1, 2.45.1,
and 2.46.1:  they are bug-fix releases from release branches, and the
next release includes their fixes.  If the merge (step 3) of a hop has
many conflicts, try undoing it with `git -C $FJALAR reset --hard` and
redoing it with `$FJALAR/merge-binutils.sh $BUNEWVER -Xpatience`, which
may group the changes into fewer or smaller conflicts.

Do steps 3-7 once per hop, on the same branch.  In those steps, "2.39" and
"2.47" stand for the hop's old and new versions, and `$BUNEWVER` is the
hop's new version (set it with, e.g., `BUNEWVER=2.40`).  The scripts take
the old version from `BINUTILS_VERSION` in `valgrind/REVISION`.  So in
step 7 of each hop, after the local tests pass and before pushing, update
`valgrind/REVISION` to the hop's new version (the
`# Binutils version 2.40, released ...` comment and
`export BINUTILS_VERSION=2.40`, for the first hop) and commit, with commit
message "Upgrade Binutils (readelf) from 2.39 to 2.40" (for the first hop).  If step 2 created a local
`regtest-expected/<os>.txt`, do not commit it:  git does not ignore it, so
`git add -A` would commit it.  Do steps 1, 2, and 8 only once.

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
   - `git pull` in `daikon`, and ensure that it has no local changes.  (The
     new Fjalar clone is already up to date.)

2. **Baselines** (before touching any source).  Run these from the new
   clone (`cd $FJALAR`).
   - `(set -o pipefail; make build 2>&1 | tee build-before.log) && ./check-regtest.sh`
     (Valgrind regtest baseline; must report no unexpected failures).  The
     new clone is already clean; do not run `make clean` first, because it
     fails until `make build` has created `valgrind/Makefile`.
     `pipefail` makes a failed build stop the command, rather than `tee`'s
     success hiding it.  If this machine's OS has no
     `regtest-expected/<os>.txt`, then `./check-regtest.sh` fails with "no
     expected-failures file", after writing `regtest-<os>.log`; create a
     local expected-failures file from that log with
     `./check-regtest.sh --log regtest-<os>.log --update` and don't commit it.
     Then run `./check-regtest.sh` at least twice more, and give a `?`
     prefix to each test whose result differs between runs (such as
     timing-dependent helgrind or `fdleak` tests), as
     `regtest-expected/ubuntu-26.04.txt` does.  Otherwise step 7 would
     report such a test as an unexpected failure, which is not a bug in the
     merge.
   - Keep `build-before.log` (ignored by git, as is every `*.log` file),
     whose compiler warnings step 6 compares with those of the merged
     code.
   - `make fjalar-test`.
   - Record the tool's symbols related to zstd, SFrame, and debuginfod, for
     step 7, in a file outside the tree, so that it is not committed:

     ```sh
     (umask 077 && mkdir -p /tmp/$USER/binutils)
     (set -o pipefail; nm valgrind/fjalar/fjalar-amd64-linux \
       | awk 'tolower($NF) ~ /zstd|sframe|debuginfod/ {print $NF}' \
       > /tmp/$USER/binutils/nm-before.txt)
     ```

     (This lists only Valgrind core's own debuginfod support.)  `pipefail`
     makes a failure of `nm` fail the command; otherwise an empty file
     would result, and two empty files would compare equal in step 7.  `ldd` and
     `nm -u` would show nothing, because Valgrind tools are linked
     statically with `-nodefaultlibs` (`valgrind/Makefile.tool.am`).
   - Run the Kvasir tests with
     `(set -o pipefail; ./test-kvasir.sh 2>&1 | tee kvasir-before.log)`
     (Kvasir baseline; record any pre-existing failures).  As in the build
     command above, `pipefail` keeps `tee`'s success from hiding a failure.
     `./test-kvasir.sh` temporarily points `$DAIKONDIR/fjalar` at this tree
     (it restores the old link on exit, and refuses to run if
     `$DAIKONDIR/fjalar` is a directory rather than a symbolic link; then
     set `DAIKONDIR` to another, possibly nonexistent, directory).  Do not use
     `make daikon-test`: it ignores `$DAIKONDIR` and builds whatever
     `../daikon/fjalar` points to (by default `$INV/fjalar`, which is a
     different clone than `$FJALAR`).  Running
     `$INV/daikon/tests/kvasir-tests` directly has the same problem; if you
     do that, first check `readlink -f $INV/daikon/fjalar`.
   - Create the DWARF 4 and DWARF 5 baseline for step 7.  Write a small C
     program in `/tmp/$USER/binutils/prog/`, outside the tree, with
     structs, arrays, pointers, and function parameters and locals.
     Compile it with each of the current gcc and clang, with each of
     `-gdwarf-4 -no-pie` and `-gdwarf-5 -no-pie`, giving four binaries,
     such as `prog-gcc-dwarf5`.  (`-no-pie` is needed because Fjalar
     recognizes a function's entry point only at the address in the
     debugging information.)  Run Kvasir on each, writing each `.decls`
     file into `/tmp/$USER/binutils/decls-before/`, which Kvasir does not
     create:

     ```sh
     mkdir -p /tmp/$USER/binutils/decls-before
     valgrind/inst/bin/valgrind --tool=fjalar --decls-only \
       --decls-file=/tmp/$USER/binutils/decls-before/prog-gcc-dwarf5.decls \
       /tmp/$USER/binutils/prog/prog-gcc-dwarf5
     ```

     Note the differences between the DWARF 4 and DWARF 5 `.decls` files
     of the same compiler.  Expect some:  Fjalar does not fully read
     DWARF 5 (for example, it reads location lists only from `.debug_loc`,
     not from DWARF 5's `.debug_loclists`).

3. **Merge.**

   ```sh
   $FJALAR/merge-binutils.sh $BUNEWVER
   ```

   The script downloads 2.39 and 2.47 into `/tmp/$USER/binutils/`, verifies
   their signatures, and extracts the parts that it needs.  It writes the
   checklist of Fjalar's changes to pristine 2.39 to
   `/tmp/$USER/binutils/2.39-2.47/binutils-Fjalar.diff`.  Then it merges
   upstream's changes into Fjalar's copies of Binutils files with
   `git cherry-pick`, stages the result, and lists the files with conflicts.
   `git -C $FJALAR diff binutils-merge/base binutils-merge/new` shows
   upstream's changes.  To start over, run `git -C $FJALAR reset --hard`.

4. **Check for new upstream dependencies.**  The script lists the headers
   that 2.47's copies of Fjalar's files include but 2.39's do not, directly
   or through another such header, and that Fjalar does not have.  The
   trial merge from 2.39 straight to 2.47 listed `bfd/elf-attrs.h`, `bfd/hidden.h`, `include/elf/kvx.h`,
   `include/elf/kvx_elfids.h`, `include/sframe-api.h`, `include/sframe.h`,
   and `include/ansidecl.h`, and, separately, `inttypes.h`, `zstd.h`, and
   `stdbool.h`, which are not in the release.  Also check whether 2.47's
   files call into new helper files (e.g. new code split out of `dwarf.c`).
   Copy any new needed headers from `include/` into
   `valgrind/fjalar/include/`; copy any from `bfd/` (such as
   `bfd/elf-attrs.h`) into `valgrind/fjalar/` and add them to
   `BINUTILS_FILES` in `merge-binutils.sh` and to `BINUTILS_FILES_RE` in
   `compare-warnings.sh`.  Add any new needed `.c` files
   to `FJALAR_SOURCES_COMMON` in `valgrind/fjalar/fjalar.am`.  (Do not edit
   `valgrind/fjalar/Makefile.am`, which `generate-fjalar-makefile.sh`
   regenerates at each Valgrind merge.)  (`demanguse.h` and the CTF headers
   were added this way in the 2.39 merge.)
   If the code that needs a new header is disabled, disable the `#include`
   under `#if 0` instead.  Remove headers that upstream deleted.
   - Known case: Binutils 2.40 added `readelf --sframe`, which includes
     `sframe-api.h` and calls into libsframe.  Fjalar does not need it:
     disable that code with `#if 0 // This code is not needed for Fjalar.`
     (as was done for CTF) rather than vendoring libsframe.
   - Binutils 2.40+ can decompress zstd-compressed debug sections, in code
     guarded by `#ifdef HAVE_ZSTD`.  Fjalar's build never defines
     `HAVE_ZSTD`:  Binutils' `configure` defines it in Binutils'
     `config.h`, which Fjalar does not use (Fjalar's `sysdep.h`, in
     `valgrind/fjalar/binutils-shim/`, includes Valgrind's `config.h`
     instead).  Make sure that
     code compiles out cleanly with `HAVE_ZSTD` undefined, rather than
     pulling in libzstd.
   - `dwarf.c`, `readelf.c`, and `elfcomm.c` include Fjalar's minimal
     `bfd.h`, `sysdep.h`, and `libiberty.h`, in
     `valgrind/fjalar/binutils-shim/`.  If 2.47's code uses a definition
     that one of them lacks, compilation fails; add the definition, taken
     from 2.47.  2.47 no longer uses `BFD_VMA_FMT`, so remove it, and
     `fprintf_vma` and its relatives, from the shim `bfd.h` if nothing uses
     them.

5. **Resolve conflicts** (expected mostly in `dwarf.c` and `readelf.c`),
   following "Hints to modifying dwarf.c and readelf.c".  A visual merge
   tool can help, e.g.
   `git -C $FJALAR mergetool --tool=meld valgrind/fjalar/dwarf.c`.
   - Keep `#if 0 // This code is not needed for Fjalar.` blocks disabled;
     new upstream code that only prints (e.g. new section dumpers) should go
     inside such blocks or be guarded.
   - Guard every new `printf`/`putchar` with `fjalar_debug` /
     `fjalar_debug_dump` (or `FJALAR_DPRINTF`); hoist side-effecting
     arguments (e.g. `read_uleb128`, `READ_ULEB`, `SAFE_BYTE_GET_AND_INC`)
     out of guarded `printf`s.
   - Do not replace libc calls with `VG_(...)` equivalents or `assert`
     with `tl_assert`; the shim `sysdep.h` and `assert.h` do that.
   - Make sure Fjalar's hooks in `dwarf.c` and `readelf.c` still run on
     every path.  The hooks are the calls to functions declared in
     `typedata.h`, `fjalar_dwarf.h`, `fjalar_include.h`, `fjalar_main.h`,
     and `GenericHashtable.h`, which build Fjalar's DWARF entries, symbol
     tables, and line-number table, such as the `harvest_*` functions,
     `add_comp_unit`, and `insertIntoFunctionSymbolTable`.
     `check-hook-counts.sh` (step 7) derives the hooks from those headers,
     so this plan does not list them.  Also keep the
     Fjalar functions that `dwarf.c` and `readelf.c` define for the rest of
     Fjalar:  `dwarf_reg_name` in `dwarf.c` and `process_elf_binary_data`
     in `readelf.c` (see "Current state").  Re-check every
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
   - Use `binutils-Fjalar.diff` as a checklist: a merge can lose a Fjalar
     change without reporting a conflict.
   - Areas to expect to need attention in 2.40-2.47:
     - DWARF 5 handling in `dwarf.c` (`.debug_rnglists`, `.debug_loclists`,
       `.debug_str_offsets`, `.debug_addr`, `DW_FORM_*x` forms, `DW_OP_*`
       additions), the main reason to upgrade, and where the hook check
       above matters most.
     - debuginfod (`HAVE_LIBDEBUGINFOD`): already conditionally compiled;
       ensure it stays undefined.
     - New `readelf` command-line options or global flags: Fjalar sets
       `do_debug_*` and related globals itself, in
       `process_elf_binary_data` at the end of `readelf.c`; check it for
       renamed or newly required globals.
     - Changed data structures in `dwarf.h` (for example `debug_info`,
       `dwarf_section`, `separate_info`) and types (upstream replaced `dwarf_vma`
       by `uint64_t` before 2.47): update the Fjalar edits inside `dwarf.c`
       and `readelf.c` that use them (see "Current state").
   - Review every new `if (fjalar_debug...)` guard for a side-effecting
     expression left inside it.
   - Confirm that no conflict markers remain
     (`grep -rn '^\(<<<<<<<\|=======\|>>>>>>>\|||||||\)' $FJALAR/valgrind/fjalar`
     prints nothing), and mark each file as resolved with `git add`.

6. **Build and fix warnings/errors.**  `make -C $FJALAR build`, then
   iterate with `make -C $FJALAR/valgrind/fjalar`.  Fix "implicit
   declaration" and "undefined reference" errors, from libc functions that
   the shim `sysdep.h` does not map yet, by adding a macro there.
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
   Finally, run `make -C $FJALAR/valgrind/fjalar install`.
   `make -C valgrind/fjalar` does not install the tool, but
   `make fjalar-test` (step 7) runs the installed one,
   `valgrind/inst/bin/valgrind`.

7. **Test.**  Run these from `$FJALAR` (`cd $FJALAR`).
   - In the last hop only, `./check-regtest.sh` — must report no
     unexpected failures, with no change to `regtest-expected/*.txt`.  This
     upgrade doesn't touch Valgrind, so any new failure is a bug in the
     merge (or an OS/compiler update; then re-run on the old sources to
     check).  In the other hops, rely on CI, which enforces the
     expected-failure lists when you push (the last bullet of this step).
   - `make fjalar-test`.
   - `(set -o pipefail; ./test-kvasir.sh 2>&1 | tee kvasir-after.log)` —
     compare with `kvasir-before.log`; the tests must pass with no goal-file changes.
     Superfluous output in `.out` diffs, or in a Kvasir `.decls` or
     `.dtrace` file, usually means an unguarded `printf`.
   - The regression tests may not exercise the newer DWARF paths, so also
     run Kvasir on the four binaries of step 2, as step 2 does, but writing
     into `/tmp/$USER/binutils/decls-after/`.  Delete and recreate that
     directory first, so that no file from a previous hop remains if
     Kvasir fails to write one.  Then
     run
     `diff -r /tmp/$USER/binutils/decls-before /tmp/$USER/binutils/decls-after`.
     The DWARF 4 files must not differ.  A DWARF 5 file may differ only
     where step 2 noted a difference between it and the DWARF 4 file of
     the same compiler, and only by becoming more like the DWARF 4 file;
     that is an improvement in DWARF 5 support, which step 8 records.  Any
     other difference is a regression.
   - Run with `--fjalar-debug-dump` on a DWARF 5 binary and compare
     against `readelf --debug-dump` from Binutils `$BUNEWVER` for sanity.
     The system `readelf` is usually from a different version (2.46 on
     Ubuntu 26.04, 2.41 on Rocky Linux 10), so build `$BUNEWVER`'s:
     `./build-binutils-readelf.sh $BUNEWVER` builds it and prints its path.
   - Before committing, run `./check-hook-counts.sh HEAD`.  It counts the
     calls of each hook (step 5) in the old and new `dwarf.c` and
     `readelf.c`, and prints each hook whose count changed, with the file
     and the old and new counts; explain each difference.  The old files
     are those of `HEAD`, which is the previous hop's commit (or, in the
     first hop, the commit where this branch started).  Without the `HEAD`
     argument, the script compares with the commit where this branch
     started, so a later hop that undid an earlier hop's change would
     report no difference.  The count omits `#if 0`
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
     caused an "undefined reference" link error in step 6, because the
     tool is linked with `-nodefaultlibs`.)
   - Commit the hop (see the note about hops above).  Then push the branch
     and confirm GitHub Actions CI passes (Ubuntu and Rocky Linux: build,
     regtest, and Kvasir jobs).

8. **Finish.**  (The last hop has already updated `valgrind/REVISION` to
   2.47.)
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
     - the checklist of upgrade-sensitive areas (step 5);
     - the DWARF 4 versus DWARF 5 comparison and the `nm` check for zstd,
       SFrame, and debuginfod code (step 7).
     The doc already uses the scripts of steps 3, 6, and 7.  If the
     `git cherry-pick` merge of step 3 caused problems in practice, say
     why, and change `merge-binutils.sh` and the doc.
     Update the list of compiler warning flags if it changed.  Rebuild
     with `make doc` (which `test.sh` runs in CI) to confirm that the
     document still formats.
   - If step 2 created a local `regtest-expected/<os>.txt`, delete it
     before the last commit (see the note about hops above).
   - Commit the doc and changelog updates (the whole branch is one PR, whose
     title is "Upgrade Binutils (readelf) from 2.39 to 2.47").
     Delete `regtest-<os>.log`, `regtest-<os>-post.log`, and
     `regtest-<os>-observed.txt` (ignored by git).
   - Push the branch and confirm GitHub Actions CI passes, as in step 7.

## Risks

- Large upstream refactorings in `dwarf.c` (DWARF 5 / split-DWARF / debuginfod
  handling) could make the merge produce many conflicts; this is the main
  reason for the stepwise upgrade.
- Silent loss of a Fjalar hook in a conflicted hunk would show up only as
  missing variables in Kvasir output.  `check-hook-counts.sh` (step 7)
  catches a lost or duplicated call, but not a call that a merge moved onto
  the wrong path, so the Kvasir regression tests are the essential check.
- An unguarded side-effecting expression inside a guarded `printf` changes
  parsing only when debugging is off.  Mitigation: review every new guard
  (step 5).
- Code for zstd, SFrame, or debuginfod could be compiled in.  Mitigation:
  the `nm` check (step 7).  A call into a system library that Fjalar does
  not link fails the link (step 6).
- The later Valgrind upgrade may enable additional warning flags, which will
  hit `readelf.c`/`dwarf.c` again.  Expect a second round of warning fixes
  there; it does not mean this merge was done wrong.
