# Plan: upgrade Fjalar's readelf code from Binutils 2.39 to 2.47

Reference procedure: `doc/valgrind-merge.texinfo`, chapter "Updating Readelf
from Binutils".  This plan applies that procedure to the current situation and
notes where it needs adjusting.

Below, `$INV/fjalar` means the Fjalar tree being upgraded.

## Ordering: do this before the Valgrind upgrade

Do this upgrade first, before `plan-upgrade-valgrind.md`, and finish it
completely (merged, CI green) before starting the Valgrind upgrade.  Reasons:

- It is smaller and self-contained: about a dozen files in `valgrind/fjalar/`,
  with conflicts concentrated in `dwarf.c` and `readelf.c`.
- Its failures are easy to attribute (spurious output or missing variables in
  Kvasir output).  Valgrind-merge failures are subtler (crashes, wrong
  comparability, DynComp panics), so it's better to start that merge from a
  known-good tree where any regression is clearly due to Valgrind.
- Recent work (#73, #76) had to extend `dwarf.c` to handle DWARF 3/4 and
  Rust.  Newer Binutils parses DWARF constructs that current compilers emit,
  so this upgrade likely delivers more user value per unit of effort.

Exception: if a user is currently blocked by something only newer Valgrind
fixes (an unsupported instruction or syscall on a new distro, or DynComp
panics like #79), do the Valgrind upgrade first.

## Current state

- `valgrind/REVISION`: `BINUTILS_VERSION=2.39` (released 2022-08-05).
- Latest release on ftp.gnu.org: **2.47** (2.40-2.46.1 were skipped).
- Binutils-derived files in `valgrind/fjalar/`:
  - `readelf.c` (~23.4k lines), `dwarf.c` (~13.4k), `dwarf.h`, `elfcomm.c/h`,
    `bucomm.h`, `demanguse.h`
  - `include/` (`dwarf2.def`, `dwarf2.h`, `demangle.h`, `ctf.h`, `ctf-api.h`,
    `safe-ctype.h`, `elf/*.h`)
  - `libiberty/dwarfnames.c`
- Fjalar-local edits must survive the merge.  They are already in the Fjalar
  copy, so merging the upstream 2.39->2.47 changes into it preserves them;
  just don't clobber them while resolving conflicts.  The complete checklist
  is the Fjalar-vs-pristine-2.39 diffs created in step 3; that includes older
  edits and the edits made during the Valgrind 3.23 merge (`f15d19e3`, #72).
  Edits since the 2.39 merge include:
  - `55ae3f48` define PTR (#62)
  - `be9be5f0` fix for newer versions of bfd.h (#63)
  - `1ca71b1c` Support DWARF 3 (#73)
  - `d8723ef7` spelling corrections (#75)
  - `95516533` Support Rust and DWARF 3 & 4 (#76)

## Key decision: one jump or stepwise?

Eight releases is the largest gap so far (previous merges: 2.35.1 -> 2.36.1 ->
2.37 -> 2.39).  `dwarf.c` and `readelf.c` are where nearly all conflicts occur.

Recommendation: first try a single 2.39 -> 2.47 dry run.  If `dwarf.c` or
`readelf.c` shows more conflicts than can reasonably be hand-merged, fall
back to two steps (2.39 -> 2.43, then 2.43 -> 2.47), building and running the
Kvasir tests after each step.

## Steps

1. **Preparation** (separate branch, e.g. `binutils-2.47`; do not combine with
   the Valgrind upgrade).
   - `git pull` both `fjalar` and `daikon`; ensure clean trees.
   - Make sure the system has `binutils-dev` / `binutils-devel` (for `bfd.h`).

2. **Baselines** (before touching any source).
   - `make build && ./check-regtest.sh` (Valgrind regtest baseline;
     must report no unexpected failures).  Do not run `make clean` first,
     because it fails until `make build` has created `valgrind/Makefile`.
     If this machine's OS has no
     `regtest-expected/<os>.txt`, create a local one with
     `./check-regtest.sh --log regtest-<os>.log --update` and don't commit it.
   - `./test-kvasir.sh 2>&1 | tee kvasir-before.log`
     (Kvasir baseline; record any pre-existing failures).
   - Run the Kvasir tests via `./test-kvasir.sh`, which points
     `$DAIKONDIR/fjalar` at this tree.  Running
     `$INV/daikon/tests/kvasir-tests` or `make daikon-test` directly builds
     whatever `$INV/daikon/fjalar` points to (by default `$INV/fjalar`, which
     may be a different clone than the one being upgraded).  If you run them
     directly, first check `readlink -f $INV/daikon/fjalar`.

3. **Create patch files.**

   ```sh
   export BUNEWVER=2.47
   $INV/fjalar/generate-binutils-patch-files.sh $BUNEWVER
   ```

   The script downloads 2.39 and 2.47 into `/tmp/$USER/binutils/`, verifies
   their signatures, and extracts them.  It writes `include.patch` and the
   reference diffs (Fjalar vs. pristine 2.39, `*-binutils-vs-fjalar.diff`)
   to `/tmp/$USER/binutils/2.39-2.47/`.

4. **Check for new upstream dependencies.**  Before patching, check whether
   2.47's `readelf.c`/`dwarf.c`/`elfcomm.c` `#include` any header (under
   `include/`, `include/elf/`, or `binutils/`) that Fjalar does not yet have,
   and whether they call into new helper files (e.g. new code split out of
   `dwarf.c`).  Copy any new needed headers into `valgrind/fjalar/include/`
   and add any new needed `.c` files to `FJALAR_SOURCES_COMMON` in
   `valgrind/fjalar/fjalar.am`.  (Do not edit `valgrind/fjalar/Makefile.am`,
   which `generate-fjalar-makefile.sh` regenerates at each Valgrind merge.)
   (`demanguse.h` and the CTF headers were added this way in the 2.39 merge.)
   - Known case: Binutils 2.40 added `readelf --sframe`, which includes
     `sframe-api.h` and calls into libsframe.  Fjalar does not need it:
     disable that code with `#if 0 // This code is not needed for Fjalar.`
     (as was done for CTF) rather than vendoring libsframe.
   - New `include/elf/*.h` files (e.g. for new architectures) are not in
     `include.patch`, because `diff -ur` without `-N` lists them only as
     "Only in ..."; copy those that 2.47's `readelf.c` includes.

5. **Merge**, dry run first:

   ```sh
   $INV/fjalar/merge-binutils.sh --dry-run $BUNEWVER
   $INV/fjalar/merge-binutils.sh $BUNEWVER
   ```

   The script applies `include.patch` with `patch --merge=diff3` and merges
   each Binutils-derived file in `valgrind/fjalar/` with
   `git merge-file --diff3`, so conflicts are inline.  It prints the number
   of conflicts in each file, and how to undo the merge.  It saves each
   merged file's previous contents as `FILE.pre-merge`, for a visual merge
   tool, e.g.:

   ```sh
   cd $INV/fjalar/valgrind/fjalar
   meld /tmp/$USER/binutils/binutils-$BUNEWVER/binutils/dwarf.c dwarf.c dwarf.c.pre-merge
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
   - Make sure Fjalar's harvesting hooks in `dwarf.c` (the calls that build
     Fjalar's DWARF entries, see `fjalar_dwarf.c`/`typedata.c`) still run on
     every path, especially for DWARF 5 forms and any new `DW_FORM_*`,
     `DW_AT_*`, `DW_OP_*` handling.  Re-check the DWARF 3/4 and Rust
     changes from #73/#76.  `$INV/fjalar/check-hook-counts.sh` reports each
     hook whose number of calls in `dwarf.c` or `readelf.c` changed; explain
     each difference.
   - Use the `*-binutils-vs-fjalar.diff` files as a checklist: a merge can
     lose a Fjalar change without reporting a conflict.
   - Delete the `.pre-merge` copies once the merge is complete.

7. **Build and fix warnings/errors.**  `make -C $INV/fjalar build`, then
   iterate with `make -C valgrind/fjalar`.  Fix "implicit declaration" and
   "undefined reference" errors (missed `VG_()` wrappers).  Reduce new
   warnings from Valgrind's stricter flags where practical;
   `compare-warnings.sh --binutils` lists the warnings that are new since the
   baseline build (see "Hints to modifying dwarf.c and readelf.c").
   Also check against the system `bfd.h` on both Rocky Linux and Ubuntu
   (the #63 workaround may need to change).

8. **Test.**  Run these from `$INV/fjalar` (`cd $INV/fjalar`; step 5 left
   the shell in `valgrind/fjalar`).
   - `./check-regtest.sh` — must report no unexpected failures, with no
     change to `regtest-expected/*.txt`.  This upgrade doesn't touch
     Valgrind, so any new failure is a bug in the merge (or an OS/compiler
     update; then re-run on the old sources to check).
   - `make fjalar-test`.
   - `./test-kvasir.sh 2>&1 | tee kvasir-after.log` — compare with
     `kvasir-before.log`.  Superfluous output in `.out` diffs usually means
     an unguarded `printf`.
   - Spot-check `--fjalar-debug-dump` style output on a DWARF 5 binary
     compiled by the current gcc and clang, against the output of 2.47's
     `readelf --debug-dump`.  `$INV/fjalar/build-binutils-readelf.sh 2.47`
     builds that `readelf` and prints its path.
   - Push the branch and confirm GitHub Actions CI passes (Ubuntu and
     Rocky Linux: build, regtest, and Kvasir jobs).

9. **Finish.**
   - Update `valgrind/REVISION`: the `# Binutils version 2.47, released ...`
     comment and `export BINUTILS_VERSION=2.47`.
   - Note the upgrade in `$INV/daikon/doc/CHANGELOG.md` if user-visible.
   - Update `doc/valgrind-merge.texinfo` with anything learned (e.g. stale
     URLs, new hints such as the SFrame handling).
   - Commit (one PR).  Delete `regtest-<os>.log`,
     `regtest-<os>-post.log`, and `regtest-<os>-observed.txt` (ignored by git).

## Risks

- Large upstream refactorings in `dwarf.c` (DWARF 5 / split-DWARF / debuginfod
  handling) could make the merge produce many conflicts; this is the main
  reason for the stepwise fallback.
- Silent loss of a Fjalar hook in a conflicted hunk would show up only as
  missing variables in Kvasir output.  `check-hook-counts.sh` catches a lost
  or duplicated call, but not a call that a merge moved onto the wrong path,
  so the Kvasir regression tests are the essential check.
- The later Valgrind upgrade may enable additional warning flags, which will
  hit `readelf.c`/`dwarf.c` again.  Expect a second round of warning fixes
  there; it does not mean this merge was done wrong.
