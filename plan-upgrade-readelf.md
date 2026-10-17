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

## Key decision: one jump or stepwise?

Eight releases is the largest gap so far (previous merges: 2.35.1 -> 2.36.1 ->
2.37 -> 2.39).  `dwarf.c` and `readelf.c` are where nearly all conflicts occur.

Recommendation: first try a single 2.39 -> 2.47 dry run.  If `dwarf.c` or
`readelf.c` shows more rejected hunks than can reasonably be hand-merged, fall
back to two steps (2.39 -> 2.43, then 2.43 -> 2.47), building and running the
Kvasir tests after each step.

## Steps

1. **Preparation** (separate branch, e.g. `binutils-2.47`; do not combine with
   the Valgrind upgrade).
   - `git pull` both `fjalar` and `daikon`; ensure clean trees.
   - Make sure the system has `binutils-dev` / `binutils-devel` (for `bfd.h`).

2. **Baselines** (before touching any source).
   - `make clean build && make test 2>&1 | tee test-before.log`
     (Valgrind regtest baseline).
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
   export BUOLDVER=2.39 BUNEWVER=2.47
   export BUOLD=binutils-$BUOLDVER BUNEW=binutils-$BUNEWVER
   mkdir -p ~/tmp/binutils && cd ~/tmp/binutils
   wget https://ftp.gnu.org/gnu/binutils/$BUOLD.tar.gz https://ftp.gnu.org/gnu/binutils/$BUNEW.tar.gz
   tar xzf $BUOLD.tar.gz && tar xzf $BUNEW.tar.gz
   diff -ur $BUOLD/include $BUNEW/include > include.patch
   diff -u  $BUOLD/libiberty/dwarfnames.c $BUNEW/libiberty/dwarfnames.c >> include.patch
   diff -u -x'Makefile*' $BUOLD/binutils $BUNEW/binutils > binutils.patch
   ```
   Also create the reference diffs (Fjalar vs. pristine 2.39) for
   `dwarf.c` and `readelf.c` as described in the doc.  Verify the tarballs'
   signatures (`.sig` files) while downloading.

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

5. **Apply the patches**, one at a time, dry run first, using
   `--merge=diff3` so conflicts are inline:
   ```sh
   cd $INV/fjalar/valgrind/fjalar
   cp -p dwarf.c dwarf.c.pre-merge; cp -p readelf.c readelf.c.pre-merge
   SKIPFILTER='/can.t find file to patch/ {skip=1} !skip && !/hunks? ignored/ {print} /Skipping patch\./ {skip=0}'
   patch -p1 -lu -f --dry-run < ~/tmp/binutils/include.patch | awk "$SKIPFILTER"
   patch -p1 -lu -f --merge=diff3 < ~/tmp/binutils/include.patch | awk "$SKIPFILTER"
   patch -p2 -lu -f -F3 --dry-run < ~/tmp/binutils/binutils.patch | awk "$SKIPFILTER"
   patch -p2 -lu -f -F3 --merge=diff3 < ~/tmp/binutils/binutils.patch | awk "$SKIPFILTER"
   ```
   The `awk` filter hides the messages for Binutils files that Fjalar doesn't
   use.  The `.pre-merge` copies are for a visual merge tool, e.g.
   `meld ~/tmp/binutils/$BUNEW/binutils/dwarf.c dwarf.c dwarf.c.pre-merge`.

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
     changes from #73/#76.
   - Remove `.rej` files (and any `.orig` files that `patch` creates) as you
     go.  Delete the `.pre-merge` copies once the merge is complete.

7. **Build and fix warnings/errors.**  `make -C $INV/fjalar build`, then
   iterate with `make -C valgrind/fjalar`.  Fix "implicit declaration" and
   "undefined reference" errors (missed `VG_()` wrappers).  Reduce new
   warnings from Valgrind's stricter flags where practical.
   Also check against the system `bfd.h` on both Rocky Linux and Ubuntu
   (the #63 workaround may need to change).

8. **Test.**
   - `make test 2>&1 | tee test-after.log` — compare with
     `test-before.log`; results should match.
   - `make fjalar-test`.
   - `./test-kvasir.sh 2>&1 | tee kvasir-after.log` — compare with
     `kvasir-before.log`.  Superfluous output in `.out` diffs usually means
     an unguarded `printf`.
   - Spot-check `--fjalar-debug-dump` style output on a DWARF 5 binary
     compiled by the current gcc and clang.
   - Push the branch and confirm GitHub Actions CI passes (Ubuntu and
     Rocky Linux, both build and Kvasir jobs).

9. **Finish.**
   - Update `valgrind/REVISION`: the `# Binutils version 2.47, released ...`
     comment and `export BINUTILS_VERSION=2.47`.
   - Note the upgrade in `$INV/daikon/doc/CHANGELOG.md` if user-visible.
   - Update `doc/valgrind-merge.texinfo` with anything learned (e.g. stale
     URLs, new hints such as the SFrame handling).
   - Commit (one PR); keep `include.patch`, `binutils.patch`, and the
     Fjalar-vs-binutils diffs for reference.

## Risks

- Large upstream refactorings in `dwarf.c` (DWARF 5 / split-DWARF / debuginfod
  handling) could make the textual patch apply poorly; this is the main reason
  for the stepwise fallback.
- Silent loss of a Fjalar hook in a conflicted hunk would show up only as
  missing variables in Kvasir output, so the Kvasir regression tests are the
  essential check.
- The later Valgrind upgrade may enable additional warning flags, which will
  hit `readelf.c`/`dwarf.c` again.  Expect a second round of warning fixes
  there; it does not mean this merge was done wrong.
