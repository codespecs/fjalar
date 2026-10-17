# Plan: upgrade Fjalar's Valgrind from 3.23.0 to 3.27.1

Reference procedure: `doc/valgrind-merge.texinfo` (chapters "Getting Started"
through "Committing").  This plan applies that procedure to the current
situation and notes where it needs adjusting.

Below, `$INV/fjalar` means the Fjalar tree being upgraded.  It must actually be
at `$INV/fjalar`, because `generate-patch-files.sh` and `make git-update`
hard-code that layout (`fjalar/valgrind`, `../coregrind.patch`).

## Ordering: do this after the readelf upgrade

Do the Binutils/readelf upgrade (`plan-upgrade-readelf.md`) first, and finish
it completely (merged, CI green) before starting this one.  That plan's
"Ordering" section gives the reasons and the exception.

## Current state

- `valgrind/REVISION`: Valgrind 3.23.0 (released 2024-04-26).
- Latest tag at sourceware.org: **VALGRIND_3_27_1**
  (skipped: 3.24.0, 3.25.0, 3.25.1, 3.26.0, 3.27.0).
- Precedent: the last merge (f15d19e3, #72) jumped 3.19.0 -> 3.23.0 in one
  step, so a single 3.23.0 -> 3.27.1 jump is reasonable.
- Fjalar-local changes made since the 3.23 merge, by where they matter:
  - Memcheck-derived files, so they can conflict in step 6:
    `1ca71b1c` (#73) changed `mc_translate.c` and `memcheck.h`.
  - DynComp, so step 7 must keep them (no conflict expected, since
    `kvasir/` is not patched): `b2c735d7` (#79) `Iop_64x4toV256` in
    `dyncomp_translate.c`.
  - Other changes since then (#76, #80, the rest of #73) touch only
    Fjalar's own files and Binutils-derived files, which this merge does not
    patch.
  - The complete checklist of Fjalar changes to upstream files is
    `coregrind-Fjalar.diff` and `memcheck-Fjalar.diff` (step 4).

## Steps

1. **Preparation** (separate branch, e.g. `valgrind-3.27.1`; do not combine with
   the Binutils/readelf upgrade, which should already be merged).
   - `git pull` both `fjalar` and `daikon`; ensure no local or outgoing changes.
   - Record baselines on current sources:
     `make test 2>&1 | tee test-before.log` and
     `./test-kvasir.sh 2>&1 | tee kvasir-before.log`.
     Use `./test-kvasir.sh`, which points `$DAIKONDIR/fjalar` at this tree.
     Running `$INV/daikon/tests/kvasir-tests` or `make daikon-test` directly
     builds whatever `$INV/daikon/fjalar` points to; if you do that, first
     check `readlink -f $INV/daikon/fjalar`.
   - `make very-clean`; review/delete untracked files
     (`git ls-files --others --exclude-standard`).

2. **Get the trees.**
   ```sh
   export VOLDVER=VALGRIND_3_23_0 VNEWVER=VALGRIND_3_27_1
   cd $INV
   git clone -b $VOLDVER --depth 1 https://sourceware.org/git/valgrind.git valgrind-old
   git clone -b $VNEWVER --depth 1 https://sourceware.org/git/valgrind.git valgrind-new
   ```
   Remove from `fjalar/valgrind` the files listed by
   `diff -qrb -x.git valgrind-old valgrind-new | grep "Only in valgrind-old"`.

3. **Baseline.**  Never build in `valgrind-old` or `valgrind-new` themselves:
   `generate-patch-files.sh` refuses to run if either contains changes or
   untracked files, such as build products (`*.o`, `Makefile`, `config.h`,
   test binaries, `inst/`).  Otherwise they would end up in
   `coregrind.patch` and then be `git add`ed by `make git-update`.  The
   error message gives the `git reset`/`git clean` command that makes a tree
   pristine again.  Build a copy instead:
   ```sh
   rm -rf valgrind-new-build
   cp -a valgrind-new valgrind-new-build && cd valgrind-new-build
   ./autogen.sh && ./configure --prefix=$(pwd)/inst
   make all install && make regtest > test.log 2>&1
   ```
   Save the summary at the end of `test.log` for comparison.

4. **Create the diffs.** Run `$INV/fjalar/generate-patch-files.sh`, producing
   `coregrind.patch`, `memcheck.patch`, `coregrind-Fjalar.diff`,
   `memcheck-Fjalar.diff`.  The script checks that `valgrind-old` and
   `valgrind-new` are pristine clones at `$VOLDVER` and `$VNEWVER`.

5. **Coregrind merge.**
   - `cd fjalar/valgrind; patch -p1 -lu --dry-run < $INV/coregrind.patch`,
     then for real.
   - Fix zero-length `.exp` files and lost execute bits (the two `find`
     commands in the doc).
   - Resolve `*.rej` using `coregrind-Fjalar.diff` and the "Valgrind
     modifications" appendix as a checklist.  In particular, verify each
     Fjalar change still exists after the merge:
     `configure.ac`, top-level `Makefile.am`, `m_libcbase.c`/`pub_tool_libcbase.h`
     (`strnlen`), `m_libcfile.c`/`pub_tool_libcfile.h` (`mkdir`, `fcntl`),
     `m_machine.c`/`pub_tool_machine.h`/`pub_core_machine.h` (extra registers),
     `pub_core_threadstate.h` (extra shadow area), `m_scheduler/scheduler.c`
     (shadow-size assertion), VEX `guest_{amd64,x86}_helpers.c`,
     `host_amd64_defs.c`, `host_generic_reg_alloc2.c` (and check
     `host_generic_reg_alloc3.c`, which is now the default allocator),
     `libvex.h`, `libvex_ir.h`, `none/tests/Makefile.am`,
     `tests/check_headers_and_includes`.
   - Pay special attention to any upstream change to guest-state layout
     (`libvex_guest_amd64.h`, `libvex_guest_x86.h`) or to the shadow-area
     size/alignment checks, since Fjalar enlarges the shadow area.

6. **Memcheck merge** into `valgrind/fjalar/`.
   - `cd fjalar/valgrind/fjalar; patch -p2 -lu --dry-run < $INV/memcheck.patch`,
     then for real (try `-F3` only if needed, and review its results).
   - Resolve `*.rej`.  Remember part of `mc_translate.c` lives in
     `fjalar/mc_translate.h`.  Preserve the #73 edits to `mc_translate.c`
     and `memcheck.h`.
   - In `mc_translate.c`'s `MC_(instrument)`, check that every case has
     matching DynComp code and that new cases get a DynComp counterpart.
   - Check `mc_main.c` still has Fjalar's options/version info.
   - New memcheck source files: decide whether Fjalar needs them; if so,
     add to `valgrind/fjalar/Makefile.am`.

7. **DynComp / Fjalar / Kvasir updates.**
   - `diff -b valgrind-old/VEX/pub/libvex_ir.h valgrind-new/VEX/pub/libvex_ir.h`
     and hand-port relevant `memcheck.patch` hunks into
     `fjalar/kvasir/dyncomp_translate.c` (`_DC` functions).
   - For every new or renamed `IROp`, `IRExpr`, or `IRStmt` kind relevant to
     amd64/x86, add handling in the `expr2tags_*_DC` functions (see the
     #79 `Iop_64x4toV256` fix for the pattern).  Search for panics/`default:`
     cases that would now be hit.  Most changes for other architectures can
     be ignored.
   - Check NEWS for 3.24–3.27 for tool-API changes (e.g. changes to
     `VG_(needs_*)`, debuginfo, `pub_tool_*.h` signatures, client-request
     numbering) and update Fjalar callers.
   - Check that Fjalar's use of Valgrind's debuginfo reader
     (`coregrind/m_debuginfo`) and its own `readelf.c`/`dwarf.c` don't now
     conflict (duplicate symbols, changed `VG_()` libc names).

8. **Build.** `make -C $INV/fjalar build`; fix compilation errors and new
   warnings (newer Valgrind may enable additional warning flags; Binutils-
   derived code is the usual source).  Test with both a current gcc and the
   compilers in the CI containers.

9. **Test.**
   - `make test 2>&1 | tee test-after.log` — compare with the step-3
     baseline; they should be similar.
   - `make fjalar-test`.
   - `./test-kvasir.sh 2>&1 | tee kvasir-after.log` — compare with
     `kvasir-before.log` from step 1.  Address-related diffs
     (`<STACK_ADDR>` etc.) may require updating `clean-output.pl`.
   - Push the branch and confirm GitHub Actions CI passes (Ubuntu and
     Rocky Linux 10 build and Kvasir jobs).

10. **Finish.**
    - Update first line of `valgrind/REVISION`
      (`# Valgrind version 3.27.1, released ...`).
    - Add names of new Valgrind test drivers to `.gitignore`
      ("Ignore generated test drivers" section).
    - `make git-update > git.script`, review, run.
    - Document user-visible changes in `$INV/daikon/doc/CHANGELOG.md`.
    - Update `doc/valgrind-merge.texinfo`: regtest baseline output, dates/OS
      versions, and any new pitfalls.
    - Commit as one PR; save the patch/diff files and `valgrind-new` (it
      becomes `valgrind-old` for the next merge, after
      `git -C valgrind-old reset --hard && git -C valgrind-old clean -fdx`;
      delete `valgrind-new-build`).

## Risks

- **Shadow-area / guest-state changes** in VEX or coregrind would break
  Fjalar's extra shadow state in subtle ways (crashes or wrong comparability),
  not compile errors.
- **New IROps** used by modern compilers (AVX/AVX2 and others on amd64) can
  make DynComp panic at run time; the Kvasir tests may not exercise them, so
  also run Kvasir/DynComp on a few programs compiled with `-O2 -march=native`.
- **Build-system changes** (`Makefile.all.am`, `Makefile.tool.am`,
  `configure.ac`) can silently drop Fjalar from the build or change flags.
- **New warning flags** will hit `readelf.c`/`dwarf.c`, which were just
  merged in the readelf upgrade; expect a second round of warning fixes
  there.
