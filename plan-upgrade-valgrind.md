# Plan: upgrade Fjalar's Valgrind from 3.23.0 to 3.27.1

Reference procedure: `doc/valgrind-merge.texinfo` (chapters "Getting Started"
through "Committing").  This plan applies that procedure to the current
situation and notes where it needs adjusting.

Below, `$FJALAR` is the Fjalar clone being upgraded (see step 1).
(`merge-valgrind.sh` merges into the tree that contains it, wherever that
is.)

## Ordering: do this after the readelf upgrade

Do the Binutils/readelf upgrade (`plan-upgrade-readelf.md`) first, and finish
it completely (landed, CI green) before starting this one.  That plan's
"Ordering" section gives the reasons and the exception.

The preparation in `plan-pre-upgrade.md` must also be done; this plan
assumes items 1 (expected regtest failures enforced in CI) and 3
(DynComp scan).

## Scope

Conceptually there are three merges, which must be done together because
Memcheck and DynComp depend tightly on Valgrind core:

1. **Coregrind** (everything under `valgrind/` except `valgrind/fjalar/`):
   Valgrind core, VEX, other tools, tests, build system.  Fjalar's
   modifications are listed in appendix "Valgrind modifications" of the
   texinfo document; the most important are the extra shadow guest state
   (`vex_extra_shadow[4]` in `coregrind/pub_core_threadstate.h`, plus the
   alignment assertions in `coregrind/m_scheduler/scheduler.c` and the
   spill-area size calculations in `VEX/priv/host_generic_reg_alloc2.c` and
   `host_generic_reg_alloc3.c`), extra guest registers in
   `VEX/pub/libvex*.h` and `VEX/priv/guest_{amd64,x86}_helpers.c`, extra
   `VG_()` libc functions, and `configure.ac` / `Makefile.am` changes that
   add the `fjalar` tool.
2. **Memcheck -> Fjalar**: `valgrind/fjalar/mc_*.c`, `mc_include.h`,
   `memcheck.h` are derived from `valgrind/memcheck/`.  `mc_translate.c`
   contains a DynComp counterpart for each case of `MC_(instrument)`; part of
   the original is in `fjalar/mc_translate.h`.
3. **Memcheck -> DynComp**: `valgrind/fjalar/kvasir/dyncomp_translate.c` is
   derived from `memcheck/mc_translate.c` with `_DC` renaming; it must be
   updated by hand, using upstream's changes to `mc_translate.c` as a guide
   (step 7).

## Current state

- `valgrind/REVISION`: Valgrind 3.23.0 (released 2024-04-26).
- Latest tag at sourceware.org (as of 2026-10-10): **VALGRIND_3_27_1**
  (skipped: 3.24.0, 3.25.0, 3.25.1, 3.26.0, 3.27.0).
- Precedent: the last merge (f15d19e3, #72) jumped 3.19.0 -> 3.23.0 in one
  step (856 files changed), so a single 3.23.0 -> 3.27.1 jump is reasonable.
  Hopping through every release would multiply the manual DynComp work,
  because `mc_translate.c` and `dyncomp_translate.c` would have to be
  revisited five times.  Fall back to a hop at 3.25.1 only if the Memcheck
  conflicts are unmanageable.
- Fjalar-local changes made since the 3.23 merge, by where they matter:
  - Memcheck-derived files, so they can conflict in step 6:
    `1ca71b1c` (#73) changed `mc_translate.c` and `memcheck.h`,
    `2377944a` (#97) changed `mc_main.c`, and `a671ce4c` (#90, register
    parameters) changed `mc_main.c` and `mc_include.h`.
  - Coregrind/upstream files, so they can conflict in step 5: `42632185`
    (#84) backported an upstream fix for `$(nproc)` in
    `auxprogs/Makefile.am`.  3.27.1 has the same line, so take upstream's
    version; after the merge, that file no longer differs from upstream.
    Likewise, `f57698c1` (#102) backported upstream fixes to
    `drd/tests/swapcontext.c`, `helgrind/tests/tc17_sembar.c`, and
    `none/tests/bug234814.c`, so that they build with GCC 15; take
    upstream's versions.
  - DynComp, so step 7 must keep them (no conflict expected, since
    upstream has no `kvasir/`): `b2c735d7` (#79) `Iop_64x4toV256` and
    `125330a0` (#88) vector shifts, `d3b71509` (#85,
    `--dyncomp-unhandled-ops`), and `225fae19` (#86, tag 0 for unary
    operations whose result is a mask or count), in `dyncomp_translate.c`;
    `8cd25174` (#104, comparison tags merged with a dirty call),
    `1ff7ffe4` (#107, no helper-call merges under
    `--dyncomp-interactions=none`), `7c4b6598` (#106, chained helper-call
    merges), `54b935a6` (#126, a comment on the dirty-call merge),
    `ea8a7103` (#116, clean intermediate helper-call merges), and
    `65f721f0` (#87, explicit handling of every unary operation), in
    `dyncomp_translate.c`;
    `a4d693e1` (#114, instruction address only when tracing) and
    `ab0b6145` (#108, `WEAK_FRESH_TAG` check), in `dyncomp_main.c`.
  - Open PRs to land before this upgrade (as of 2026-10-20):
    - DynComp, `dyncomp_translate.c`:  #111, #115, #117, #119, #120,
      #122, #123, and #125.  Because #87 handles every unary operation
      explicitly, new IROps in 3.24-3.27 reach the `default` cases of all
      four `expr2tags_*_DC` functions, and
      `--dyncomp-unhandled-ops=warn` lists them all in one run (step 7).
    - Memcheck-derived files, so they can conflict in step 6:  #115,
      #117, #119, #120, and #122 change `mc_translate.c` and
      `mc_translate.h`.
    - A script that this plan uses:  #132 (`check-regtest.sh --log` takes
      the operating system from the log's name).
    - Other open PRs may have been opened since.  To list the open PRs
      that change files under `valgrind/`:

      ```sh
      gh pr list -R codespecs/fjalar --json number,files --jq \
        '.[] | select(any(.files[]; .path | startswith("valgrind/")))
             | .number'
      ```

  - Other changes since then (#76, #80, #89, #91, #94, the rest of #73)
    touch only Fjalar's own files and Binutils-derived files, which this
    merge does not change.
  - The complete checklist of Fjalar changes to upstream files is
    `coregrind-Fjalar.diff` and `memcheck-Fjalar.diff` (step 4).

## Steps

1. **Preparation** (separate branch, e.g. `valgrind-3.27.1`; do not combine with
   the Binutils/readelf upgrade, which should already have landed).
   - Work in a new clone, because each working directory is dedicated to
     one branch: clone Fjalar from GitHub into, e.g.,
     `$INV/fjalar-branch-valgrind-3.27.1`, and create the branch there.
     Set `FJALAR` to that clone, e.g.,
     `FJALAR=$INV/fjalar-branch-valgrind-3.27.1`; the commands below use
     it.

   - `git pull` both `fjalar` and `daikon`; ensure no local or outgoing changes.
   - Record baselines on current sources, from the new clone
     (`cd $FJALAR`):
     `(set -o pipefail; make build 2>&1 | tee build-before.log)` (save the
     log, to compare warnings after the merge); `./check-regtest.sh`, which
     needs the build (must report no unexpected failures; if this machine's
     OS has no `regtest-expected/<os>.txt`, create a local, uncommitted one
     with `--update`); and `make fjalar-test`.
   - Run the Kvasir tests with `./test-kvasir.sh 2>&1 | tee kvasir-before.log`
     (step 9 compares with this log).  `./test-kvasir.sh` temporarily points
     `$DAIKONDIR/fjalar` at this tree (it restores the old link on exit, and
     refuses to run if `$DAIKONDIR/fjalar` is a directory rather than a
     symbolic link; then set `DAIKONDIR` to another, possibly nonexistent,
     directory).  Do not use `make daikon-test`: it ignores `$DAIKONDIR` and
     builds whatever `../daikon/fjalar` points to, which may be a different
     clone.  Running `$INV/daikon/tests/kvasir-tests` directly has the same
     problem; if you do that, first check `readlink -f $INV/daikon/fjalar`.
   - `make very-clean`; review/delete untracked files
     (`git ls-files --others --exclude-standard`), except
     `regtest-expected/<os>.txt` if you created it above:  step 9 compares
     against it.

2. **Get the trees.**

   ```sh
   export VOLDVER=VALGRIND_3_23_0 VNEWVER=VALGRIND_3_27_1
   VALGRIND_GIT=https://sourceware.org/git/valgrind.git
   [ -d $INV/valgrind-old ] \
     || git clone -b $VOLDVER --depth 1 $VALGRIND_GIT $INV/valgrind-old
   rm -rf $INV/valgrind-new
   git clone -b $VNEWVER --depth 1 $VALGRIND_GIT $INV/valgrind-new
   ```

   Step 10 of the previous merge kept that merge's `valgrind-new` as
   `valgrind-old`, so reuse it if it exists; `merge-valgrind.sh` (step 4)
   checks that it is at `$VOLDVER`.

   Correct the files of earlier merges, following section "Correct the
   files of earlier merges" of `doc/valgrind-merge.texinfo`.
   `$FJALAR/list-file-discrepancies.sh $INV/valgrind-old` lists
   files that Fjalar tracks but `valgrind-old` lacks (remove those that
   Fjalar should not have); Memcheck files in `valgrind/fjalar` that
   `valgrind-old` lacks (keep Fjalar's own, such as `mc_translate.h`);
   Memcheck files that `valgrind-old` has but `valgrind/fjalar` lacks (copy
   them, because Fjalar builds every Memcheck source file); and files that
   `valgrind-old` has but Fjalar does not track, such as empty files and
   files that match `.gitignore` (add those that Fjalar should have).
   Commit these corrections before merging, because
   `merge-valgrind.sh` requires a clean work tree.  (The merge handles the
   files that upstream added or removed since `$VOLDVER`.)

3. **Baseline.**  First install `gdb` and the glibc debuginfo package;
   without them, most `gdbserver_tests` fail.  Then run
   `$FJALAR/upstream-regtest.sh $INV/regtest-upstream-3.27.1.txt`, which
   takes about 15 minutes.  It builds a fresh copy of `valgrind-new`, in
   `valgrind-new-build`, runs the regression tests there with the options
   that `check-regtest.sh` uses, and writes the tests that fail to
   `regtest-upstream-3.27.1.txt`, the list of tests that fail in upstream
   3.27.1 on this machine; step 9 uses it.  The list contains an entry
   `post_regtest_checks: Unknown directory 'inst'. ...`, because the
   post-test header check in upstream's tree does not know the `inst`
   directory that this build installs into; Fjalar's tree does not have
   that error.

   The script never builds in `valgrind-old` or `valgrind-new`
   themselves, so that `valgrind-new` stays a clean clone, which becomes
   `valgrind-old` for the next merge.

4. **Merge.**  Run `$FJALAR/merge-valgrind.sh`.  It checks that
   `valgrind-old` and `valgrind-new` are at `$VOLDVER` and `$VNEWVER`,
   writes `coregrind-Fjalar.diff` and `memcheck-Fjalar.diff`, merges
   upstream's changes into Coregrind and into both copies of Memcheck
   (`valgrind/memcheck` and `valgrind/fjalar`) with `git cherry-pick`,
   regenerates `valgrind/fjalar/Makefile.am`, stages the result, and lists
   the conflicts.  `git diff valgrind-merge/base valgrind-merge/new` shows
   upstream's changes.  To start over, run `git reset --hard`.

5. **Coregrind conflicts.**
   - Resolve the conflicts outside `valgrind/fjalar` (files with conflict
     markers, and modify/delete conflicts, all of which
     `git diff --name-only --diff-filter=U` lists), then `git add` or
     `git rm` each file, using `coregrind-Fjalar.diff` and the "Valgrind
     modifications" appendix as a checklist.  In particular, verify each
     Fjalar change still exists after the merge:
     `configure.ac`, top-level `Makefile.am`, `m_libcbase.c`/`pub_tool_libcbase.h`
     (`strnlen`), `m_libcfile.c`/`pub_tool_libcfile.h` (`mkdir`, `fcntl`),
     `m_machine.c`/`pub_tool_machine.h`/`pub_core_machine.h` (extra registers),
     `pub_core_threadstate.h` (extra shadow area), `m_scheduler/scheduler.c`
     (shadow-size assertion), VEX `guest_{amd64,x86}_helpers.c`,
     `host_amd64_defs.c`, `host_generic_reg_alloc2.c` and
     `host_generic_reg_alloc3.c` (spill-area size; v3 is the default
     allocator, and the doc's "Valgrind modifications" appendix omits it),
     `libvex.h`, `libvex_ir.h`, `none/tests/Makefile.am`,
     `tests/check_headers_and_includes`.
   - Pay special attention to any upstream change to guest-state layout
     (`libvex_guest_amd64.h`, `libvex_guest_x86.h`) or to the shadow-area
     size/alignment checks, since Fjalar enlarges the shadow area.
     `vex_extra_shadow` must remain aligned on `LibVEX_GUEST_STATE_ALIGN`,
     and the size/alignment assertions in `scheduler.c` must still account
     for it.  If upstream added fields to `VexGuestAMD64State`, recheck that
     the guest state size remains a multiple of the alignment, and that
     Fjalar's extra guest registers are still at the offsets that DynComp
     and `mc_machine.c` expect.

6. **Memcheck conflicts** in `valgrind/fjalar/`.
   - Resolve the conflicts (as for Coregrind), using
     `memcheck-Fjalar.diff`, including files that upstream removed but
     Fjalar modified; `git rm`
     any that Fjalar does not need.  Remember part of `mc_translate.c`
     lives in `fjalar/mc_translate.h`.  Preserve the #73 edits to `mc_translate.c`
     and `memcheck.h`.
   - In `mc_translate.c`'s `MC_(instrument)` and every helper that it
     calls, check that every case has matching DynComp code, that new cases
     get a DynComp counterpart, and that upstream changes to a Memcheck case
     are mirrored in its DynComp case.  Go through
     `git diff valgrind-merge/base valgrind-merge/new -- valgrind/fjalar/mc_translate.c`
     hunk by hunk, checking off each hunk as
     applied, not applicable, or ported to DynComp (step 7).
   - Check `mc_main.c` still has Fjalar's options/version info.
   - `merge-valgrind.sh` runs `generate-fjalar-makefile.sh`, which regenerates
     `valgrind/fjalar/Makefile.am` from `valgrind/memcheck/Makefile.am`, so
     Fjalar builds every new Memcheck source file.  If
     `valgrind/memcheck/Makefile.am` had a conflict, rerun it after
     resolving the conflict.  Review the staged diff of
     `valgrind/fjalar/Makefile.am`, and update `valgrind/fjalar/fjalar.am`,
     which holds Fjalar's changes to the build, if an upstream change
     conflicts with them.

7. **DynComp / Fjalar / Kvasir updates.**
   - `diff -b $INV/valgrind-old/VEX/pub/libvex_ir.h $INV/valgrind-new/VEX/pub/libvex_ir.h`
     and hand-port relevant hunks of
     `git diff valgrind-merge/base valgrind-merge/new -- valgrind/fjalar/mc_translate.c`
     into
     `fjalar/kvasir/dyncomp_translate.c` (`_DC` functions).
   - For every new or renamed `IROp`, `IRExpr`, or `IRStmt` kind relevant to
     amd64/x86, add handling in the `expr2tags_*_DC` functions (see the
     #79 `Iop_64x4toV256` fix for the pattern).  With #87, that includes
     new unary operations, which reach `expr2tags_Unop_DC`'s `default`
     case.  Running the Kvasir tests and the programs of
     `plan-pre-upgrade.md` item 3 with
     `--dyncomp-unhandled-ops=warn` (#85) lists the unhandled ones that
     they hit.  Search for panics/`default:`
     cases that would now be hit.  Most changes for other architectures can
     be ignored.
   - Running programs finds only the operations those programs use, so also
     run `$FJALAR/list-dyncomp-missing-iops.sh`.  It lists the operations
     that Memcheck handles but DynComp does not mention, and all operations
     that DynComp does not mention (mostly for other architectures).
     Add each relevant one to the appropriate `expr2tags_*_DC` switch, or
     leave it to the `default` case deliberately, with a comment.  Also
     compare `Iex_*` and `Ist_*` kinds.
   - Read NEWS for 3.24.0 through 3.27.1 and note: new platforms (each adds
     `VEX/priv/*` and `coregrind/m_*` files and `configure.ac` cases);
     tool-API changes (e.g. changes to `VG_(needs_*)`, `VG_(track_*)`,
     debuginfo, `pub_tool_*.h` signatures, client-request numbering), which
     need updates to Fjalar callers in `fjalar_main.c`, `fjalar_runtime.c`,
     and `kvasir/*.c`; changes to Memcheck instrumentation, `--track-origins`,
     leak checking, or error suppression, which Fjalar's `mc_*.c` files must
     mirror; and new autotools or compiler requirements (step 8).
   - Check that Fjalar's use of Valgrind's debuginfo reader
     (`coregrind/m_debuginfo`) and its own `readelf.c`/`dwarf.c` don't now
     conflict (duplicate symbols, changed `VG_()` libc names).

8. **Build.**  Step 1 ended with `make very-clean`, so the first build
   compiles every file.  Save its output, and list the warnings that are
   new since step 1's `build-before.log`:

   ```sh
   (set -o pipefail; make -C $FJALAR build 2>&1 | tee $FJALAR/build-after.log)
   $FJALAR/compare-warnings.sh $FJALAR/build-before.log $FJALAR/build-after.log
   ```

   `compare-warnings.sh` prints the new warnings (`>` lines) and the ones
   that are gone (`<` lines), ignoring line numbers, which the merge
   shifts.
   Fix compilation errors and new warnings (newer Valgrind may enable
   additional warning flags; Binutils-derived code is the usual source).
   If the build stopped at an error, its log is incomplete:  after fixing
   the error, run `make very-clean` and the commands again, because an
   incremental build prints no warnings for files that it does not
   recompile.  Test with both a current gcc and the
   compilers in the CI containers.  If `autogen.sh` or `configure` fails,
   the likely cause is a `configure.ac` / `Makefile.am` merge error or a
   newer required autoconf/automake version; check `valgrind-new/autogen.sh`
   and NEWS for tool-version requirements, and make sure the CI Docker images
   (`mdernst/daikon-ubuntu-jdk11-plus`, `mdernst/daikon-rockylinux-jdk25-plus`)
   satisfy them.

9. **Test.**  Run these from `$FJALAR` (`cd $FJALAR`).
   - `./check-regtest.sh`.  The expected failures will change, because
     3.27.1 adds, removes, and fixes tests.  For each unexpected failure:
     if it is also in step 3's `regtest-upstream-3.27.1.txt`, it is an
     upstream failure, so add it to the expected list; otherwise it was
     probably caused by the merge, so fix it.  Remove expected failures
     that now pass.  `./check-regtest.sh --log regtest-<os>.log --update`
     rewrites the list; review its diff, which goes in the PR.
   - `make fjalar-test`.
   - `./test-kvasir.sh 2>&1 | tee kvasir-after.log` — compare with
     `kvasir-before.log` from step 1; the tests must pass with no goal-file
     changes.  Address-related diffs (`<STACK_ADDR>`, `<STATIC_ADDR>`, or
     `<HEAP_ADDR>` on the goal side and hex values on the new side) may
     require updating the address ranges in
     `$DAIKONDIR/tests/kvasir-tests/clean-output.pl`.  DynComp
     comparability differences are the most likely regressions; investigate
     each one rather than updating goal files.
   - Run plain Memcheck (`valgrind/inst/bin/valgrind --tool=memcheck`) on a
     small program, to make sure the core still works independently of
     Fjalar.
   - Push the branch and confirm GitHub Actions CI passes (Ubuntu and
     Rocky Linux 10: build, regtest, and Kvasir jobs).  The CI containers
     differ from your machine, so the regtest jobs will probably fail
     until their lists are updated too: take `regtest-<os>-observed.txt`
     from each job's `regtest-results-*` artifact, apply the same
     upstream-or-merge-bug test as above, and commit the updated
     `regtest-expected/<os>.txt`.  Step 3's upstream list comes from your
     machine; a failure that appears only in CI may be an upstream failure
     specific to that container or CPU.  To check, build upstream 3.27.1 in
     that container (e.g., `docker run` the CI image, clone
     `VALGRIND_3_27_1`, and run `upstream-regtest.sh` as in step 3) and
     compare.

10. **Finish.**
    - Update first line of `valgrind/REVISION`
      (`# Valgrind version 3.27.1, released ...`).
    - Add names of new Valgrind test programs to `.gitignore`, in the
      per-tool sections (such as `# /memcheck/`).
    - Check that Fjalar's files match the target release:
      `./list-file-discrepancies.sh $INV/valgrind-new`.  It should list
      only files that you decided to keep or omit (steps 5 and 6).
    - Document user-visible changes in `$INV/daikon/doc/CHANGELOG.md`.
      Users care, because newer Valgrind supports newer CPUs, kernels,
      glibc, and compilers.  `README` mentions no Valgrind version number,
      so it needs no change.
    - Update `doc/valgrind-merge.texinfo`: dates/OS versions and any new
      pitfalls.  (The regtest baseline output pasted into the doc is
      superseded by `regtest-expected/*.txt`.)
    - In the same PR, while the merge is fresh, also make the documented
      procedure in `doc/valgrind-merge.texinfo` match the one actually
      used, by incorporating what this plan adds to it:
      - working in a new clone (step 1);
      - reading NEWS for every intermediate release (step 7);
      - the list of Coregrind files that need special attention (step 5),
        especially the shadow-state layout and `host_generic_reg_alloc3.c`;
        and, in appendix "Valgrind modifications", add
        `host_generic_reg_alloc3.c` and make the entries match
        `coregrind-Fjalar.diff` from this merge;
      - the mechanical `Iop_` coverage check (step 7), in appendix
        "Supporting new VEX IR Instruction" (section "Updating
        Fjalar/Kvasir" already runs `list-dyncomp-missing-iops.sh`);
      - the hunk-by-hunk checkoff of `mc_translate.c` (step 6);
      - `make fjalar-test` and the plain Memcheck run (step 9).
      Rebuild with `make doc` (which `test.sh` runs in CI) to confirm that
      the document still formats.
    - Use the commit message "Upgrade Valgrind from 3.23.0 to 3.27.1".  The
      diff files can also be attached to the PR.
    - Commit as one PR, and save the diff files.
    - After the PR has landed, keep `valgrind-new` as the next merge's
      `valgrind-old` (step 2 reuses it), and delete `valgrind-new-build`.
      Do not do this earlier:  review may require redoing the merge,
      which needs `valgrind-old`, or comparing a failure that
      appears only in CI with upstream's build (step 9).

      ```sh
      rm -rf $INV/valgrind-old $INV/valgrind-new-build
      mv $INV/valgrind-new $INV/valgrind-old
      ```

      Remove `valgrind-old` first; otherwise `mv` moves `valgrind-new`
      inside it.

## Risks

- **Shadow-area / guest-state changes** in VEX or coregrind would break
  Fjalar's extra shadow state in subtle ways (crashes or wrong comparability),
  not compile errors.  Mitigation: the `scheduler.c` assertions, plus the
  DynComp regression tests.
- **A Memcheck change mirrored in `mc_translate.c` but not in
  `dyncomp_translate.c`** (or vice versa).  Mitigation: the hunk-by-hunk
  checkoff in step 6.
- **New IROps** used by modern compilers (AVX/AVX2 and others on amd64) can
  make DynComp panic at run time.  Re-run the vectorized programs from
  `plan-pre-upgrade.md` item 3 (which all work on 3.23 by then); a panic
  there after the merge is due to the upgrade.
- **Build-system changes** (`Makefile.all.am`, `Makefile.tool.am`,
  `configure.ac`) can silently drop Fjalar from the build or change flags.
- **Newer upstream build requirements** (autotools, compiler) that the CI
  images do not meet.  Mitigation: check NEWS (step 7) before starting
  step 5.
- **New warning flags** will hit `readelf.c`/`dwarf.c`, which were just
  merged in the readelf upgrade; expect a second round of warning fixes
  there.
