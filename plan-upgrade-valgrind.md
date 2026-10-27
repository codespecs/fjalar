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

This plan assumes that CI enforces the expected regtest failures (#175),
and that DynComp handles every IROp that the vectorized programs of step 9
exercised on 3.23 (#172, #173).

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
  conflicts are unmanageable.  The steps below are written for the single
  jump.  For the fallback, do all the steps twice, once for 3.23.0 -> 3.25.1
  and once for 3.25.1 -> 3.27.1, and in each pass substitute that hop's
  versions for 3.23.0 and 3.27.1 everywhere:  `VOLDTAG` and `VNEWTAG`
  (including in the CI command of step 9), the NEWS releases to read,
  `valgrind/REVISION`, and the commit message.
- The checklist of Fjalar changes to upstream files is
  `git diff --diff-filter=a valgrind-merge/base valgrind-merge/fjalar`
  (step 4).  By where they matter:
  - Memcheck-derived files, such as `mc_translate.c`, `mc_main.c`, and
    `memcheck.h`, can conflict in step 6.
  - Coregrind and other upstream files can conflict in step 5.  Where
    Fjalar backported an upstream fix (such as `$(nproc)` in
    `auxprogs/Makefile.am`, and the GCC 15 fixes to
    `drd/tests/swapcontext.c`, `helgrind/tests/tc17_sembar.c`, and
    `none/tests/bug234814.c`), take upstream's version.
  - DynComp changes, in `kvasir/`, cause no conflict, because upstream has
    no `kvasir/`, but step 7 must keep them.
- Land the open PRs that change files under `valgrind/` before this
  upgrade.  To list them:

  ```sh
  gh pr list -R codespecs/fjalar --limit 1000 --json number,files --jq \
    '.[] | select((.files | length) >= 100
                  or any(.files[]; .path | startswith("valgrind/")))
         | .number'
  ```

  `gh` returns only the first 100 files of each PR, so the command also
  lists every PR with 100 or more files; check those by hand.

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
     with `--update`), then
     `cp regtest-<os>-observed.txt $INV/regtest-before-merge.txt` (step 9
     compares with it; `regtest-expected/<os>.txt` cannot serve, because it
     may list tests that no longer fail); and `make fjalar-test`.
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
   export VOLDTAG=VALGRIND_3_23_0 VNEWTAG=VALGRIND_3_27_1
   VALGRIND_GIT=https://sourceware.org/git/valgrind.git
   [ -d $INV/valgrind-old ] \
     || git clone -b $VOLDTAG --depth 1 $VALGRIND_GIT $INV/valgrind-old
   rm -rf $INV/valgrind-new
   git clone -b $VNEWTAG --depth 1 $VALGRIND_GIT $INV/valgrind-new
   ```

   Step 10 of the previous merge kept that merge's `valgrind-new` as
   `valgrind-old`, so reuse it if it exists; `merge-valgrind.sh` (step 4)
   checks that it is at `$VOLDTAG`.

   Correct the files of earlier merges, following section "Correct the
   files of earlier merges" of `doc/valgrind-merge.texinfo`.
   `$FJALAR/list-file-discrepancies.sh $INV/valgrind-old` lists
   files that Fjalar tracks but `valgrind-old` lacks (remove those that
   Fjalar should not have); Memcheck files in `valgrind/fjalar` that
   `valgrind-old` lacks (keep Fjalar's own, such as `mc_translate.h`);
   Memcheck files that `valgrind-old` has but `valgrind/fjalar` lacks (copy
   them, because Fjalar builds every Memcheck source file); files that
   `valgrind-old` has but Fjalar does not track, such as empty files and
   files that match `.gitignore` (add those that Fjalar should have); and
   files whose mode differs from that in `valgrind-old` (fix those that
   Fjalar did not change on purpose).  Against 3.23.0, these corrections
   are already committed, so the script lists only Fjalar's own
   `valgrind/fjalar/mc_translate.h`.
   Commit any corrections before merging, because
   `merge-valgrind.sh` requires a clean work tree.  (The merge handles the
   files that upstream added or removed since `$VOLDTAG`.)

3. **Baseline.**  First install `gdb` and the glibc debuginfo package;
   without them, most `gdbserver_tests` fail.  Then run
   `$FJALAR/upstream-regtest.sh $INV/regtest-upstream-$VNEWTAG.txt`, which
   takes about 15 minutes.  It checks that `valgrind-new` is at
   `$VNEWTAG`, builds a fresh copy of it, in `valgrind-new-build`, runs
   the regression tests there with the options that `check-regtest.sh`
   uses, and writes the tests that fail to
   `regtest-upstream-$VNEWTAG.txt`, the list of tests that fail in
   upstream 3.27.1 on this machine; step 9 uses it.

   The script never builds in `valgrind-old` or `valgrind-new`
   themselves, so that `valgrind-new` stays a clean clone, which becomes
   `valgrind-old` for the next merge.

4. **Merge.**  Run `$FJALAR/merge-valgrind.sh`.  It checks that
   `valgrind-old` and `valgrind-new` are at `$VOLDTAG` and `$VNEWTAG`,
   records Fjalar before the merge as `valgrind-merge/fjalar`, merges
   upstream's changes into Coregrind and into both copies of Memcheck
   (`valgrind/memcheck` and `valgrind/fjalar`) with `git cherry-pick`,
   regenerates `valgrind/fjalar/Makefile.am`, stages the result, and lists
   the conflicts.  `git diff valgrind-merge/base valgrind-merge/new` shows
   upstream's changes.  After resolving the conflicts (steps 5 and 6), run
   `$FJALAR/compare-fjalar-changes.sh`, which lists each Fjalar change
   that the merge lost or altered.  To start over, run `git reset --hard`.

5. **Coregrind conflicts.**
   - Resolve the conflicts outside `valgrind/fjalar` (files with conflict
     markers, and modify/delete conflicts, all of which
     `git diff --name-only --diff-filter=U` lists), then `git add` or
     `git rm` each file, using Fjalar's changes outside `valgrind/fjalar`
     and the "Valgrind modifications" appendix as a checklist.  In particular, verify each
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
     Fjalar's changes in `valgrind/fjalar`, including files that upstream removed but
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
   - `git diff -b valgrind-merge/base valgrind-merge/new -- valgrind/VEX/pub/libvex_ir.h`
     and hand-port relevant hunks of
     `git diff valgrind-merge/base valgrind-merge/new -- valgrind/fjalar/mc_translate.c`
     into
     `fjalar/kvasir/dyncomp_translate.c` (`_DC` functions).
   - For every new or renamed `IROp`, `IRExpr`, or `IRStmt` kind relevant to
     amd64/x86, add handling in the `expr2tags_*_DC` functions (see the
     #79 `Iop_64x4toV256` fix for the pattern).  With #87, that includes
     new unary operations, which reach `expr2tags_Unop_DC`'s `default`
     case, and for which `make fjalar-test` (step 9) fails.  Running the Kvasir tests and the vectorized
     programs of step 9 with
     `--dyncomp-unhandled-ops=warn` (#85) lists the unhandled ones that
     they hit.  Search for panics/`default:`
     cases that would now be hit.  Most changes for other architectures can
     be ignored.
   - Running programs finds only the operations those programs use.
     `make fjalar-test` runs `valgrind/fjalar/tests/dyncomp-op-coverage-test.sh`
     (from #173), which lists each new IROp that has no case, and each IROp
     listed as unimplemented that amd64 or x86 now uses.  Handle each
     operation that it lists, as appendix "Supporting new VEX IR
     Instruction" of `doc/valgrind-merge.texinfo` describes:  give it a
     case, or, if amd64 and x86 do not use it, list it in the comment of
     `dyncomp_translate.c` that begins "The following opcodes are not
     implemented".
     Also compare `Iex_*` and `Ist_*` kinds.
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
     3.27.1 adds, removes, and fixes tests.  Then
     `./check-regtest.sh --log regtest-<os>.log --expected $INV/regtest-upstream-$VNEWTAG.txt --report-only`
     lists the failures that are not in step 3's upstream list.  Each one
     that is in `$INV/regtest-before-merge.txt` (step 1) failed before the
     merge too, and is specific to Fjalar; each other one was probably
     caused by the merge, so fix it.  A test that `regtest-expected/<os>.txt`
     marks with `?` may fail only sometimes, so if such a test is not in
     `regtest-before-merge.txt`, run the tests again before you conclude
     that the merge broke it.  Only when no merge-caused failure remains,
     `./check-regtest.sh --log regtest-<os>.log --update` rewrites the
     list, adding the new upstream failures and removing the tests that
     now pass; review its diff.  If the list is committed, its diff goes
     in the PR; if step 1 created it locally, do not commit it.
   - `make fjalar-test`.  It runs every test, even after one fails, and
     then lists the tests that failed.
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
   - Look for DynComp panics on unhandled IROps by running vectorized
     programs under DynComp.  On 3.23, before the upgrade, this found one
     (#172).  The programs were five small ones (sums, integer arithmetic,
     floating-point arithmetic, string functions, and bit manipulation),
     each compiled with `-O2 -march=x86-64-v3`, `-O3 -march=x86-64-v3`,
     `-O3 -march=x86-64-v2`, and `-O3`, plus Daikon's `md5` and `bzip2`
     tests compiled with `-O3 -march=x86-64-v3`; they exercised 258
     distinct IROps, 84 of them on 256-bit vectors.  Compile each program
     with `-gdwarf-4 -no-pie`, because Fjalar does not fully read DWARF 5 and
     recognizes a function's entry point only at the address in the
     debugging information.  Unless Valgrind decodes AVX-512 (3.23 does
     not), do not use `-march=x86-64-v4`, which permits AVX-512
     instructions on any machine, or `-march=native` on a machine with
     AVX-512:  if Valgrind cannot decode an instruction, the program dies
     with SIGILL before DynComp sees its IROps.  Run each program with
     `$FJALAR/valgrind/inst/bin/valgrind --tool=fjalar --dyncomp --dyncomp-unhandled-ops=warn`,
     which reports each unhandled operation once and continues, instead
     of stopping at the first; add
     `--trace-flags=01000000 --trace-notbelow=0` to see which IROps a run
     exercised.  Do not use `$DAIKONDIR/scripts/kvasir-dtrace`:  it runs
     the Kvasir in `$DAIKONDIR/fjalar`, which may be a different tree.
   - Push the branch and confirm GitHub Actions CI passes (Ubuntu and
     Rocky Linux 10: build, regtest, and Kvasir jobs).  The CI containers
     differ from your machine, so the regtest jobs will probably fail
     until their lists are updated too: take `regtest-<os>-observed.txt`
     from each job's `regtest-results-*` artifact, apply the same
     upstream-or-merge-bug test as above, and commit the updated
     `regtest-expected/<os>.txt`.  Step 3's upstream list comes from your
     machine; a failure that appears only in CI may be an upstream failure
     specific to that container or CPU.  To check, run
     `upstream-regtest.sh` in the failing job's image (the regtest jobs of
     `.github/workflows/ci.yml` name the images), and compare.  The script
     needs `INV`, the upstream clone at `$INV/valgrind-new`, and a Fjalar
     tree that contains it and `check-regtest.sh`.  For example, for the
     Ubuntu job (writing the list to `$INV` on the host):

     ```sh
     docker run --rm -v "$INV:/host" mdernst/daikon-ubuntu-jdk11-plus:latest bash -c '
       export INV=/tmp/inv VNEWTAG=VALGRIND_3_27_1
       git clone -q -b $VNEWTAG --depth 1 https://sourceware.org/git/valgrind.git $INV/valgrind-new
       git clone -q --depth 1 https://github.com/codespecs/fjalar.git $INV/fjalar
       $INV/fjalar/upstream-regtest.sh /host/regtest-upstream-$VNEWTAG-ubuntu.txt'
     ```

10. **Finish.**
    - Update first line of `valgrind/REVISION`
      (`# Valgrind version 3.27.1, released ...`).
    - The merge updates `valgrind/.gitignore` (upstream's), including the
      names of new Valgrind test programs.  Add to the top-level
      `.gitignore` only the files that Fjalar's changes generate.
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
        `host_generic_reg_alloc3.c` and make the entries match Fjalar's
        changes outside `valgrind/fjalar` after this merge;
      - the `Iop_` coverage tests that `make fjalar-test` runs (step 7),
        in appendix "Supporting new VEX IR Instruction";
      - the hunk-by-hunk checkoff of `mc_translate.c` (step 6);
      - `make fjalar-test` and the plain Memcheck run (step 9).
      Rebuild with `make doc` (which `test.sh` runs in CI) to confirm that
      the document still formats.
    - If step 1 created a local `regtest-expected/<os>.txt`, delete it
      before committing:  git does not ignore it, so `git add -A` would
      commit it.
    - Use the commit message "Upgrade Valgrind from 3.23.0 to 3.27.1".
    - Commit as one PR.
    - After the PR has landed, keep `valgrind-new` as the next merge's
      `valgrind-old` (step 2 reuses it), and delete `valgrind-new-build`
      and `regtest-before-merge.txt`.
      Do not do this earlier:  review may require redoing the merge,
      which needs `valgrind-old`, or comparing a failure that
      appears only in CI with upstream's build (step 9).

      ```sh
      rm -rf $INV/valgrind-old $INV/valgrind-new-build $INV/regtest-before-merge.txt
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
  make DynComp panic at run time.  Re-run the vectorized programs of step 9
  (which all work on 3.23); a panic there after the merge is due to the
  upgrade.
- **Build-system changes** (`Makefile.all.am`, `Makefile.tool.am`,
  `configure.ac`) can silently drop Fjalar from the build or change flags.
- **Newer upstream build requirements** (autotools, compiler) that the CI
  images do not meet.  Mitigation: check NEWS (step 7) before starting
  step 5.
- **New warning flags** will hit `readelf.c`/`dwarf.c`, which were just
  merged in the readelf upgrade; expect a second round of warning fixes
  there.
