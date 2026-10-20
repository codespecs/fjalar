# Plan: upgrade Fjalar's Valgrind from 3.23.0 to 3.27.1

Reference procedure: `doc/valgrind-merge.texinfo` (chapters "Getting Started"
through "Committing").  This plan applies that procedure to the current
situation and notes where it needs adjusting.

Below, `$FJALAR` is the Fjalar clone being upgraded (see step 1); it
must be directly in `$INV`.  Some scripts that the merge uses read the
Fjalar tree from `$INV/fjalar`, so step 1 makes `$INV/fjalar` a symbolic
link to `$FJALAR` while any of them is in use:  `generate-patch-files.sh`
until #133 lands, and `apply-patch-files.sh`, which #103 adds and which
uses `$INV/fjalar`.  (`make git-update`, which #103 removes, reads
`../coregrind.patch` and `../memcheck.patch`, which are in `$INV` for any
clone directly in `$INV`, so it needs no link.)

## Ordering: do this after the readelf upgrade

Do the Binutils/readelf upgrade (`plan-upgrade-readelf.md`) first, and finish
it completely (landed, CI green) before starting this one.  That plan's
"Ordering" section gives the reasons and the exception.

The preparation in `plan-pre-upgrade.md` must also be done; this plan
assumes items 1 (regtest in CI), 3 (`generate-patch-files.sh` checks its
inputs), 4 (DynComp scan), and 7 (stale upstream files removed).  Item 2
(#103:  patch files created with `git diff` and applied with
`git apply --3way`) is still open.  Until it lands, the paragraph above
and steps 2, 3, 5, 6, and 10 below describe the current procedure
(`patch`, `*.rej` files, and `make git-update`); #103 rewrites them for
its procedure.

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
   updated by hand, using `memcheck.patch` as a guide.

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
  - Upstream files that Fjalar still tracked although upstream had deleted
    them were removed by `1d9a43ad` (#98).
  - DynComp, so step 7 must keep them (no conflict expected, since
    `kvasir/` is not patched): `b2c735d7` (#79) `Iop_64x4toV256` and
    `125330a0` (#88) vector shifts, `d3b71509` (#85,
    `--dyncomp-unhandled-ops`), and `225fae19` (#86, tag 0 for unary
    operations whose result is a mask or count), in `dyncomp_translate.c`;
    `8cd25174` (#104, comparison tags merged with a dirty call),
    `1ff7ffe4` (#107, no helper-call merges under
    `--dyncomp-interactions=none`), `7c4b6598` (#106, chained helper-call
    merges), and `54b935a6` (#126, a comment on the dirty-call merge), in
    `dyncomp_translate.c`;
    `a4d693e1` (#114, instruction address only when tracing) and
    `ab0b6145` (#108, `WEAK_FRESH_TAG` check), in `dyncomp_main.c`.
  - Open PRs to land before this upgrade (as of 2026-10-20):
    - DynComp, `dyncomp_translate.c`:  #87 (explicit handling of all 283
      unary operations), #111,
      #115, #116, #117, #119, #120, #122, #123, and #125.  With #85
      (landed) and #87, new IROps in 3.24-3.27 reach the `default` cases of all four
      `expr2tags_*_DC` functions, and
      `--dyncomp-unhandled-ops=warn` lists them all in one run (step 7).
    - Memcheck-derived files, so they can conflict in step 6:  #115,
      #117, #119, #120, and #122 change `mc_translate.c` and
      `mc_translate.h`.
    - Scripts that this plan uses:  #133 (`generate-patch-files.sh` and
      `make git-update` find the Fjalar tree themselves, so that step 1
      needs no symbolic link) and #132 (`check-regtest.sh --log` takes the
      operating system from the log's name).
    - Other open PRs may have been opened since.  To list the open PRs
      that change files under `valgrind/`:
      `gh pr list -R codespecs/fjalar --json number,files --jq '.[] | select(any(.files[]; .path | startswith("valgrind/"))) | .number'`.
  - Other changes since then (#76, #80, #89, #91, #94, the rest of #73)
    touch only Fjalar's own files and Binutils-derived files, which this
    merge does not patch.
  - The complete checklist of Fjalar changes to upstream files is
    `coregrind-Fjalar.diff` and `memcheck-Fjalar.diff` (step 4).

## Steps

1. **Preparation** (separate branch, e.g. `valgrind-3.27.1`; do not combine with
   the Binutils/readelf upgrade, which should already have landed).
   - Work in a new clone, because each working directory is dedicated to
     one branch: clone Fjalar from GitHub into, e.g.,
     `$INV/fjalar-branch-valgrind-3.27.1`, and create the branch there.
     Do not clone `$INV/fjalar`:  once `$INV/fjalar` is a symbolic link to
     the new clone (below), that clone's `origin` would be itself, so
     `git pull` would silently pull nothing.  Set `FJALAR` to that clone, e.g.,
     `FJALAR=$INV/fjalar-branch-valgrind-3.27.1`; the commands below use
     it.  If none of the scripts that read `$INV/fjalar` is in use (see the
     paragraph at the top of this plan), skip the rest of this bullet.
     Otherwise, while merging, make `$INV/fjalar` a symbolic link to that
     clone.  If `$INV/fjalar` is already a symbolic
     link, record its target (`readlink $INV/fjalar`) and replace it with
     `ln -sfn fjalar-branch-valgrind-3.27.1 $INV/fjalar`.  If it is a
     directory, first move it aside; otherwise `ln -s` creates the link
     inside it:
     ```sh
     mv $INV/fjalar $INV/fjalar-orig
     git -C $INV/fjalar-orig worktree repair
     ln -s fjalar-branch-valgrind-3.27.1 $INV/fjalar
     ```
     `git worktree repair` reconnects the worktrees linked to the moved
     clone (`git -C $INV/fjalar-orig worktree list`).  Without it, their
     `.git` files still name `$INV/fjalar/.git/worktrees/...`, which the
     new link redirects into the merge clone, so git commands in them fail
     or act on the wrong repository.
     Meanwhile, `$INV/daikon/fjalar` (which by default points to
     `$INV/fjalar`) also reaches the new clone.  When the merge PR has
     landed, undo this:  point the link back at its recorded target, or
     `rm $INV/fjalar && mv $INV/fjalar-orig $INV/fjalar && git -C $INV/fjalar worktree repair`.
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
   cd $INV
   [ -d valgrind-old ] || git clone -b $VOLDVER --depth 1 https://sourceware.org/git/valgrind.git valgrind-old
   rm -rf valgrind-new
   git clone -b $VNEWVER --depth 1 https://sourceware.org/git/valgrind.git valgrind-new
   ```
   Step 10 of the previous merge kept that merge's `valgrind-new` as
   `valgrind-old`, so reuse it if it exists; `generate-patch-files.sh`
   (step 4) checks that it is a pristine clone at `$VOLDVER`.
   Remove from `$FJALAR/valgrind` the files that `valgrind-new` does not have,
   using the commands in section "Remove files that the target Valgrind release
   does not have" of `doc/valgrind-merge.texinfo`.  The second command there
   handles Fjalar's own copy of memcheck in `valgrind/fjalar/`.  The
   doc's commands use `$INV/fjalar`; use `$FJALAR` in its place.

3. **Baseline.**  Never build in `valgrind-old` or `valgrind-new` themselves:
   `generate-patch-files.sh` refuses to run if either contains changes or
   untracked files, such as build products (`*.o`, `Makefile`, `config.h`,
   test binaries, `inst/`).  Otherwise they would end up in
   `coregrind.patch` and then be `git add`ed by `make git-update`.  The
   error message gives the `git reset`/`git clean` command that makes a tree
   pristine again.  Build a copy instead.  First install `gdb` and the
   glibc debuginfo package; without them, most `gdbserver_tests` fail.
   ```sh
   cd $INV
   rm -rf valgrind-new-build
   git clone -q valgrind-new valgrind-new-build && cd valgrind-new-build
   ./autogen.sh && ./configure --prefix=$(pwd)/inst
   make -j"$(nproc)" all install && make -j"$(nproc)" regtest XMLLINT=xmllint-skipped-by-check-regtest > test.log 2>&1
   make -s --no-print-directory post-regtest-checks > test-post.log 2>&1
   $FJALAR/check-regtest.sh --log test.log --expected $INV/regtest-upstream-3.27.1.txt --update
   ```
   These are the options that `check-regtest.sh` itself uses.  Setting
   `XMLLINT` keeps `make check` from validating the manual, which fails
   without the DocBook DTD.  `-s --no-print-directory` keeps make's own
   messages out of `test-post.log`, which `check-regtest.sh` reads (because
   its name is derived from `test.log`) as the post-test checks' error
   messages.  The script writes the observed failures to `test-observed.txt`.
   `regtest-upstream-3.27.1.txt` is the list of tests that fail in upstream
   3.27.1 on this machine; step 9 uses it.  It contains an entry
   `post_regtest_checks: Unknown directory 'inst'. ...`, because the
   post-test header check in upstream's tree does not know the `inst`
   directory that this build installs into; Fjalar's tree does not have
   that error.

4. **Create the diffs.** Run `$FJALAR/generate-patch-files.sh`, producing
   `coregrind.patch`, `memcheck.patch`, `coregrind-Fjalar.diff`,
   `memcheck-Fjalar.diff`.  The script checks that `valgrind-old` and
   `valgrind-new` are pristine clones at `$VOLDVER` and `$VNEWVER`.

5. **Coregrind merge.**
   - `cd $FJALAR/valgrind && patch -p1 -lu --dry-run < $INV/coregrind.patch`,
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

6. **Memcheck merge** into `valgrind/fjalar/`.
   - `cd $FJALAR/valgrind/fjalar && patch -p2 -lu --dry-run < $INV/memcheck.patch`,
     then for real (try `-F3` only if needed, and review its results).
   - Resolve `*.rej`.  Remember part of `mc_translate.c` lives in
     `fjalar/mc_translate.h`.  Preserve the #73 edits to `mc_translate.c`
     and `memcheck.h`.
   - In `mc_translate.c`'s `MC_(instrument)` and every helper that it
     calls, check that every case has matching DynComp code, that new cases
     get a DynComp counterpart, and that upstream changes to a Memcheck case
     are mirrored in its DynComp case.  Go through the `mc_translate.c`
     portion of `memcheck.patch` hunk by hunk, checking off each hunk as
     applied, not applicable, or ported to DynComp (step 7).
   - Check `mc_main.c` still has Fjalar's options/version info.
   - Run `$FJALAR/generate-fjalar-makefile.sh`, which regenerates
     `valgrind/fjalar/Makefile.am` from `valgrind/memcheck/Makefile.am`, so
     Fjalar builds every new Memcheck source file.  Review the diff of
     `valgrind/fjalar/Makefile.am`, and update `valgrind/fjalar/fjalar.am`,
     which holds Fjalar's changes to the build, if an upstream change
     conflicts with them.

7. **DynComp / Fjalar / Kvasir updates.**  Run the commands of this step
   from `$INV` (`cd $INV`; step 6 left the shell in
   `$FJALAR/valgrind/fjalar`), so that the relative paths are right and the
   scratch files `all-ops`, `dc-ops`, and `mc-ops` are written outside the
   Fjalar tree.
   - `diff -b valgrind-old/VEX/pub/libvex_ir.h valgrind-new/VEX/pub/libvex_ir.h`
     and hand-port relevant `memcheck.patch` hunks into
     `fjalar/kvasir/dyncomp_translate.c` (`_DC` functions).
   - For every new or renamed `IROp`, `IRExpr`, or `IRStmt` kind relevant to
     amd64/x86, add handling in the `expr2tags_*_DC` functions (see the
     #79 `Iop_64x4toV256` fix for the pattern).  With #87, that includes
     new unary operations, which reach `expr2tags_Unop_DC`'s `default`
     case.  Running the Kvasir tests and the programs of
     `plan-pre-upgrade.md` item 4 with
     `--dyncomp-unhandled-ops=warn` (#85) lists the unhandled ones that
     they hit.  Search for panics/`default:`
     cases that would now be hit.  Most changes for other architectures can
     be ignored.
   - Running programs finds only the operations those programs use, so also
     list the operations that DynComp does not mention:
     ```sh
     cd $INV
     grep -oE '\bIop_[A-Za-z0-9_]+' valgrind-new/VEX/pub/libvex_ir.h | sort -u > all-ops
     grep -oE '\bIop_[A-Za-z0-9_]+' $FJALAR/valgrind/fjalar/kvasir/dyncomp_translate.c | sort -u > dc-ops
     grep -oE '\bIop_[A-Za-z0-9_]+' valgrind-new/memcheck/mc_translate.c | sort -u > mc-ops
     comm -23 mc-ops dc-ops     # ops Memcheck handles but DynComp does not
     comm -23 all-ops dc-ops    # all ops DynComp does not mention (mostly other architectures)
     ```
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
   new since step 1's `build-before.log`.  The merge shifts line numbers,
   so the commands remove them before comparing:
   ```sh
   cd $FJALAR
   (set -o pipefail; make build 2>&1 | tee build-after.log)
   for f in before after; do
     grep -E ':[0-9]+:[0-9]+: warning' build-$f.log | sed -E 's/:[0-9]+:[0-9]+:/:/' \
       | sort > $INV/warnings-$f.txt
   done
   diff $INV/warnings-before.txt $INV/warnings-after.txt
   ```
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
     `VALGRIND_3_27_1`, and run `make regtest` as in step 3) and compare.

10. **Finish.**
    - Update first line of `valgrind/REVISION`
      (`# Valgrind version 3.27.1, released ...`).
    - Add names of new Valgrind test programs to `.gitignore`, in the
      per-tool sections (such as `# /memcheck/`).
    - `make git-update > git.script`, review, run.
    - `git add -u -- valgrind`.  This stages the removal of the files that
      step 2 removed with `rm` and that are in neither `valgrind-old` nor
      `valgrind-new`, which `git.script` does not cover.
    - Check that Fjalar tracks no file that upstream does not have:  the
      first command in the doc section of step 2 prints nothing.
    - Document user-visible changes in `$INV/daikon/doc/CHANGELOG.md`.
      Users care, because newer Valgrind supports newer CPUs, kernels,
      glibc, and compilers.  `README` mentions no Valgrind version number,
      so it needs no change.
    - Update `doc/valgrind-merge.texinfo`: dates/OS versions and any new
      pitfalls.  (The regtest baseline output pasted into the doc is
      superseded by `regtest-expected/*.txt`.)
    - In the same PR, while the merge is fresh, also make the documented
      procedure in `doc/valgrind-merge.texinfo` match the one actually
      used, by incorporating what this plan adds beyond
      `plan-pre-upgrade.md` item 5:
      - working in a new clone (step 1);
      - reading NEWS for every intermediate release (step 7);
      - the list of Coregrind files that need special attention (step 5),
        especially the shadow-state layout and `host_generic_reg_alloc3.c`;
        and, in appendix "Valgrind modifications", add
        `host_generic_reg_alloc3.c` and make the entries match
        `coregrind-Fjalar.diff` from this merge;
      - the mechanical `Iop_` coverage check (step 7), in "Updating
        Fjalar/Kvasir" and in appendix "Supporting new VEX IR Instruction";
      - the hunk-by-hunk checkoff of `mc_translate.c` (step 6);
      - `make fjalar-test` and the plain Memcheck run (step 9).
      Rebuild with `make doc` (which `test.sh` runs in CI) to confirm that
      the document still formats.
    - Use the commit message "Upgrade Valgrind from 3.23.0 to 3.27.1".  The
      patch/diff files can also be attached to the PR.
    - Commit as one PR, and save the patch/diff files.
    - After the PR has landed, keep `valgrind-new` as the next merge's
      `valgrind-old` (step 2 reuses it), and delete `valgrind-new-build`.
      Do not do this earlier:  review may require regenerating the patch
      files, which needs `valgrind-old`, or comparing a failure that
      appears only in CI with upstream's build (step 9).
      ```sh
      cd $INV
      rm -rf valgrind-old valgrind-new-build
      mv valgrind-new valgrind-old
      git -C valgrind-old reset --hard && git -C valgrind-old clean -fdx
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
  `plan-pre-upgrade.md` item 4 (which all work on 3.23 by then); a panic
  there after the merge is due to the upgrade.
- **Build-system changes** (`Makefile.all.am`, `Makefile.tool.am`,
  `configure.ac`) can silently drop Fjalar from the build or change flags.
- **Newer upstream build requirements** (autotools, compiler) that the CI
  images do not meet.  Mitigation: check NEWS (step 7) before starting
  step 5.
- **New warning flags** will hit `readelf.c`/`dwarf.c`, which were just
  merged in the readelf upgrade; expect a second round of warning fixes
  there.
