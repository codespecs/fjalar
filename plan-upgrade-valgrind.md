# Plan: upgrade Fjalar's Valgrind from 3.23.0 to 3.27.1

Reference procedure: `doc/valgrind-merge.texinfo` (chapters "Getting Started"
through "Committing").  This plan applies that procedure to the current
situation and notes where it needs adjusting.

Below, `$INV/fjalar` means the Fjalar tree being upgraded.
(`merge-valgrind.sh` merges into the tree that contains it, wherever that
is.)

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
  - Memcheck-derived files, so they can conflict (step 6):
    `1ca71b1c` (#73) changed `mc_translate.c` and `memcheck.h`.
  - DynComp, so step 7 must keep them (no conflict expected, since
    upstream has no `kvasir/`): `b2c735d7` (#79) `Iop_64x4toV256` in
    `dyncomp_translate.c`.
  - Other changes since then (#76, #80, the rest of #73) touch only
    Fjalar's own files and Binutils-derived files, which this merge does not
    change.
  - The complete checklist of Fjalar changes to upstream files is
    `git diff --diff-filter=a valgrind-merge/base valgrind-merge/fjalar`
    (step 4).
- Land the open PRs that change the files that this merge merges into
  (everything under `valgrind/` except Fjalar's own files and the
  Binutils-derived files) before starting this upgrade, so that their
  changes are part of the Fjalar tree being merged into rather than
  conflicting with the upgrade later.  To list them:

  ```sh
  gh pr list -R codespecs/fjalar --limit 1000 --json number,files --jq \
    '.[] | select((.files | length) >= 100
                  or any(.files[]; .path
                                   | (startswith("valgrind/") and (startswith("valgrind/fjalar/") | not))
                                     or test("^valgrind/fjalar/(mc_|memcheck\\.h$)")))
         | .number'
  ```

  `gh` returns only the first 100 files of each PR, so the command also
  lists every PR with 100 or more files; check those by hand.

## Steps

1. **Preparation** (separate branch, e.g. `valgrind-3.27.1`; do not combine with
   the Binutils/readelf upgrade, which should already be merged).
   - `git pull` both `fjalar` and `daikon`; ensure no local or outgoing changes.
   - Record baselines on current sources: `make build`; then
     `./check-regtest.sh`, which needs the build (must report no unexpected
     failures; if this machine's OS has no `regtest-expected/<os>.txt`,
     create a local, uncommitted one with `--update`); and
     `./test-kvasir.sh 2>&1 | tee kvasir-before.log`.
     Use `./test-kvasir.sh`, which points `$DAIKONDIR/fjalar` at this tree.
     Running `$INV/daikon/tests/kvasir-tests` or `make daikon-test` directly
     builds whatever `$INV/daikon/fjalar` points to; if you do that, first
     check `readlink -f $INV/daikon/fjalar`.
   - `make very-clean`; review/delete untracked files
     (`git ls-files --others --exclude-standard`), except
     `regtest-expected/<os>.txt` if you created it above:  step 9 compares
     against it.

2. **Get the trees.**

   ```sh
   export VOLDTAG=VALGRIND_3_23_0 VNEWTAG=VALGRIND_3_27_1
   git clone -b $VOLDTAG --depth 1 https://sourceware.org/git/valgrind.git $INV/valgrind-old
   git clone -b $VNEWTAG --depth 1 https://sourceware.org/git/valgrind.git $INV/valgrind-new
   ```

   Correct the files of earlier merges, following section "Correct the
   files of earlier merges" of `doc/valgrind-merge.texinfo`.
   `./list-file-discrepancies.sh $INV/valgrind-old` lists
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

3. **Baseline.**  Build in a copy of `valgrind-new`, so that `valgrind-new`
   stays a clean clone, which becomes `valgrind-old` for the next merge:

   ```sh
   rm -rf $INV/valgrind-new-build
   git clone -q $INV/valgrind-new $INV/valgrind-new-build && cd $INV/valgrind-new-build
   ./autogen.sh && ./configure --prefix=$(pwd)/inst
   make all install \
     && make regtest XMLLINT=xmllint-skipped-by-check-regtest > test.log 2>&1
   make -s --no-print-directory post-regtest-checks > test-post.log 2>&1
   $INV/fjalar/check-regtest.sh --log test.log \
     --expected $INV/regtest-upstream-3.27.1.txt --update
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

4. **Merge.**  Run `$INV/fjalar/merge-valgrind.sh`.  It checks that
   `valgrind-old` and `valgrind-new` are at `$VOLDTAG` and `$VNEWTAG`,
   records Fjalar before the merge as `valgrind-merge/fjalar`, merges
   upstream's changes into Coregrind and into both copies of Memcheck
   (`valgrind/memcheck` and `valgrind/fjalar`) with `git cherry-pick`,
   regenerates `valgrind/fjalar/Makefile.am`, stages the result, and lists
   the conflicts.  `git diff valgrind-merge/base valgrind-merge/new` shows
   upstream's changes.  After resolving the conflicts (steps 5 and 6), run
   `$INV/fjalar/compare-fjalar-changes.sh`, which lists each Fjalar change
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
     (shadow-size assertion), VEX `host_amd64_defs.c`,
     `host_generic_reg_alloc2.c` (and check
     `host_generic_reg_alloc3.c`, which is now the default allocator),
     `none/tests/Makefile.am`, `tests/check_headers_and_includes`.
   - Pay special attention to any upstream change to guest-state layout
     (`libvex_guest_amd64.h`, `libvex_guest_x86.h`) or to the shadow-area
     size/alignment checks, since Fjalar enlarges the shadow area.

6. **Memcheck conflicts** in `valgrind/fjalar/`.
   - Resolve the conflicts (as for Coregrind), using Fjalar's changes in
     `valgrind/fjalar`, including files that upstream removed but
     Fjalar modified; `git rm`
     any that Fjalar does not need.  Remember part of `mc_translate.c`
     lives in `fjalar/mc_translate.h`.  Preserve the #73 edits to `mc_translate.c`
     and `memcheck.h`.
   - In `mc_translate.c`'s `MC_(instrument)`, check that every case has
     matching DynComp code and that new cases get a DynComp counterpart.
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
   - `git -C $INV/fjalar diff -b valgrind-merge/base valgrind-merge/new -- valgrind/VEX/pub/libvex_ir.h`
     and hand-port relevant hunks of
     `git diff valgrind-merge/base valgrind-merge/new -- valgrind/fjalar/mc_translate.c`
     into
     `fjalar/kvasir/dyncomp_translate.c` (`_DC` functions).
   - For every new or renamed `IROp`, `IRExpr`, or `IRStmt` kind relevant to
     amd64/x86, add handling in the `expr2tags_*_DC` functions (see the
     #79 `Iop_64x4toV256` fix for the pattern).  Search for panics/`default:`
     cases that would now be hit.  Most changes for other architectures can
     be ignored.  `valgrind/fjalar/tests/dyncomp-op-coverage-test.sh` (from
     #173; `make fjalar-test` runs it) lists each new IROp that has no case,
     and each IROp listed as unimplemented that amd64 or x86 now uses.
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

9. **Test.**  Run these from `$INV/fjalar` (`cd $INV/fjalar`).
   - `./check-regtest.sh`.  The expected failures will change, because
     3.27.1 adds, removes, and fixes tests.  For each unexpected failure:
     if it is also in step 3's `regtest-upstream-3.27.1.txt`, it is an
     upstream failure, so add it to the expected list; otherwise it was
     probably caused by the merge, so fix it.  Remove expected failures
     that now pass.  `./check-regtest.sh --log regtest-<os>.log --update`
     rewrites the list; review its diff, which goes in the PR.
   - `make fjalar-test`.
   - `./test-kvasir.sh 2>&1 | tee kvasir-after.log` — compare with
     `kvasir-before.log` from step 1.  Address-related diffs
     (`<STACK_ADDR>` etc.) may require updating `clean-output.pl`.
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
     `$INV/fjalar/valgrind/inst/bin/valgrind --tool=fjalar --dyncomp --dyncomp-unhandled-ops=warn`,
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
     specific to that container or CPU.  To check, build upstream 3.27.1 in
     that container (e.g., `docker run` the CI image, clone
     `VALGRIND_3_27_1`, and run `make regtest` as in step 3) and compare.

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
    - Update `doc/valgrind-merge.texinfo`: dates/OS versions and any new
      pitfalls.  (The regtest baseline output pasted into the doc is
      superseded by `regtest-expected/*.txt`.)
    - Commit as one PR; save `valgrind-new` (it becomes `valgrind-old` for
      the next merge) and delete `valgrind-new-build`.

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
