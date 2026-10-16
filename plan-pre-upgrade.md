# Plan: preparation before the Binutils/readelf and Valgrind upgrades

These changes are independent of both upgrades (`plan-upgrade-readelf.md`,
`plan-upgrade-valgrind.md`).  Doing them first, as separate PRs, makes both
upgrades smaller and easier to review, and makes future merges cheaper.
Both upgrade plans assume these are done.

Below, `$INV/fjalar` means the Fjalar tree being changed.

Suggested PRs, in order:
1. Valgrind regtest in CI, report-only (item 1): PR #96, which also adds
   these plans.
2. Remove files that upstream deleted (item 7).  Do this before
   bootstrapping item 1's expected-failure lists, because it changes which
   tests fail.
3. Commit the expected-failure lists and make the regtest jobs enforce
   them (item 1, "Remaining").
4. `make git-update` and `generate-patch-files.sh` fixes (items 2 and 3).
5. DynComp scan for unhandled IROps (item 4); one PR per bug found.
6. Merge-doc updates (item 5), possibly together with PR 4.

Item 6 is a quick investigation with no code change; do it any time before
step 4 of the readelf plan.

## 1. Run Valgrind's regression tests in CI, against expected failures

Status: script and CI jobs written, in PR #96.  Tested end to end on a
Rocky Linux 10 host (not the CI container): 813 tests; failures were 14
`gdbserver_tests` (no glibc debuginfo), `cachegrind/tests/ann1` and `diff`,
`memcheck/tests/memalign2` (the last three are stale tests; see item 7),
`memcheck/tests/origin6-fp`, `none/tests/libvex_test`,
`none/tests/libvexmultiarch_test`, and 29 post-test-check errors (mostly
item 7; also two Fjalar include-rule violations).  Expected-failure lists
not yet bootstrapped.

Why: both upgrade plans currently check Valgrind's regression tests by
comparing `test-before.log` and `test-after.log` by eye.  More merges are
expected after these two, so automating the check pays for itself.

What (done):
- `check-regtest.sh` runs `make test`, extracts the failing tests from the
  `vg_regtest` summary, and compares them with
  `regtest-expected/<os>.txt` (`<os>` from `/etc/os-release`, e.g.
  `ubuntu-26.04`, `rocky-10`).  It fails on an unexpected failure or if the
  tests did not run; it warns about expected failures that passed.  A `?`
  prefix marks a test that may or may not fail.  `--update` regenerates the
  list (keeping comments and `?` lines); `--log FILE` parses an existing log;
  `--report-only` never fails.  It also reports each error from the
  post-test checks (makefile consistency, headers) as its own entry,
  `post_regtest_checks: MESSAGE`, so a new error is not hidden by an old one.
- `make check-regtest` runs it.
- CI jobs `regtest_ubuntu_26_04` and `regtest_rocky_10` build Fjalar and run
  `./check-regtest.sh --report-only`, uploading `regtest-observed-*.txt` and
  the log as an artifact.
- `test.sh`'s commented-out `make test` now points to the script.
- `.gitignore`: ignores the script's output, and 45 test binaries (tests
  added in the 3.23 merge) that were missing from it; removes a corrupted
  line (`valgrind/cachegrind/tests/clreqvalgrind/tests/filter_discards`,
  two entries joined by a missing newline; both are listed separately).

Remaining:
1. After #96 and item 7 are merged, push a branch and let the regtest jobs
   run.  Download the
   `regtest-results-*` artifacts and copy each `regtest-observed-<os>.txt`
   to `regtest-expected/<os>.txt` (or run
   `./check-regtest.sh --log regtest-<os>.log --expected regtest-expected/<os>.txt --update`).
2. Re-run the jobs at least twice more.  Any test whose result differs
   between runs (timing-dependent tests such as helgrind or `fdleak`, or
   CPU-dependent tests such as AVX-512 ones; the job logs the CPU) gets a `?`
   prefix.
3. Remove `--report-only` from both CI jobs (the TODO comments in
   `.github/workflows/ci.yml`) and commit the lists.
4. Optional: install `gdb` and glibc debuginfo in the Daikon Docker images
   (in the Daikon repository), which makes most `gdbserver_tests` pass, then
   regenerate the lists.  This makes the regtest a more sensitive check.
5. Update `doc/valgrind-merge.texinfo` ("Get New Valgrind Regtest Baseline
   Results", "Testing Valgrind") to describe `check-regtest.sh`; see item 5.

Done when: CI enforces the lists on both distros and is green.

## 2. Fix the memcheck part of `make git-update`

Why: the coregrind part of `git-update` (`Makefile`) prints `git add` /
`git rm` commands, but the memcheck part:
- prints `add ...` / `remove ...`, which are not commands;
- prints `valgrind/memcheck/...` paths, but Fjalar's copy of memcheck is
  `valgrind/fjalar/`;
- has a `remove` branch (matching `+++ ... 1969-12-31`) that never fires,
  because `generate-patch-files.sh` uses `--unidirectional-new-file`.

What:
- For files new upstream (lines `--- valgrind-old/memcheck/X ... 1969-12-31`
  in `memcheck.patch`), print `git add valgrind/fjalar/X`.
- For files removed upstream (lines `Only in valgrind-old/memcheck...: X` in
  `memcheck.patch`), print `git rm valgrind/fjalar/X`.  (`memcheck.patch`
  excludes `docs` and `tests`, so these are source files.)
- The output is still reviewed by hand: Fjalar may not want every new
  memcheck file, and a removed memcheck file may have Fjalar changes.

Test: in a scratch `$INV`, run `generate-patch-files.sh` on two existing
Valgrind tags between which memcheck source files were both added and
removed (find such a pair with
`diff -qr -xdocs -xtests valgrind-old/memcheck valgrind-new/memcheck`), and
check the commands `make git-update` prints.

## 3. Make `generate-patch-files.sh` check its inputs

Why: any build product in `valgrind-old` or `valgrind-new` silently ends up
in `coregrind.patch` and is then `git add`ed by `make git-update`.  Also,
with `$INV` unset, `cd $INV` goes to `$HOME`.

What: at the top of the script,
- fail if `$INV` is unset or `$INV/valgrind-old`, `$INV/valgrind-new`, or
  `$INV/fjalar/valgrind` is missing;
- fail if `git -C $INV/valgrind-old status --porcelain --ignored` or the
  same for `valgrind-new` prints anything (build products present);
- add `set -e`.

## 4. Look for DynComp panics on unhandled IROps, now, on Valgrind 3.23

Why: the main runtime risk of the Valgrind upgrade is IROps that
`fjalar/kvasir/dyncomp_translate.c` does not handle; #79 was one, found by
accident.  Finding them on 3.23 means they can be fixed separately, and any
panic after the upgrade can then be blamed on the upgrade.

What:
- Write a few small C programs whose hot loops vectorize (array sums,
  `memcpy`/`memset`/string functions, float and integer arithmetic), compile
  them with `-O2 -march=x86-64-v3` (AVX2) and also `-O3 -march=native`, and
  run them under Kvasir with DynComp
  (`$DAIKONDIR/scripts/kvasir-dtrace --dyncomp ./prog`).
- Fix each panic in its own PR, following #79's pattern.
- Running programs finds only some problems: `expr2tags_Binop_DC`,
  `expr2tags_Triop_DC`, and `expr2tags_Qop_DC` panic on an unhandled
  operation, but `expr2tags_Unop_DC` silently passes the operand's tag
  through (see "Supporting new VEX IR Instruction" in the merge doc, as
  updated by #82).  So also compare the `Iop_*` values that are amd64/x86
  relevant in `VEX/pub/libvex_ir.h` against the cases those four functions
  handle, and check each unhandled unary op whose result should not be
  comparable to its operand.
- Add one such program to Daikon's Kvasir tests (`tests/kvasir-tests`, in the
  Daikon repository), compiled with `-march=x86-64-v3`, so CI exercises
  AVX2 IROps.  GitHub's runners support AVX2; check that before relying on it
  (the Kvasir CI jobs log the CPU flags).

## 5. Update `doc/valgrind-merge.texinfo` with what is already known

Why: so that neither upgrade plan has to say "the doc says X, but do Y".

What:
- #82 (merged after this plan was first written) already fixed http URLs
  and typos, made the doc use `$DAIKONDIR` (set to `$INV/daikon`), and
  documented that `expr2tags_Unop_DC` does not panic.  Pull it before
  editing the doc.
- The doc's three direct runs of `$DAIKONDIR/tests/kvasir-tests` ("Verify
  current sources pass the regression tests", "Merging the binutils
  changes", "Testing Fjalar") test whatever `$DAIKONDIR/fjalar` points to.
  Say to use `./test-kvasir.sh`, or to check
  `readlink -f $DAIKONDIR/fjalar` first.
- "Get New Valgrind Regtest Baseline Results": build the upstream baseline
  in a copy of `valgrind-new`, never in `valgrind-new` itself (build products
  would end up in `coregrind.patch`).
- "Remove files that have been removed upstream": also handle files removed
  from `memcheck/`, whose counterparts are in `valgrind/fjalar/`.
- "Merging the binutils changes": `--merge=diff3` produces inline conflict
  markers, not `.rej` files (the `meld` instructions refer to `.rej` files);
  add checking that 2.4x code compiles against the oldest system `bfd.h` in
  CI (item 6), and the SFrame and zstd handling.
- Describe `check-regtest.sh` and `make check-regtest` (item 1) in the
  regtest sections, replacing comparing logs by eye.
- Describe the fixed `make git-update` (item 2).
- "Remove files that have been removed upstream": add a check, to run after
  the merge, that Fjalar tracks no upstream file that upstream deleted
  (item 7's command).
- The doc says new test drivers go in the "Ignore generated test drivers"
  section of `.gitignore`, but there is no such section; binaries are
  listed in per-tool sections (`# /memcheck/` etc.).

## 6. Record the `bfd.h` version in each CI container

Why: `dwarf.c`, `readelf.c`, and `elfcomm.c` include the system `bfd.h`.
Step 4 of the readelf plan checks that the 2.47 code uses only bfd macros
and functions that the oldest CI `bfd.h` provides; it needs to know which
version that is.

What: in each Docker image, run `rpm -q binutils-devel` (Rocky Linux) or
`dpkg -l binutils-dev` (Ubuntu), and record the versions in the readelf plan
(step 4).  Optionally, also print it in the CI "System information" step.

## 7. Remove upstream files that upstream deleted but Fjalar still tracks

Why: past merges skipped the doc's "Remove files that have been removed
upstream" step.  Comparing `git ls-files valgrind` (excluding
`valgrind/fjalar/`) with upstream `VALGRIND_3_23_0` finds 32 tracked files
that upstream no longer has, some left over since the 3.8.1 merge (2013).
They cause real test failures:
- stale `.vgtest` files make `cachegrind/tests/ann1`,
  `cachegrind/tests/diff`, and `memcheck/tests/memalign2` run and fail;
- they cause 27 of the 29 post-test-check errors ("... is missing in
  EXTRA_DIST").

The files: `cachegrind/cg_merge.c`; `cachegrind/tests/{ann1,diff}.*`,
`cgout-test`, `cgout-test2`; `helgrind/tests/pth_destroy_cond.stderr.exp2`;
four `massif/tests/*.post.exp-*freebsd*`; in `memcheck/tests/`:
`memalign2.{c,stderr.exp,vgtest}`, `filter_sized_delete`,
`memcmptest.stderr.exp2`, and seven FreeBSD `.exp` files;
`none/tests/arm64/memory.*`; `none/tests/s390x/op00.stderr.exp{1,2}`.

What:
```sh
git clone -b VALGRIND_3_23_0 --depth 1 https://sourceware.org/git/valgrind.git /tmp/v323
cd $INV/fjalar
comm -23 <(git ls-files valgrind | sed 's|^valgrind/||' | grep -v '^fjalar/' | sort) \
         <(git -C /tmp/v323 ls-files | sort) | grep -vx REVISION
```
Review the list (`REVISION` is Fjalar's own; check that no other entry is a
Fjalar addition), `git rm` them, rebuild, and re-run `./check-regtest.sh`.
The remaining two post-test-check errors are Fjalar's own
(`fjalar/mc_main.c` includes `pub_core_aspacemgr.h`, `fjalar/typedata.c`
includes `pub_core_mallocfree.h`); either exempt them in
`valgrind/tests/check_headers_and_includes` or leave them in the
expected-failures lists.

Done when: the `comm` command prints nothing, and the three stale tests no
longer run.
