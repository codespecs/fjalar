# Plan: preparation before the Binutils/readelf and Valgrind upgrades

These changes are independent of both upgrades (`plan-upgrade-readelf.md`,
`plan-upgrade-valgrind.md`).  Doing them first, as separate PRs, makes both
upgrades smaller and easier to review, and makes future merges cheaper.
Both upgrade plans assume these are done.

Below, `$INV/fjalar` means the Fjalar tree being changed.

Items 3, 5, and 7 are done:  #99, #101, and #98 have landed.  Items 1
and 2 are open pull requests; their descriptions give the details.
Items 4 and 6 are described here.  Other open PRs that both
upgrades should wait for, because they change files that the upgrades
merge into, are listed in the "Current state" section of each upgrade
plan.

## 1. Run Valgrind's regression tests in CI, against expected failures

#96.  (#102, which has landed, makes Valgrind's test programs build with
GCC 15 on Ubuntu 26.04.)  Its CI jobs only report the failures.

Remaining, after #96 lands:
1. Rebuild and push the Daikon `-plus` Docker images, which Fjalar's CI
   uses (`scripts/Dockerfile-README.md` in Daikon), so that they contain
   `gdb` and glibc debuginfo, which codespecs/daikon#916 (landed) added.
   This makes most `gdbserver_tests` meaningful.  Ideally, do this before
   step 2, so that the lists are generated only once.
2. Push a branch and let the regtest jobs run.  Download the
   `regtest-results-*` artifacts and copy each `regtest-<os>-observed.txt`
   to `regtest-expected/<os>.txt`.
3. Re-run the jobs at least twice more.  Any test whose result differs
   between runs (timing-dependent tests such as helgrind or `fdleak`, or
   CPU-dependent tests such as AVX-512 ones; the job logs the CPU) gets a
   `?` prefix.
4. Remove `--report-only` from both CI jobs (the TODO comments in
   `.github/workflows/ci.yml`) and commit the lists.
5. Describe `check-regtest.sh` in `doc/valgrind-merge.texinfo` ("Get New
   Valgrind Regtest Baseline Results", "Testing Valgrind"), replacing the
   comparison of logs by eye.

Done when:  CI enforces the lists on both distributions and is green.

## 2. Add and remove files during the merge without `make git-update`

#103:  create the patch files with `git diff` and apply them with
`git apply --3way`.  It contains #113 (generate
`valgrind/fjalar/Makefile.am` from Memcheck's).

## 3. Make `generate-patch-files.sh` check its inputs

Done:  #99 has landed.

## 4. Look for DynComp panics on unhandled IROps, now, on Valgrind 3.23

Status: much of this is in open PRs; do the rest after they land.
- #85 adds `--dyncomp-unhandled-ops=panic|warn`; `warn` reports each
  unhandled binary, ternary, or quaternary operation once and continues.
  That makes the scan below much faster: one run lists every unhandled
  operation a program hits, instead of stopping at the first.
- #86 and #87 make `expr2tags_Unop_DC` switch on the operation and cover
  all 283 unary operations, so unary operations no longer silently pass
  their operand's tag through (the gap described below).
- #88, which has landed, handles more vector shifts that used to panic.

Why: the main runtime risk of the Valgrind upgrade is IROps that
`fjalar/kvasir/dyncomp_translate.c` does not handle; #79 was one, found by
accident.  Finding them on 3.23 means they can be fixed separately, and any
panic after the upgrade can then be blamed on the upgrade.

What:
- Write a few small C programs whose hot loops vectorize (array sums,
  `memcpy`/`memset`/string functions, float and integer arithmetic), compile
  them with `-O2 -march=x86-64-v3` (AVX2) and also `-O3 -march=native`, and
  run them under Kvasir with DynComp
  (`$DAIKONDIR/scripts/kvasir-dtrace --dyncomp --dyncomp-unhandled-ops=warn ./prog`,
  once #85 has landed).
- Fix each panic in its own PR, following #79's pattern.
- Running programs finds only the operations those programs use.  Also
  compare the `Iop_*` values relevant to amd64/x86 in `VEX/pub/libvex_ir.h`
  against the cases the four `expr2tags_*_DC` functions handle.  Before
  #86/#87, `expr2tags_Unop_DC` silently passed the operand's tag through
  for any unary operation (see "Supporting new VEX IR Instruction" in the
  merge doc, as updated by #82); after them, it handles each one
  explicitly, so this comparison is mainly for binary, ternary, and
  quaternary operations.
- Add one such program to Daikon's Kvasir tests (`tests/kvasir-tests`, in the
  Daikon repository), compiled with `-march=x86-64-v3`, so CI exercises
  AVX2 IROps.  GitHub's runners support AVX2; check that before relying on it
  (the Kvasir CI jobs log the CPU flags).

## 5. Update `doc/valgrind-merge.texinfo` with what is already known

Done:  #101 has landed.  Describing `check-regtest.sh` remains (item 1).
#98 and #127 (both landed), #103, and #113 also update the merge doc.

## 6. Record the `bfd.h` version in each CI container

Status: done.  #96's regtest jobs log it.  On 2026-10-17 (in #96's CI
logs, and from `docker run --rm --pull=always IMAGE rpm -q binutils-devel`
or `dpkg-query -W binutils-dev`):
- Ubuntu 26.04 (`daikon-ubuntu-jdk11-plus`): `binutils-dev` 2.46-3ubuntu2.
- Rocky Linux 10 (`daikon-rockylinux-jdk25-plus`): `binutils-devel`
  2.41-63.el10.

So the oldest `bfd.h` in CI is from Binutils 2.41.

Why: `dwarf.c`, `readelf.c`, and `elfcomm.c` include the system `bfd.h`.
Step 4 of the readelf plan checks that the 2.47 code uses only bfd macros
and functions that the oldest CI `bfd.h` provides; it needs to know which
version that is.

What: the CI "System information" step of each regtest job runs
`rpm -q binutils-devel` (Rocky Linux) or `dpkg-query -W binutils-dev`
(Ubuntu).  Step 4 of the readelf plan refers to the versions above.
#101 records the oldest one in the merge doc.

## 7. Remove upstream files that upstream deleted but Fjalar still tracks

Done:  #98 has landed.
