# Plan: preparation before the Binutils/readelf and Valgrind upgrades

These changes are independent of both upgrades (`plan-upgrade-readelf.md`,
`plan-upgrade-valgrind.md`).  Doing them first, as separate PRs, makes both
upgrades smaller and easier to review, and makes future merges cheaper.
Each upgrade plan's "Ordering" section says which of these items it
requires; neither requires all of them.

Below, `$INV/fjalar` means the Fjalar tree being changed.

Items 3, 5, and 7 are done:  #99, #101, and #98 have landed.  Item 6 is
done too, by #96.  Item 1's pull request,
#96, has landed, but follow-up work remains.  Item 2 is an open pull
request; its description gives the details.  Item 4 is described here.
Other open PRs that both
upgrades should wait for, because they change files that the upgrades
merge into, are listed in the "Current state" section of each upgrade
plan.

## 1. Run Valgrind's regression tests in CI, against expected failures

#96, which has landed.  (#102, which has also landed, makes Valgrind's test programs build with
GCC 15 on Ubuntu 26.04.)  #96's CI jobs only report the failures.

Remaining:
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
`git apply --3way`.  It builds on #113 (generate
`valgrind/fjalar/Makefile.am` from Memcheck's), which has landed.

## 3. Make `generate-patch-files.sh` check its inputs

Done:  #99 has landed.

## 4. Look for DynComp panics on unhandled IROps, now, on Valgrind 3.23

Status: #85 and #86 have landed; #87 is open.  Do the rest after #87
lands.
- #85 adds `--dyncomp-unhandled-ops=panic|warn`; `warn` reports each
  unhandled binary, ternary, or quaternary operation once and continues.
  That makes the scan below much faster: one run lists every unhandled
  operation a program hits, instead of stopping at the first.
- #86 (landed) and #87 (open) make `expr2tags_Unop_DC` switch on the operation and cover
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
  them with `-O2 -march=x86-64-v3` (AVX2) and also `-O3 -march=x86-64-v3`,
  and run them under Kvasir with DynComp
  (`$DAIKONDIR/scripts/kvasir-dtrace --dyncomp --dyncomp-unhandled-ops=warn ./prog`).
  Do not use `-march=native` or `-march=x86-64-v4`:  on a machine with
  AVX-512, they emit AVX-512 instructions, which Valgrind 3.23 cannot
  decode, so the program dies with SIGILL before DynComp sees its IROps.
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
#98, #113, and #127 (all landed) and #103 also update the merge doc.

## 6. Record the `bfd.h` version in each CI container

Status: done.  #96's regtest jobs log it.  On 2026-10-17 (in #96's CI
logs, and from `docker run --rm --pull=always IMAGE rpm -q binutils-devel`
or `dpkg-query -W binutils-dev`):
- Ubuntu 26.04 (`daikon-ubuntu-jdk11-plus`): `binutils-dev` 2.46-3ubuntu2.
- Rocky Linux 10 (`daikon-rockylinux-jdk25-plus`): `binutils-devel`
  2.41-63.el10.

So the oldest `bfd.h` in CI is from Binutils 2.41.

Why: `dwarf.c` and `readelf.c` include the system `bfd.h`.  (So does
upstream's `elfcomm.c`, but in Fjalar's copy that `#include` is inside
`#if 0`.)
Step 4 of the readelf plan checks that the 2.47 code uses only bfd macros
and functions that the oldest CI `bfd.h` provides; it needs to know which
version that is.

What: the CI "System information" step of each regtest job runs
`rpm -q binutils-devel` (Rocky Linux) or `dpkg-query -W binutils-dev`
(Ubuntu).  Step 4 of the readelf plan refers to the versions above.
#101 records the oldest one in the merge doc.

## 7. Remove upstream files that upstream deleted but Fjalar still tracks

Done:  #98 has landed.
