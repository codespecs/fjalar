# Plan: preparation before the Binutils/readelf and Valgrind upgrades

These changes are independent of both upgrades (`plan-upgrade-readelf.md`,
`plan-upgrade-valgrind.md`).  Doing them first, as separate PRs, makes both
upgrades smaller and easier to review, and makes future merges cheaper.
Each upgrade plan's "Ordering" section says which of these items it
requires; neither requires all of them.

Below, `$INV/fjalar` means the Fjalar tree being changed.

Both upgrades should wait for the open PRs that change files that the
upgrades merge into; the "Current state" section of each upgrade plan
says how to list them.

## 1. Enforce the expected regtest failures in CI

Fjalar's CI runs Valgrind's regression tests, but its jobs only report
the failures.

1. Push a branch and let the regtest jobs run.  Download the
   `regtest-results-*` artifacts:  either download each one's `.zip` file
   from the run's page and unzip it into its own directory, or run
   `gh run download <run-id>`, which puts each artifact in its own
   directory.  In each artifact's directory, which contains
   `regtest-<os>.log` and `regtest-<os>-post.log`, run
   `$INV/fjalar/check-regtest.sh --log regtest-<os>.log --expected $INV/fjalar/regtest-expected/<os>.txt --update`,
   which writes the observed failures to the list, after a header that
   explains the format and how to regenerate the list.
2. Re-run the jobs at least twice more.  Any test whose result differs
   between runs (timing-dependent tests such as helgrind or `fdleak`, or
   CPU-dependent tests such as AVX-512 ones; the job logs the CPU) gets a
   `?` prefix.
3. Remove `--report-only` from both CI jobs (the TODO comments in
   `.github/workflows/ci.yml`) and commit the lists.

Done when:  CI enforces the lists on both distributions and is green.

## 2. Look for DynComp panics on unhandled IROps, now, on Valgrind 3.23

\#87 made `expr2tags_Unop_DC` switch on the operation and cover all 283
unary operations, so unary operations no longer silently pass their
operand's tag through.

Why: the main runtime risk of the Valgrind upgrade is IROps that
`fjalar/kvasir/dyncomp_translate.c` does not handle; #79 was one, found by
accident.  Finding them on 3.23 means they can be fixed separately, and any
panic after the upgrade can then be blamed on the upgrade.

What:

- Write a few small C programs whose hot loops vectorize (array sums,
  `memcpy`/`memset`/string functions, float and integer arithmetic), compile
  them with `-O2 -march=x86-64-v3` (AVX2) and also `-O3 -march=x86-64-v3`,
  and run them under Kvasir with DynComp
  (`$INV/fjalar/valgrind/inst/bin/valgrind --tool=fjalar --dyncomp --dyncomp-unhandled-ops=warn ./prog`).
  Do not use `$DAIKONDIR/scripts/kvasir-dtrace`:  it runs the Kvasir in
  `$DAIKONDIR/fjalar`, which may be a different tree than the one being
  changed.  After changing `dyncomp_translate.c`, run
  `make -C $INV/fjalar/valgrind/fjalar install`, because
  `valgrind/inst/bin/valgrind` runs the installed tool.
  `warn` reports each unhandled operation once and continues, so one run
  lists every unhandled operation a program hits, instead of stopping at
  the first.
  Do not use `-march=native` or `-march=x86-64-v4`:  on a machine with
  AVX-512, they emit AVX-512 instructions, which Valgrind 3.23 cannot
  decode, so the program dies with SIGILL before DynComp sees its IROps.
- Fix each panic in its own PR, following #79's pattern.
- Running programs finds only the operations those programs use.  So, in
  its own PR, extend `valgrind/fjalar/tests/dyncomp-unop-coverage-test.sh`
  (which `make fjalar-test` runs) to binary, ternary, and quaternary
  operations.  It takes each operation's arity from `typeOfPrimop` in
  VEX's `ir_defs.c` and checks that `expr2tags_Unop_DC` has a case for
  exactly the unary operations; check `expr2tags_Binop_DC`,
  `expr2tags_Triop_DC`, and `expr2tags_Qop_DC` too.  The test's parser
  needs two changes.  First, it finds `expr2tags_Unop_DC` by its return
  type, `IRExpr*`, but the other three functions return `IRAtom*`.
  Second, `expr2tags_Binop_DC`, `expr2tags_Triop_DC`, and
  `expr2tags_Qop_DC` each have a section
  headed `// Unimplemented` whose case labels (such as `Iop_Rotx32`) fall
  through to the `default` case, which by default panics; the test must
  not count those as handled.  Move them to the comment of
  `dyncomp_translate.c` that lists the operations that DynComp does not
  implement.  Many operations of other architectures have no case, on
  purpose; the test must accept those that are listed, as case labels, in
  that comment.  Fix the operations relevant to amd64/x86 that the test
  reports, and add the others to that comment (on 3.23, these include
  `Iop_MulHi8Sx16` and `Iop_MulHi8Ux16`, which only s390 uses).  After the Valgrind upgrade, the test
  then lists each new operation that DynComp does not handle.  Describe
  the test in appendix "Supporting new VEX IR Instruction" of
  `doc/valgrind-merge.texinfo`.
- Add one such program to Daikon's Kvasir tests (`tests/kvasir-tests`, in the
  Daikon repository), compiled with `-march=x86-64-v3`, so CI exercises
  AVX2 IROps.  GitHub's runners support AVX2; check that before relying on it
  (the Kvasir CI jobs log the CPU flags).
