# Plan: preparation before the Binutils/readelf and Valgrind upgrades

These changes are independent of both upgrades (`plan-upgrade-readelf.md`,
`plan-upgrade-valgrind.md`).  Doing them first, as separate PRs, makes both
upgrades smaller and easier to review, and makes future merges cheaper.
Each upgrade plan's "Ordering" section says which of these items it
requires; neither requires all of them.

Status:  both items are done.

Below, `$INV/fjalar` means the Fjalar tree being changed.

Both upgrades should wait for the open PRs that change files that the
upgrades merge into; the "Current state" section of each upgrade plan
says how to list them.

## 1. Enforce the expected regtest failures in CI

Before this item, Fjalar's CI ran Valgrind's regression tests, but its
jobs only reported the failures.

Status:  done.  #175 commits `regtest-expected/ubuntu-26.04.txt` and
`regtest-expected/rocky-10.txt` and removes `--report-only` from both CI
jobs, so CI enforces the lists on both distributions.  The steps below
are how the lists were made; each list's header says how to regenerate
it.

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

Why: the main runtime risk of the Valgrind upgrade is IROps that
`fjalar/kvasir/dyncomp_translate.c` does not handle; #79 was one, found by
accident.  Finding them on 3.23 means they can be fixed separately, and any
panic after the upgrade can then be blamed on the upgrade.

Status:  done.  #172 and #173 landed.

- #172 fixes the one panic found.  amd64 translates `PMADDUBSW` (SSSE3)
  and `VPMADDUBSW` (AVX and AVX2) to `Iop_PwExtUSMulQAdd8x16`, which
  `expr2tags_Binop_DC` listed as unimplemented.  #172 also adds
  `dyncomp-vector-ops-test.sh`, which runs DynComp on a program that
  executes AVX2, FMA, and F16C instructions and checks that the program's
  IR contains the expected IROps; GitHub's runners have those features.
  This test replaces the program that this step planned to add to
  Daikon's Kvasir tests:  it runs in Fjalar's CI with the code that it
  tests, needs no goal files, and checks the IR so that it is not vacuous.
- #173 renames `dyncomp-unop-coverage-test.sh` to
  `dyncomp-op-coverage-test.sh` and makes it check all four arities.  An
  IROp that DynComp does not implement is now listed in the comment after
  `expr2tags_Unop_DC` rather than as a case label in an `// Unimplemented`
  section.  The test also checks that the amd64 and x86 front ends use
  none of the listed IROps; that check would have found #172's bug.
  `Iop_MulHi8Sx16` and `Iop_MulHi8Ux16`, which had neither a case nor a
  listing, are handled as multiplications rather than listed, because
  their tag behavior is obvious.  #173 also describes the test in appendix
  "Supporting new VEX IR Instruction" of `doc/valgrind-merge.texinfo`.
  After the Valgrind upgrade, the test reports each new IROp, and each
  listed IROp that amd64 or x86 starts to use.
- Running vectorized programs under DynComp found no other unhandled
  IROp.  The programs were five small ones (sums, integer arithmetic,
  floating-point arithmetic, string functions, and bit manipulation), each
  compiled with `-O2 -march=x86-64-v3`, `-O3 -march=x86-64-v3`,
  `-O3 -march=x86-64-v2`, and `-O3`, plus Daikon's `md5` and `bzip2` tests
  compiled with `-O3 -march=x86-64-v3`.  They exercised 258 distinct
  IROps, 84 of them on 256-bit vectors.
- Found along the way:  Fjalar crashed on any program with a `_Float16`
  or `__bf16` variable; #174 fixes that.  Fjalar also crashed on
  `long double`, `_Float128`, and `_Complex` variables.  #177 and #180 fix
  those:  Fjalar prints a `long double` or `_Float128` value converted to
  a `double` and omits such a return value, and it omits a `_Complex`
  value, which Daikon cannot represent.  #180 also omits the values of
  decimal floating-point types, complex integer types, and `_BitInt(N)`
  for N > 128, which crashed Fjalar too.

To repeat the exploration (for example, after the Valgrind upgrade),
compile each program with `-gdwarf-4 -no-pie`, because Fjalar does not read
DWARF 5 and recognizes a function's entry point only at the address in the
debugging information.  Do not use `-march=native` or `-march=x86-64-v4`
unless Valgrind decodes AVX-512:  on a machine with AVX-512, they emit
AVX-512 instructions, and Valgrind 3.23 cannot decode them, so the program
dies with SIGILL before DynComp sees its IROps.  Run each program with
`$INV/fjalar/valgrind/inst/bin/valgrind --tool=fjalar --dyncomp --dyncomp-unhandled-ops=warn`,
which reports each unhandled operation once and continues, instead of
stopping at the first; add `--trace-flags=01000000 --trace-notbelow=0` to
see which IROps a run exercised.  Do not use
`$DAIKONDIR/scripts/kvasir-dtrace`:  it runs the Kvasir in
`$DAIKONDIR/fjalar`, which may be a different tree.
