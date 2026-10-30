# Plan: reduce Fjalar's differences from its version of Valgrind

The goal is to make the next Valgrind merges (`merge-valgrind.sh`, see
`doc/valgrind-merge.texinfo` and `plan-upgrade-valgrind.md`) produce fewer
conflicts and fewer silently lost changes.  Every line in which Fjalar's
copy of an upstream file differs from upstream is a potential conflict and
an item that `compare-fjalar-changes.sh` reports and that a person must
check.  This plan reduces the differences between Fjalar and the Valgrind
version that Fjalar is based on, **3.23.0** (`valgrind/REVISION`), not the
latest Valgrind.

## Ordering

Do this work before the 3.23.0 -> 3.27.1 upgrade (`plan-upgrade-valgrind.md`).
Every difference removed here is one fewer conflict to resolve in that
merge.

## Status

Steps 0-8 have landed:  #190 (Step 0, a script that measures the
differences, and a CI check that upstream files keep upstream's
whitespace), #182 (Step 1, file types and modes), #183 (Step 2,
whitespace), #184 (Step 3, cosmetic edits), #191 (Step 4, unneeded changes
to the Memcheck copies), #192 (Step 5, a single switch for each disabled
part of Memcheck), #193 (Step 6a, `mc_include.h`), #194 (Step 6b, Fjalar's
functions in `mc_main.c`), #221 (Step 6c, Memcheck's definitions restored
to `mc_translate.c`), #197 (Step 6d, DynComp in `MC_(instrument)`), #195
(Step 7a, the guest-layout fields and `VEX_N_FXSTATE`), #196 (Step 7b, the
register accessors), #220 (Step 7c, the file functions), #206 (Step 7d,
the function-name printing in VEX), and #205 (Step 8, the changes that
must remain), with its companion codespecs/daikon#955.  So did PR #181,
which restored upstream's `AC_INIT` version string.

Only Step 9 (documentation) remains.  It is unblocked.

## The remaining differences

`diff-from-valgrind.sh` prints the differences from the tree that
`merge-valgrind.sh` uses as the base of a merge:  upstream
`VALGRIND_3_23_0` at `valgrind/`, plus upstream `memcheck/` (without
`docs/`, `tests/`, and `Makefile.am`) at `valgrind/fjalar/`.  It omits the
files that only Fjalar has (Fjalar's own sources and Binutils-derived
files).

Measured at commit 23bfcf99 (after Step 4), the differences were in 26
files, with 1054 lines added and 266 removed.  Measured at commit 8efd1baa
(after Steps 7 and 8, before Step 6c), they were in 15 files, with 226
lines added and 203 removed.  Step 6c restored about 180 lines to
`mc_translate.c`; measure again (`diff-from-valgrind.sh --shortstat`) as
part of Step 9.

What remains is Fjalar's essential hooks:

- the extra shadow area for DynComp tags (`pub_core_threadstate.h`, the
  spill offset in `host_generic_reg_alloc2.c` and
  `host_generic_reg_alloc3.c`, and the assertion in `scheduler.c`);
- the build integration (`configure.ac`, `Makefile.am`, and
  `tests/check_headers_and_includes`);
- the extra-shadow tag accessor `VG_(get_tag_ptr_for_guest_offset)`
  (`m_machine.c` and `pub_core_machine.h`);
- the DynComp and Fjalar hooks in `mc_main.c` and `mc_translate.c`,
  including the `CHECK_SP` calls in the `mc_new_mem_stack_*` functions;
- `memcheck.h`, which includes `pub_tool_clreq.h` instead of upstream's
  `valgrind.h`, as `tests/check_headers_and_includes` requires of a file in
  a tool directory.

Edits that no step covered, in `mc_main.c` and `mc_translate.c` (about 70
lines):  a Fjalar header comment at the top of each file; in `mc_main.c`, a
`DEBUG` macro that `MAX_DEBUG_INFO` enables, casts to `void *` in its
calls, extra `DEBUG` calls, `#undef`s of `SM_OFF`, `SM_OFF_16`, and
`INLINE`, and the renaming of a parameter `str` to `astr`; and in
`MC_(instrument)`, 2 copies of a 9-line block that prints registers when
`fjalar_print_IR` is set.  A later PR could remove them.

## Principles

1. Prefer, in order:  no change to the upstream file; Fjalar code in a
   Fjalar-owned file; a minimal hook (ideally one line, adjacent to as
   little upstream text as possible) in the upstream file.
2. In upstream files, keep upstream's text byte for byte, including
   whitespace, names, comments, copyright years, and typos.  Send fixes of
   upstream bugs or typos upstream instead.
3. Fjalar supports only amd64-linux (#121), but keep the functionality of
   its x86-only changes.

## Step 9: documentation

- Update the "Valgrind modifications" appendix of
  `doc/valgrind-merge.texinfo` and step 5 of `plan-upgrade-valgrind.md`,
  which list Fjalar's changes to Coregrind, to match what remains (see
  "The remaining differences" above).
- Add `diff-from-valgrind.sh` to the merge procedure:  run it before and
  after a merge, and expect only the documented changes.
- After each Valgrind merge, check `.alwaysDefd` in
  `guest_amd64_helpers.c`:  Memcheck's `isAlwaysDefd` panics if an
  `fxState` range partly overlaps an always-defined part of the guest
  state.  In 3.23.0, the range `guest_RAX` through `guest_R15` that
  `fjalar_main.c` passes overlaps none.

## Not recommended

- **Compiling unmodified Memcheck files from `valgrind/memcheck/`** instead
  of keeping copies in `valgrind/fjalar/`.  `merge-valgrind.sh` already
  merges the copies, and a copy that is identical to upstream never
  conflicts, so this would save little and would complicate the build.
- **Running DynComp as a separate instrumentation pass** instead of
  interleaving it with Memcheck's.  It would remove the hooks from
  `MC_(instrument)`, but Memcheck would then instrument DynComp's helper
  calls, and the IR order would change; the risk is too high for the gain.
