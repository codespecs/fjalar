// Test input for dyncomp-interactions-units-test.sh.

// less() compares its parameters with a cmp instruction whose condition
// code is read by a setl instruction in a different basic block.  VEX
// translates the setl into a call to amd64g_calculate_condition, whose
// arguments include the operands of the comparison.  Under
// --dyncomp-interactions=units, DynComp should make a and b comparable.
int less(int a, int b) {
  unsigned char result;
  __asm__ volatile ("cmpl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsetl %0"
                    : "=q" (result) : "r" (a), "r" (b) : "cc");
  return result;
}

// lessMask() compares its parameters with a cmp instruction whose carry is
// read by an sbb instruction in a different basic block, as in the idiom
// mask = -(a < b) for unsigned a and b.  VEX translates the read of the
// carry into a call to amd64g_calculate_rflags_c, whose arguments include
// the operands of the comparison.  Under --dyncomp-interactions=units,
// DynComp should make a and b comparable.
int lessMask(unsigned a, unsigned b) {
  int mask;
  __asm__ volatile ("cmpl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsbbl %0, %0"
                    : "=r" (mask) : "r" (a), "r" (b) : "cc");
  return mask;
}

// overflow() multiplies a and b with an imul instruction whose overflow flag
// is read by a seto instruction in a different basic block.  VEX translates
// the seto into a call to amd64g_calculate_condition, whose arguments include
// the operands of the multiplication.  The operands of a multiplication need
// not have the same units, so under --dyncomp-interactions=units, DynComp
// should not make a and b comparable.
int overflow(int a, int b) {
  unsigned char result;
  __asm__ volatile ("imull %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tseto %0"
                    : "=q" (result), "+r" (a) : "r" (b) : "cc");
  return result;
}

// mulThenLahf() multiplies a and b with an imul instruction, and then a lahf
// instruction in a different basic block copies the flags of the
// multiplication (via amd64g_calculate_rflags_all) into a register.  Copying
// flags is not an interaction, and the operands of a multiplication need not
// have the same units, so under --dyncomp-interactions=units, DynComp should
// not make a and b comparable.
int mulThenLahf(int a, int b) {
  int flags;
  __asm__ volatile ("imull %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tlahf\n\t"
                    "movzbl %%ah, %0"
                    : "=r" (flags), "+r" (a) : "r" (b) : "cc", "rax");
  return flags;
}

// absDiffSum() computes the sum of the absolute differences of the bytes of
// a and b with a psadbw instruction.  VEX translates the psadbw into a call
// to amd64g_calculate_mmx_psadbw, which does not read flags.  Subtraction is
// an interaction under --dyncomp-interactions=units, so DynComp should make
// a and b comparable.
long absDiffSum(long a, long b) {
  long result;
  __asm__ volatile ("movq %1, %%mm0\n\t"
                    "movq %2, %%mm1\n\t"
                    "psadbw %%mm1, %%mm0\n\t"
                    "movq %%mm0, %0\n\t"
                    "emms"
                    : "=r" (result) : "r" (a), "r" (b) : "mm0", "mm1");
  return result;
}

int main(void) {
  less(1, 2);
  lessMask(7, 8);
  overflow(3, 4);
  mulThenLahf(9, 10);
  absDiffSum(5, 6);
  return 0;
}
