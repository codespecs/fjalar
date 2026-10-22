// Test input for dyncomp-interactions-comparisons-test.sh.

// less() compares its parameters with a cmp instruction whose condition
// code is read by a setl instruction in a different basic block.  VEX
// translates the setl into a call to amd64g_calculate_condition, whose
// arguments include the operands of the comparison.  Under
// --dyncomp-interactions=comparisons, DynComp should make a and b
// comparable.
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
// the operands of the comparison.  Under --dyncomp-interactions=comparisons,
// DynComp should make a and b comparable.
int lessMask(unsigned a, unsigned b) {
  int mask;
  __asm__ volatile ("cmpl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsbbl %0, %0"
                    : "=r" (mask) : "r" (a), "r" (b) : "cc");
  return mask;
}

// lessWide() compares two 128-bit signed integers, given as their low and
// high halves, as a compiler compares two __int128 values:  a cmp
// instruction compares the low halves, an sbb instruction subtracts the
// high halves and the borrow, and a setl instruction reads the result.
// Each instruction is in a different basic block.  The sbb reads the
// carry of the cmp via amd64g_calculate_rflags_c, and the setl reads the
// flags of the sbb via amd64g_calculate_condition, whose arguments include
// the high halves.  Under --dyncomp-interactions=comparisons, DynComp
// should make aLo and bLo comparable, and aHi and bHi comparable.
//
// *** KNOWN LIMITATION:  DynComp makes aLo and bLo comparable, but NOT aHi
// *** and bHi.  The .goal file records this current, incorrect behavior.
// *** The flags read by the setl are those of the sbb, whose thunk holds
// *** bHi xor the old carry rather than bHi, and that xor gets tag 0
// *** because it is not an interaction.  See the comment above
// *** dyncomp_cc_op_is_sub in kvasir/dyncomp_main.c.  If DynComp is fixed,
// *** change aHi and bHi in the .goal file to have the same comparability.
int lessWide(long aLo, long aHi, long bLo, long bHi) {
  unsigned char result;
  long hi = aHi;
  __asm__ volatile ("cmpq %3, %2\n\t"
                    "jmp 1f\n"
                    "1:\tsbbq %4, %1\n\t"
                    "jmp 2f\n"
                    "2:\tsetl %0"
                    : "=q" (result), "+r" (hi)
                    : "r" (aLo), "r" (bLo), "r" (bHi) : "cc");
  return result;
}

// carry() adds a and b with an add instruction whose carry is read by a setc
// instruction in a different basic block.  VEX translates the setc into a
// call to amd64g_calculate_condition, whose arguments include the operands
// of the add.  An addition is not a comparison, so under
// --dyncomp-interactions=comparisons, DynComp should not make a and b
// comparable.
int carry(int a, int b) {
  unsigned char result;
  __asm__ volatile ("addl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsetc %0"
                    : "=q" (result), "+r" (a) : "r" (b) : "cc");
  return result;
}

// addWithCarry() adds a and b with an add instruction whose carry is read
// by an adc instruction in a different basic block.  VEX translates the
// read of the carry into a call to amd64g_calculate_rflags_c, whose
// arguments include the operands of the add.  An addition is not a
// comparison, so under --dyncomp-interactions=comparisons, DynComp should
// not make a and b comparable.
int addWithCarry(int a, int b, int c, int d) {
  __asm__ volatile ("addl %2, %0\n\t"
                    "jmp 1f\n"
                    "1:\tadcl %3, %1"
                    : "+r" (a), "+r" (c) : "r" (b), "r" (d) : "cc");
  return c;
}

// subThenLahf() subtracts b from a with a sub instruction, and then a lahf
// instruction in a different basic block copies the flags of the subtraction
// (via amd64g_calculate_rflags_all) into a register.  Copying flags is not a
// comparison, so under --dyncomp-interactions=comparisons, DynComp should not
// make a and b comparable.
int subThenLahf(int a, int b) {
  int flags;
  __asm__ volatile ("subl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tlahf\n\t"
                    "movzbl %%ah, %0"
                    : "=r" (flags), "+r" (a) : "r" (b) : "cc", "rax");
  return flags;
}

int main(void) {
  less(1, 2);
  lessMask(3, 4);
  lessWide(20, 21, 22, 23);
  carry(5, 6);
  addWithCarry(7, 8, 9, 10);
  subThenLahf(18, 19);
  return 0;
}
