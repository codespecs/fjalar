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
// should make aLo and bLo comparable, and aHi and bHi comparable.  (The
// sbb's thunk holds bHi xor the old carry rather than bHi; see
// sbbSecondOperand_DC in kvasir/dyncomp_translate.c.)
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

// lessWideSameBlock() is like lessWide(), but the sbb and setl instructions
// are in the same basic block, as they are in compiled code.  VEX passes the
// xor in the sbb's thunk directly to amd64g_calculate_condition, rather than
// reading it from the guest state.  Under --dyncomp-interactions=comparisons,
// DynComp should make aLo and bLo comparable, and aHi and bHi comparable.
int lessWideSameBlock(long aLo, long aHi, long bLo, long bHi) {
  unsigned char result;
  long hi = aHi;
  __asm__ volatile ("cmpq %3, %2\n\t"
                    "jmp 1f\n"
                    "1:\tsbbq %4, %1\n\t"
                    "setl %0"
                    : "=q" (result), "+r" (hi)
                    : "r" (aLo), "r" (bLo), "r" (bHi) : "cc");
  return result;
}

// xorThenLess() compares c with a ^ b with a cmp instruction whose
// condition code is read by a setl instruction in a different basic block.
// The CC_DEP2 field of the cmp's thunk is the result of the xor, but the cmp
// is not an sbb, so DynComp should not treat a as an operand of the
// comparison.  An xor is not an interaction, so under
// --dyncomp-interactions=comparisons, DynComp should not make a, b, and c
// comparable.
int xorThenLess(long a, long b, long c) {
  unsigned char result;
  long x = a;
  __asm__ volatile ("xorq %2, %1\n\t"
                    "cmpq %1, %3\n\t"
                    "jmp 1f\n"
                    "1:\tsetl %0"
                    : "=q" (result), "+r" (x) : "r" (b), "r" (c) : "cc");
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

// subThenInc() subtracts b from a with a sub instruction, and then an inc
// instruction in a different basic block reads the carry flag of the
// subtraction (via amd64g_calculate_rflags_c), in order to preserve it.
// The inc does not use the flags as the result of a comparison, so under
// --dyncomp-interactions=comparisons, DynComp should not make a and b
// comparable.
int subThenInc(int a, int b, int c) {
  __asm__ volatile ("subl %2, %0\n\t"
                    "jmp 1f\n"
                    "1:\tincl %1"
                    : "+r" (a), "+r" (c) : "r" (b) : "cc");
  return c;
}

// subThenIncSameBlock() is like subThenInc(), but the inc is in the same
// basic block as the sub, so VEX specializes the read of the carry flag into
// a CmpLT32U of the operands of the sub.  The inc does not use the flags as
// the result of a comparison, so under --dyncomp-interactions=comparisons,
// DynComp should not make a and b comparable.
int subThenIncSameBlock(int a, int b, int c) {
  __asm__ volatile ("subl %2, %0\n\t"
                    "incl %1"
                    : "+r" (a), "+r" (c) : "r" (b) : "cc");
  return c;
}

// subSetbInc() subtracts b from a, and then, in the same basic block, a setb
// instruction reads the carry flag of the subtraction and an inc instruction
// preserves it.  The setb uses the flags as the result of a comparison, so
// under --dyncomp-interactions=comparisons, DynComp should make a and b
// comparable, even if VEX computes both reads of the carry flag with the
// same CmpLT32U.
int subSetbInc(int a, int b, int c) {
  unsigned char below;
  __asm__ volatile ("subl %3, %1\n\t"
                    "setb %0\n\t"
                    "incl %2"
                    : "=q" (below), "+r" (a), "+r" (c) : "r" (b) : "cc");
  return below;
}

// subIncJnz() is like subThenIncSameBlock(), but a jnz instruction in the
// same basic block reads the zero flag of the inc.  VEX translates the jnz
// into a call to amd64g_calculate_condition whose CC_NDEP argument is the
// carry flag of the sub, which the inc preserved.  The jnz does not read the
// carry flag, so under --dyncomp-interactions=comparisons, DynComp should
// not make a and b comparable.
int subIncJnz(int a, int b, int c) {
  __asm__ volatile ("subl %2, %0\n\t"
                    "incl %1\n\t"
                    "jnz 1f\n"
                    "1:"
                    : "+r" (a), "+r" (c) : "r" (b) : "cc");
  return c;
}

// subIncSetb() subtracts b from a, an inc instruction in the same basic block
// preserves the carry flag of the subtraction (via a CmpLT32U), and then a
// setb instruction in a different basic block reads that carry flag.  The
// setb uses the carry flag as the result of a comparison, so under
// --dyncomp-interactions=comparisons, DynComp should make a and b
// comparable.
int subIncSetb(int a, int b, int c) {
  unsigned char below;
  __asm__ volatile ("subl %3, %1\n\t"
                    "incl %2\n\t"
                    "jmp 1f\n"
                    "1:\tsetb %0"
                    : "=q" (below), "+r" (a), "+r" (c) : "r" (b) : "cc");
  return below;
}

// subThenIncSetb() is like subIncSetb(), but the sub, the inc, and the setb
// are each in a different basic block, so the inc reads the carry flag of
// the subtraction via amd64g_calculate_rflags_c.  Under
// --dyncomp-interactions=comparisons, DynComp should make a and b comparable.
int subThenIncSetb(int a, int b, int c) {
  unsigned char below;
  __asm__ volatile ("subl %3, %1\n\t"
                    "jmp 1f\n"
                    "1:\tincl %2\n\t"
                    "jmp 2f\n"
                    "2:\tsetb %0"
                    : "=q" (below), "+r" (a), "+r" (c) : "r" (b) : "cc");
  return below;
}

// subIncSetbSameBlock() is like subIncSetb(), but the setb is in the same
// basic block as the sub and the inc.  Under
// --dyncomp-interactions=comparisons, DynComp should make a and b comparable.
int subIncSetbSameBlock(int a, int b, int c) {
  unsigned char below;
  __asm__ volatile ("subl %3, %1\n\t"
                    "incl %2\n\t"
                    "setb %0"
                    : "=q" (below), "+r" (a), "+r" (c) : "r" (b) : "cc");
  return below;
}

// subbIncSetb() is like subIncSetb(), but the subtraction is of bytes, so
// the inc reads the carry flag of the subtraction via a CmpLT64U of its
// operands, each masked with 0xFF.  Under --dyncomp-interactions=comparisons,
// DynComp should make a and b comparable.
int subbIncSetb(unsigned char a, unsigned char b, int c) {
  unsigned char below;
  __asm__ volatile ("subb %3, %1\n\t"
                    "incl %2\n\t"
                    "jmp 1f\n"
                    "1:\tsetb %0"
                    : "=q" (below), "+q" (a), "+r" (c) : "q" (b) : "cc");
  return below;
}

// subIncTestIncSetb() subtracts b from a, and an inc instruction in the same
// basic block preserves the carry flag of the subtraction.  Then, in a
// different basic block, a test instruction clears the carry flag, an inc
// instruction preserves it (VEX computes the preserved carry flag as the
// constant 0), and a setb instruction in a later basic block reads it.  The
// carry flag that the setb reads is not the result of the subtraction, so
// under --dyncomp-interactions=comparisons, DynComp should not make a and b
// comparable.
int subIncTestIncSetb(int a, int b, int c, int d) {
  unsigned char below;
  __asm__ volatile ("subl %3, %1\n\t"
                    "incl %2\n\t"
                    "jmp 1f\n"
                    "1:\ttestl %4, %4\n\t"
                    "incl %2\n\t"
                    "jmp 2f\n"
                    "2:\tsetb %0"
                    : "=q" (below), "+r" (a), "+r" (c) : "r" (b), "r" (d)
                    : "cc");
  return below;
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
  lessWideSameBlock(24, 25, 26, 27);
  xorThenLess(28, 29, 30);
  carry(5, 6);
  addWithCarry(7, 8, 9, 10);
  subThenInc(15, 16, 17);
  subThenLahf(18, 19);
  subThenIncSameBlock(24, 25, 26);
  subSetbInc(27, 28, 29);
  subIncJnz(30, 31, 32);
  subIncSetb(33, 34, 35);
  subThenIncSetb(36, 37, 38);
  subIncSetbSameBlock(39, 40, 41);
  subbIncSetb(42, 43, 44);
  subIncTestIncSetb(45, 46, 47, 48);
  return 0;
}
