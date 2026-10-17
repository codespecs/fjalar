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

struct longPair {
  long a;
  long b;
};

// copyLongs() copies a struct with movdqu, so VEX loads both fields with one
// 128-bit load.  Loading is not an interaction under
// --dyncomp-interactions=comparisons, so DynComp should not make a and b
// comparable.
long copyLongs(long a, long b) {
  struct longPair p, q;
  p.a = a;
  p.b = b;
  __asm__ volatile ("movdqu %1, %%xmm0\n\t"
                    "movdqu %%xmm0, %0"
                    : "=m" (q) : "m" (p) : "xmm0");
  return q.a;
}

struct intPair {
  int a;
  int b;
};

// copyInts() copies a struct with one 64-bit load.  Loading is not an
// interaction under --dyncomp-interactions=comparisons, so DynComp should
// not make a and b comparable.
int copyInts(int a, int b) {
  struct intPair p, q;
  p.a = a;
  p.b = b;
  __asm__ volatile ("movq %1, %%rax\n\t"
                    "movq %%rax, %0"
                    : "=m" (q) : "m" (p) : "rax");
  return q.a;
}

int main(void) {
  less(1, 2);
  lessMask(3, 4);
  carry(5, 6);
  addWithCarry(7, 8, 9, 10);
  subThenInc(15, 16, 17);
  subThenLahf(18, 19);
  subThenIncSameBlock(20, 21, 22);
  subSetbInc(23, 24, 25);
  copyLongs(11, 12);
  copyInts(13, 14);
  return 0;
}
