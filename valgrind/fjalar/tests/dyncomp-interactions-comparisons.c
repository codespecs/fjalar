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

int main(void) {
  less(1, 2);
  addWithCarry(3, 4, 5, 6);
  return 0;
}
