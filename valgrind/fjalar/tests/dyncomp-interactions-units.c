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

int main(void) {
  less(1, 2);
  overflow(3, 4);
  return 0;
}
