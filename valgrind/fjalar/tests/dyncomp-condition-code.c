// Test input for dyncomp-condition-code-test.sh.

// less() compares its parameters with a cmp instruction whose condition
// code is read by a setl instruction in a different basic block.  VEX
// translates the setl into a call to amd64g_calculate_condition whose
// first argument is the constant condition code and whose other arguments
// include the operands of the comparison.  DynComp should make a and b
// comparable.
int less(int a, int b) {
  unsigned char result;
  __asm__ volatile ("cmpl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsetl %0"
                    : "=q" (result) : "r" (a), "r" (b) : "cc");
  return result;
}

// notCompared() does not compare its parameters, so DynComp should not
// make c and d comparable.
int notCompared(int c, int d) {
  return c;
}

int main(void) {
  less(1, 2);
  notCompared(3, 4);
  return 0;
}
