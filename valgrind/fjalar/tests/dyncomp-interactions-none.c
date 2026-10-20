// Test input for dyncomp-interactions-none-test.sh,
// dyncomp-interactions-default-test.sh, and dyncomp-condition-code-test.sh.

// less() compares its parameters with a cmp instruction whose condition
// code is read by a setl instruction in a different basic block.  VEX
// translates the setl into a call to amd64g_calculate_condition (or
// x86g_calculate_condition) whose first argument is the constant condition
// code and whose other arguments include the operands of the comparison.  Under
// --dyncomp-interactions=none, DynComp should not make a and b comparable;
// otherwise, it should.
int less(int a, int b) {
  unsigned char result;
  __asm__ volatile ("cmpl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsetl %0"
                    : "=q" (result) : "r" (a), "r" (b) : "cc");
  return result;
}

// add_const() adds a constant to its parameter.  Under
// --dyncomp-interactions=none, an addition is not an interaction even when one
// operand is a constant, so the return value should not be comparable to x.
int add_const(int x) {
  int y = x + 1;
  return y;
}

int main(void) {
  add_const(1);
  less(1, 2);
  return 0;
}
