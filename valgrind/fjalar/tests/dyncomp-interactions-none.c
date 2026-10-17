// Test input for dyncomp-interactions-none-test.sh.

// less() compares its parameters with a cmp instruction whose condition
// code is read by a setl instruction in a different basic block.  VEX
// translates the setl into a call to amd64g_calculate_condition, whose
// arguments include the operands of the comparison.  Under
// --dyncomp-interactions=none, DynComp should not make a and b comparable.
int less(int a, int b) {
  unsigned char result;
  __asm__ volatile ("cmpl %2, %1\n\t"
                    "jmp 1f\n"
                    "1:\tsetl %0"
                    : "=q" (result) : "r" (a), "r" (b) : "cc");
  return result;
}

struct longPair {
  long a;
  long b;
};

// copyLongs() copies a struct with movdqu, so VEX loads both fields with one
// 128-bit load.  Loading is not an interaction under
// --dyncomp-interactions=none, so DynComp should not make a and b comparable.
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
// interaction under --dyncomp-interactions=none, so DynComp should not make
// a and b comparable.
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
  copyLongs(1, 2);
  copyInts(3, 4);
  return 0;
}
