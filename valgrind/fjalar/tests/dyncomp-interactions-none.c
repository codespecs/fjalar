// Test input for dyncomp-interactions-none-test.sh.

// less() compares its parameters with a cmp instruction whose condition
// code is read by a setl instruction in a different basic block.  VEX
// translates the setl into a call to amd64g_calculate_condition whose
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

struct pair {
  long a;
  long b;
};

// Copies src to dst with movdqu, so VEX loads both fields with one 128-bit
// load and stores them with one 128-bit store.
#define COPY_PAIR(dst, src)                        \
  __asm__ volatile ("movdqu %1, %%xmm0\n\t"        \
                    "movdqu %%xmm0, %0"            \
                    : "=m" (dst) : "m" (src) : "xmm0")

// Under --dyncomp-interactions=none, DynComp should not make a and b
// comparable, but the return value should be comparable to a, from which it
// flows.
long copy(long a, long b) {
  struct pair p, q;
  p.a = a;
  p.b = b;
  COPY_PAIR(q, p);
  return q.a;
}

struct int_pair {
  int x;
  int y;
};

// Copies src to dst with movq, so VEX loads both fields with one 64-bit load
// and stores them with one 64-bit store.
#define COPY_INT_PAIR(dst, src)                    \
  __asm__ volatile ("movq %1, %%rax\n\t"           \
                    "movq %%rax, %0"               \
                    : "=m" (dst) : "m" (src) : "rax")

// Under --dyncomp-interactions=none, DynComp should not make x and y
// comparable, but the return value should be comparable to x, from which it
// flows.
int copy_ints(int x, int y) {
  struct int_pair p, q;
  p.x = x;
  p.y = y;
  COPY_INT_PAIR(q, p);
  return q.x;
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
  copy(1, 2);
  copy_ints(1, 2);
  return 0;
}
