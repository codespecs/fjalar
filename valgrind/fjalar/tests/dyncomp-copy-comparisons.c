// Test input for dyncomp-copy-comparisons-test.sh.

// Under --dyncomp-interactions=comparisons, a load is not an interaction,
// so copying a struct with one wide load and one wide store should not make
// its fields comparable.

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

// a and b should not be comparable; the return value should be comparable
// to a.
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

// x and y should not be comparable; the return value should be comparable
// to x.
int copy_ints(int x, int y) {
  struct int_pair p, q;
  p.x = x;
  p.y = y;
  COPY_INT_PAIR(q, p);
  return q.x;
}

int main(void) {
  copy(1, 2);
  copy_ints(1, 2);
  return 0;
}
