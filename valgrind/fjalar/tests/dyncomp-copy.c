// Test input for dyncomp-copy-none-test.sh and
// dyncomp-copy-comparisons-test.sh.

// Under --dyncomp-interactions=none and comparisons, a load is not an
// interaction, so copying a struct with wide loads and wide stores should
// not make its fields comparable, and each copied field should keep the
// comparability of its source field.

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

// Like copy(), but the return value should be comparable to b.
long copy_second(long a, long b) {
  struct pair p, q;
  p.a = a;
  p.b = b;
  COPY_PAIR(q, p);
  return q.b;
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

// Like copy_ints(), but the return value should be comparable to y.
int copy_ints_second(int x, int y) {
  struct int_pair p, q;
  p.x = x;
  p.y = y;
  COPY_INT_PAIR(q, p);
  return q.y;
}

struct quad {
  long a;
  long b;
  long c;
  long d;
};

// Copies src to dst with two 128-bit loads followed by two 128-bit stores,
// so the second load precedes the first store.
#define COPY_QUAD(dst, src)                        \
  __asm__ volatile ("movdqu %1, %%xmm0\n\t"        \
                    "movdqu 16+%1, %%xmm1\n\t"     \
                    "movdqu %%xmm0, %0\n\t"        \
                    "movdqu %%xmm1, 16+%0"         \
                    : "=m" (dst) : "m" (src) : "xmm0", "xmm1")

// No two of a, b, c, and d should be comparable; the return value should be
// comparable to d.
long copy_quad_last(long a, long b, long c, long d) {
  struct quad p, q;
  p.a = a;
  p.b = b;
  p.c = c;
  p.d = d;
  COPY_QUAD(q, p);
  return q.d;
}

struct int_quad {
  int w;
  int x;
  int y;
  int z;
};

// Copies with a struct assignment.  At -O0, GCC compiles it to two 64-bit
// loads followed by two 64-bit stores, so the second load precedes the first
// store.  No two of w, x, y, and z should be comparable; the return value
// should be comparable to z.
int copy_int_quad_last(int w, int x, int y, int z) {
  struct int_quad p, q;
  p.w = w;
  p.x = x;
  p.y = y;
  p.z = z;
  q = p;
  return q.z;
}

int main(void) {
  copy(1, 2);
  copy_second(1, 2);
  copy_ints(1, 2);
  copy_ints_second(1, 2);
  copy_quad_last(1, 2, 3, 4);
  copy_int_quad_last(1, 2, 3, 4);
  return 0;
}
