// Test input for dyncomp-masked-move-test.sh.

// vmaskmovps loads or stores only the lanes whose mask element has its high
// bit set, and VEX translates each lane to a guarded load (Ist_LoadG) or a
// guarded store (Ist_StoreG).  A lane that is loaded or stored should carry
// its tag, and a lane that is not should carry none.  Each value is moved
// into or out of a vector register with vmovd, which moves one lane, because
// a 128-bit load would make the values in its lanes comparable.

// Loads src with the mask, and returns lane 0 of the result.
#define MASKED_LOAD(result, src, mask)                          \
  __asm__ volatile ("vmovdqu %2, %%xmm1\n\t"                    \
                    "vmaskmovps %1, %%xmm1, %%xmm0\n\t"         \
                    "vmovd %%xmm0, %0"                          \
                    : "=r" (result) : "m" (src), "m" (mask)     \
                    : "xmm0", "xmm1")

// Stores a vector whose lane 0 is value to dst with the mask.
#define MASKED_STORE(dst, value, mask)                          \
  __asm__ volatile ("vmovdqu %2, %%xmm1\n\t"                    \
                    "vmovd %1, %%xmm0\n\t"                      \
                    "vmaskmovps %%xmm0, %%xmm1, %0"             \
                    : "+m" (dst) : "r" (value), "m" (mask)      \
                    : "xmm0", "xmm1")

// a and b should not be comparable; the return value should be comparable
// to a.
int masked_load(int a, int b) {
  int src[4] = {0, 0, 0, 0};
  int mask[4] = {-1, 0, 0, 0};
  int result;
  src[0] = a;
  src[1] = b;
  MASKED_LOAD(result, src, mask);
  return result;
}

// Lane 0 is not loaded, so the result has no tag, and the return value
// should be comparable to b only.
int masked_load_skipped(int a, int b) {
  int src[4] = {0, 0, 0, 0};
  int mask[4] = {0, 0, 0, 0};
  int result;
  src[0] = a;
  MASKED_LOAD(result, src, mask);
  return result + b;
}

// a and b should not be comparable; the return value should be comparable
// to a.
int masked_store(int a, int b) {
  int dst[4] = {0, 0, 0, 0};
  int mask[4] = {-1, 0, 0, 0};
  dst[0] = b;
  MASKED_STORE(dst, a, mask);
  return dst[0];
}

// Lane 0 is not stored, so dst[0] keeps b, and the return value should be
// comparable to b.
int masked_store_skipped(int a, int b) {
  int dst[4] = {0, 0, 0, 0};
  int mask[4] = {0, 0, 0, 0};
  dst[0] = b;
  MASKED_STORE(dst, a, mask);
  return dst[0];
}

int main(void) {
  masked_load(1, 2);
  masked_load_skipped(3, 4);
  masked_store(5, 6);
  masked_store_skipped(7, 8);
  return 0;
}
