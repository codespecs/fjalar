// Test input for dyncomp-masked-move-test.sh and the other
// dyncomp-masked-move-*-test.sh scripts.

// vmaskmovps and vmaskmovpd load or store only the lanes whose mask element
// has its high bit set, and VEX translates each lane to a guarded load
// (Ist_LoadG) or a guarded store (Ist_StoreG).  xsave and xrstor save and
// restore each XMM register with a 128-bit guarded store or guarded load,
// whose guard depends on the mask in edx:eax.  A lane that is loaded or
// stored should carry the tag of the value that is moved.  A lane that is not
// loaded gets the zero that VEX supplies, which has no tag, and a lane that
// is not stored leaves the tag of the memory unchanged.  Each value is moved
// into or out of a vector register with vmovd or vmovq, which moves one lane,
// because a 128-bit load would make the values in its lanes comparable.  The
// comments on the functions give the comparability under the default
// --dyncomp-interactions=all.

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

// Like masked_load, but with 64-bit lanes.  a and b should not be
// comparable; the return value should be comparable to a.
long masked_load_64(long a, long b) {
  long src[2] = {0, 0};
  long mask[2] = {-1, 0};
  long result;
  src[0] = a;
  src[1] = b;
  __asm__ volatile ("vmovdqu %2, %%xmm1\n\t"
                    "vmaskmovpd %1, %%xmm1, %%xmm0\n\t"
                    "vmovq %%xmm0, %0"
                    : "=r" (result) : "m" (src), "m" (mask)
                    : "xmm0", "xmm1");
  return result;
}

// Like masked_store, but with a 256-bit vector, whose 8 lanes are stored
// with 8 guarded stores.  Lanes 0 and 7 are stored.  a and b should not be
// comparable; the return value should be comparable to a.
int masked_store_ymm(int a, int b) {
  int dst[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  int mask[8] = {-1, 0, 0, 0, 0, 0, 0, -1};
  dst[0] = b;
  __asm__ volatile ("vmovdqu %2, %%ymm1\n\t"
                    "vmovd %1, %%xmm0\n\t"
                    "vmaskmovps %%ymm0, %%ymm1, %0\n\t"
                    "vzeroupper"
                    : "+m" (dst) : "r" (a), "m" (mask)
                    : "xmm0", "xmm1");
  return dst[0];
}

// Saves xmm0, which holds a, with xsave, overwrites xmm0 with b, and then
// restores xmm0 with xrstor.  The mask in hi:lo selects the state components
// to save and restore; it is not a constant, so the guard of each guarded
// store and guarded load is not a constant.  a and b should not be
// comparable; the return value should be comparable to a.
int xsave_xrstor(int a, int b, unsigned lo, unsigned hi) {
  // The xsave area must be 64-byte aligned, and its header must be zero
  // before xsave.  The SSE state ends at byte 576.
  char xsave_area[1024] __attribute__((aligned(64))) = {0};
  int result;
  __asm__ volatile ("vmovd %2, %%xmm0\n\t"
                    "xsave %0\n\t"
                    "vmovd %3, %%xmm0\n\t"
                    "xrstor %0\n\t"
                    "vmovd %%xmm0, %1"
                    : "+m" (xsave_area), "=r" (result)
                    : "r" (a), "r" (b), "a" (lo), "d" (hi)
                    : "xmm0");
  return result;
}

int main(void) {
  masked_load(1, 2);
  masked_load_skipped(3, 4);
  masked_store(5, 6);
  masked_store_skipped(7, 8);
  masked_load_64(9, 10);
  masked_store_ymm(11, 12);
  // Bit 1 of the mask selects the SSE state, which includes xmm0.
  xsave_xrstor(13, 14, 2, 0);
  return 0;
}
