// Test input for dyncomp-wide-store-test.sh.

// A 256-bit store should write the tag of the stored value to all 32 bytes
// that it writes, so a later load of any of those bytes gets that tag.  The
// stored vector is in a register, not loaded in the same superblock, so
// DynComp stores the tag of the vector rather than the tags of the bytes that
// a load read.

// a and b should not be comparable; the return value should be comparable
// to a, because the store overwrites dst[6], which held b.
int wide_store(int a, int b) {
  int dst[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  dst[6] = b;
  __asm__ volatile ("vmovd %1, %%xmm0\n\t"
                    "vmovdqu %%ymm0, %0"
                    : "=m" (dst) : "r" (a) : "xmm0");
  return dst[6];
}

int main(void) {
  wide_store(1, 2);
  return 0;
}
