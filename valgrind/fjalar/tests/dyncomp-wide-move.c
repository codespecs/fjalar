// Test input for dyncomp-wide-move-test.sh and the other
// dyncomp-wide-move-*-test.sh scripts.

// A 128-bit or 256-bit store should write the tag of the stored value to
// every byte that it writes, so a later load of any of those bytes gets that
// tag.  The stored vector is in a register, not loaded in the same
// superblock, so DynComp stores the tag of the vector rather than the tags of
// the bytes that a load read.
//
// A 128-bit or 256-bit load is not an interaction under any value of
// --dyncomp-interactions, so it merges nothing.  A store of a vector that was
// loaded in the same superblock writes the tag of each byte that the load
// read.

// Stores a 256-bit vector whose tag is the tag of a to dst, after storing b
// to element I of dst.  a and b should not be comparable; the return value
// should be comparable to a, because the vector overwrites dst[I].
#define STORE_256(I)                                    \
  int store_256_##I(int a, int b) {                     \
    int dst[8] = {0, 0, 0, 0, 0, 0, 0, 0};              \
    dst[I] = b;                                         \
    __asm__ volatile ("vmovd %1, %%xmm0\n\t"            \
                      "vmovdqu %%ymm0, %0"              \
                      : "+m" (dst) : "r" (a) : "xmm0"); \
    return dst[I];                                      \
  }

// Like STORE_256, but stores a 128-bit vector, which overwrites dst[0]
// through dst[3] only.
#define STORE_128(I)                                    \
  int store_128_##I(int a, int b) {                     \
    int dst[8] = {0, 0, 0, 0, 0, 0, 0, 0};              \
    dst[I] = b;                                         \
    __asm__ volatile ("vmovd %1, %%xmm0\n\t"            \
                      "vmovdqu %%xmm0, %0"              \
                      : "+m" (dst) : "r" (a) : "xmm0"); \
    return dst[I];                                      \
  }

STORE_256(0)
STORE_256(1)
STORE_256(2)
STORE_256(3)
STORE_256(4)
STORE_256(5)
STORE_256(6)
STORE_256(7)

STORE_128(3)
// The return value should be comparable to b, not to a.
STORE_128(4)

// Loads 32 bytes, which hold a, b, c, and d, one in each 8-byte chunk.  No
// two of a, b, c, and d should be comparable.
void load_256(int a, int b, int c, int d) {
  int src[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  src[1] = a;
  src[3] = b;
  src[5] = c;
  src[7] = d;
  __asm__ volatile ("vmovdqu %0, %%ymm0" : : "m" (src) : "xmm0");
}

// Loads 16 bytes, which hold a and b but not c.  No two of a, b, and c
// should be comparable.
void load_128(int a, int b, int c) {
  int src[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  src[0] = a;
  src[3] = b;
  src[4] = c;
  __asm__ volatile ("vmovdqu %0, %%xmm0" : : "m" (src) : "xmm0");
}

// Copies a 32-byte array that holds a, b, c, and d, one in each 8-byte chunk,
// with one 256-bit load and one 256-bit store in the same superblock, and
// returns element I of the copy.  No two of a, b, c, and d should be
// comparable; the return value should be comparable to element I.
#define COPY_256(I)                                             \
  long copy_256_##I(long a, long b, long c, long d) {           \
    long src[4], dst[4];                                        \
    src[0] = a;                                                 \
    src[1] = b;                                                 \
    src[2] = c;                                                 \
    src[3] = d;                                                 \
    __asm__ volatile ("vmovdqu %1, %%ymm0\n\t"                  \
                      "vmovdqu %%ymm0, %0"                      \
                      : "=m" (dst) : "m" (src) : "xmm0");       \
    return dst[I];                                              \
  }

COPY_256(0)
COPY_256(1)
COPY_256(2)
COPY_256(3)

int main(void) {
  store_256_0(1, 2);
  store_256_1(1, 2);
  store_256_2(1, 2);
  store_256_3(1, 2);
  store_256_4(1, 2);
  store_256_5(1, 2);
  store_256_6(1, 2);
  store_256_7(1, 2);
  store_128_3(1, 2);
  store_128_4(1, 2);
  load_256(1, 2, 3, 4);
  load_128(1, 2, 3);
  copy_256_0(1, 2, 3, 4);
  copy_256_1(1, 2, 3, 4);
  copy_256_2(1, 2, 3, 4);
  copy_256_3(1, 2, 3, 4);
  return 0;
}
