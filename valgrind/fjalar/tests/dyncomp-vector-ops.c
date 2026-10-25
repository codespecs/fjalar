// Executes AVX2, FMA, and F16C instructions, so that DynComp instruments
// the IROps that VEX translates them to.  dyncomp-vector-ops-test.sh runs
// it.  Intrinsics, rather than loops for the compiler to vectorize, choose
// the instructions, so that a compiler change does not change the IROps.

#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>

#define N 64

int32_t ints[N], int_results[N];
uint8_t ubytes[N];
int8_t sbytes[N];
int16_t shorts[N];
double doubles[N], double_results[N];
uint16_t halves[N];
float floats[N];

void integer_ops(void) {
  for (int i = 0; i < N; i += 8) {
    __m256i a = _mm256_loadu_si256((__m256i*)&ints[i]);
    __m256i b = _mm256_loadu_si256((__m256i*)&ints[N - 8 - i]);
    __m256i sum = _mm256_add_epi32(a, b);
    __m256i product = _mm256_mullo_epi32(sum, b);
    __m256i permuted = _mm256_permutevar8x32_epi32(product, _mm256_set1_epi32(i & 7));
    __m256i greater = _mm256_cmpgt_epi32(permuted, a);
    _mm256_storeu_si256((__m256i*)&int_results[i],
                        _mm256_permute4x64_epi64(greater, 0x1b));
  }
}

void byte_ops(void) {
  for (int i = 0; i < N; i += 32) {
    __m256i u = _mm256_loadu_si256((__m256i*)&ubytes[i]);
    __m256i s = _mm256_loadu_si256((__m256i*)&sbytes[i]);
    __m256i products = _mm256_maddubs_epi16(u, s);
    __m256i shuffled = _mm256_shuffle_epi8(u, s);
    __m256i blended = _mm256_blendv_epi8(products, shuffled, s);
    _mm256_storeu_si256((__m256i*)&shorts[i / 2], blended);
  }
}

void floating_point_ops(void) {
  for (int i = 0; i < N; i += 4) {
    __m256d a = _mm256_loadu_pd(&doubles[i]);
    __m256d b = _mm256_loadu_pd(&doubles[N - 4 - i]);
    // a * a + 1.5 is positive, so the square root is not a NaN.
    __m256d fused = _mm256_fmadd_pd(a, a, _mm256_set1_pd(1.5));
    _mm256_storeu_pd(&double_results[i], _mm256_sqrt_pd(_mm256_max_pd(fused, b)));
  }
  for (int i = 0; i < N; i += 8) {
    __m256 f = _mm256_cvtph_ps(_mm_loadu_si128((__m128i*)&halves[i]));
    _mm256_storeu_ps(&floats[i], _mm256_div_ps(f, _mm256_set1_ps(3.0f)));
  }
}

int main(void) {
  for (int i = 0; i < N; i++) {
    ints[i] = i * 2654435761u;
    ubytes[i] = i * 13;
    sbytes[i] = i * 11 - 100;
    doubles[i] = i * 0.75 - 20;
    halves[i] = 0x3c00 + i;  // 1.0 and slightly larger, as IEEE half floats
  }
  integer_ops();
  byte_ops();
  floating_point_ops();
  long checksum = 0;
  for (int i = 0; i < N; i++) {
    checksum += int_results[i] + shorts[i / 2] + (long)double_results[i]
                + (long)floats[i];
  }
  printf("%ld\n", checksum);
  return 0;
}
