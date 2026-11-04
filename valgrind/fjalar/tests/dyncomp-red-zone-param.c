// Test input for dyncomp-red-zone-param-test.sh.

// leaf is a leaf function without a stack protector, so it keeps its
// formal parameters and locals in the red zone below the stack pointer.
// Its local needs 32-byte alignment, so GCC realigns the stack pointer and
// gives the formal parameters locations relative to the stack pointer, not
// to the frame base.

typedef int v8si __attribute__((vector_size(32)));

// a and b should not be comparable; the return value should be comparable
// to a.
__attribute__((no_stack_protector))
int leaf(int a, int b) {
  v8si v = {0};
  v[0] = a;
  return v[0];
}

int main(void) {
  leaf(1, 2);
  return 0;
}
