#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
#define CIGINT_N 8
#include "cigint.h"

int main(void) {
  Cigint a = 10000 * 10000;
  a = a * 123 * 123 * 999 * 123;
  a *= a;
  // print10(a + 1);
  cprintf("%Cd %d %s\n", a, 100, "Hello WOrld");
  return 0;
}
