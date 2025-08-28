#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
#define CIGINT_N (28000/32)
#include "cigint.h"

int main(void) {
  Cigint one = {0};
  one.data[CIGINT_N - 1] = (1ul << 31) - 1;
  cprintf("%Cb\n", one);

  one = shl(one, 31);
  cprintf("%Cb\n", one);

  one = shr(one, 31);
  cprintf("%Cb\n", one);

  Cigint two = {0};
  two.data[CIGINT_N - 1] = 2;

  cprintf("%Cd\n", add(one, two));
  cprintf("%Cd\n", sub(one, two));
  cprintf("%Cd\n", mul(one, two));
  cprintf("%Cd\n", div(one, two));

  one = pow(one, 100);
  cprintf("%Cd\n", one);

  return 0;
}
