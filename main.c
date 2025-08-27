#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
#define CIGINT_N 8
#include "cigint.h"

int main(void) {
  Cigint one = {0};
  one.data[CIGINT_N - 1] = (1ul << 31) - 1;
  print2(one);
  printf("\n");

  one = shl(one, 31);
  print2(one);
  printf("\n");

  one = shr(one, 31);
  print2(one);
  printf("\n");

  Cigint two = {0};
  two.data[CIGINT_N - 1] = 2;

  print2(add(one, two));
  printf("\n");

  print2(sub(one, two));
  printf("\n");

  print10(mul(one, one));
  printf("\n");

  print2(div(one, two));
  printf("\n");

  Cigint twelve = {0}, four = {0};
  twelve.data[CIGINT_N - 1] = 4;
  four.data[CIGINT_N - 1] = 1000;
  print2(div(twelve, four));
  printf("\n");
  print2(mod(twelve, four));
  printf("\n");
  return 0;
}
