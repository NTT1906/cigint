#define CIGINT_IMPLEMENTATION
#define CIGINT_STRIP_PREFIX
// #define CIGINT_N (28000/32)
#define CIGINT_N 1000
#include "cigint.h"

int main(void) {
	Cigint one = {0};
	one.data[CIGINT_N - 1] = (1ul << 31) - 1;
	cprintf("%Cb\n", one);

	one = shl(one, 31);
	cprintf("%Cb\n", one);

	one = shr(one, 31);
	cprintf("%Cb\n", one);

	Cigint two = from_u32(2);
	cprintf("One: %Cd\n", one);
	cprintf("Two: %Cd\n", two);
	cprintf("+  :%Cd\n", add(one, two));
	cprintf("-  :%Cd\n", sub(one, two));
	cprintf("*  :%Cd\n", mul(one, two));
	cprintf("/  :%Cd\n", div(one, two));

	Cigint three = one;
	cigint_sqr_ref(&three);
	cprintf("1  :%Cd\n", one);
	cprintf("3  :%Cd\n", three);
	Cigint tmp = cigint_pow(one, 100);
	cprintf("   :%Cd\n", tmp);
	Cigint four = cigint_pow_v2(&one, 100);
	cprintf("** :%Cd\n", four);
	Cigint five = cigint_pow_v3(one, 100);
	cprintf("** :%Cd\n", five);
	Cigint a = cigint_from_dec("98079714341385330254404631364738284897724378381211926529");
	cprintf("a  :%Cd\n", a);
	Cigint b = cigint_from_dec("9619630365287747226839050184643602938340697085011445564157160567898819911694890106389939682378399424833933803521");
	Cigint c = cigint_mul(a, a);
	cprintf("c  :%Cd\n", c);
	printf("CMP: %d\n", cigint_cmp(b, c));
	return 0;
}
