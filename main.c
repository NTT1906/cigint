#include "cigint.h"

int main(void) {
/*
	u128 n = U128_ZERO;
	assert(u128_eq0(n));
	n = u128_add(n, u128_from_u64(1));
	assert(!u128_eq0(n));

	u128 t = u128_shl(u128_from_u64(1), 127);
	u128_print10(t);
	i128_print10(t);
	u128_print2(t);

	u128 neg1 = u128_neg(u128_from_u64(1));
	i128_print10(neg1);
	neg1 = u128_add(neg1, u128_from_u64(2));
	i128_print10(neg1);
*/
	u128 a = U128_ZERO;
	u128 b = u128_add(a, u128_from_u64(1));
	for (u32 i = 0; i <= 180; i++) {
		u128_print10(a);
		u128 c = u128_add(a, b);
		a = b;
		b = c;
	}
	return 0;
}
