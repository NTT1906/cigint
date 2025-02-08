#include "cigint.h"

int main(void) {
	uint128_t t = from_u64((1ul << 63) - 1 + (1ul << 63));
	assert(1 == u128_eq(t, u128_shr(u128_shl(t, 4), 4)));
	assert(1 == u128_eq(u128_add(from_u64(12), from_u64(100)), from_u64(112)));
	assert(1 == u128_eq(u128_add(from_u64(1ul << 62), from_u64(1ul << 62)), from_u64(1ul << 63)));
	assert(0 == u128_eq(u128_sub(from_u64(1ul << 63), from_u64(1ul << 62)), from_u64((1ul << 62) + 1)));
	// print2((from_u64(1)));
	print2(u128_neg(from_u64(1)));
	// print10(u128_neg(from_u64(1)));

	uint128_t base = u128_shl(from_u64(1), 127);
	char buf[] = "000000000000000000000000000000000000000";
	sprint10(base, buf);
	printf("%s\n", buf);
	assert(1 == u128_eq(from_u64(1 << 20), u128_mod(from_u64(1 << 20), from_u64(1 << 21))));
	assert(0 == u128_eq(from_u64(2 << 20), u128_mod(from_u64(1 << 20), from_u64(1 << 21))));
	print10(base);
	print2(base);
	return 0;
}
