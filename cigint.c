#include "cigint.h"

u32 u128_get_bit(u128 num, u32 pos) {
	if (pos < 64) {
		return (u32) ((num.lo & (1UL << pos)) >> pos);
	}
	if (pos < 128) {
		pos -= 64;
		return (u32) ((num.hi & (1UL << pos)) >> pos);
	}

	return 0;
}

u128 u128_set_bit(u128 num, u32 pos, u32 val) {
	if (pos < 64) {
		num.lo = (num.lo & ~(1UL << pos)) | (val << pos);
		return num;
	}
	if (pos < 128) {
		pos -= 64;
		num.hi = (num.hi & ~(1UL << pos)) | (val << pos);
		return num;
	}

	return num;
}

void u128_print2(u128 num) {
	printf("0b");
	u32 is_leading_zero = 1;
	for (u32 i = 127; i != 0; --i) {
		u32 digit = u128_get_bit(num, i);
		if (is_leading_zero) {
			if (digit == 1) {
				is_leading_zero = 0;
			}
			else {
				continue;
			}
		}
		printf("%d", digit);
	}

	printf("\n");
}

void u128_print10(u128 num) {
	u128 p17 = u128_from_u64(100000000000000000);
	uint64_t last_17_digits = u128_mod(num, p17).lo;
	u128 first_22_digits = u128_div(num, p17);
#if 0
	if (first_22_digits.hi > 0) {
		uint64_t first_5_digits = u128_div(first_22_digits, p17).lo;
		uint64_t next_17_digits = u128_mod(first_22_digits, p17).lo;
		printf("%"PRIu64"" "%017"PRIu64"" "%017"PRIu64"\n", first_5_digits, next_17_digits, last_17_digits);
		return;
	}
	printf("%022"PRIu64"" "%017"PRIu64"\n", first_22_digits.lo, last_17_digits);
#else
	u64 next_17_digits = 0;
	if (first_22_digits.hi > 0) {
		u64 first_5_digits = u128_div(first_22_digits, p17).lo;
		next_17_digits = u128_mod(first_22_digits, p17).lo;
		printf("%"PRIu64"", first_5_digits);
	}
	else {
		next_17_digits = first_22_digits.lo;
	}

	if (next_17_digits > 0) {
		printf("%"PRIu64"" "%017"PRIu64"\n", next_17_digits, last_17_digits);
	}
	else {
		printf("%"PRIu64"\n", last_17_digits);
	}
#endif
}

void i128_print10(u128 num) {
	u32 digit = u128_get_bit(num, 127);
	if (digit == 0) {
		u128_print10(num);
		return;
	}

	u128 two_pow_127 = (u128) { .hi = (1UL << 63) };
	printf("-");
	u128_print10(u128_sub(two_pow_127, u128_set_bit(num, 127, 0)));
}

u128 u128_from_u64(uint64_t num) {
	return (u128) {
		.lo = num,
	};
}

u128 u128_and(u128 a, u128 b) {
	return (u128) {
		.hi = a.hi & b.hi,
		.lo = a.lo & b.lo,
	};
}

u128 u128_or(u128 a, u128 b) {
	return (u128) {
		.hi = a.hi | b.hi,
		.lo = a.lo | b.lo,
	};
}

u128 u128_xor(u128 a, u128 b) {
	return (u128) {
		.hi = a.hi ^ b.hi,
		.lo = a.lo ^ b.lo,
	};
}

u128 u128_not(u128 a) {
	return (u128) {
		.hi = ~a.hi,
		.lo = ~a.lo,
	};
}

u128 u128_shl(u128 num, uint32_t amnt) {
	if (amnt == 0) {
		return num;
	}
	if (amnt < 64) {
		uint64_t lo_leading = ((num.lo & (((1ul << amnt) - 1) << (64 - amnt))) >> (64 - amnt));
		return (u128) {
			.hi = (num.hi << amnt) | lo_leading,
			.lo = (num.lo << amnt)
		};
	}
	else if (amnt < 128) {
		return (u128) {
			.hi = (num.lo << (amnt - 64)),
			.lo = 0
		};
	}

	return U128_ZERO;
}

u128 u128_shr(u128 num, uint32_t amnt) {
	if (amnt == 0) {
		return num;
	}

	if (amnt < 64) {
		uint64_t hi_trailing = (num.hi & ((1ul << amnt) - 1));
		return (u128) {
			.hi = (num.hi >> amnt),
			.lo = (hi_trailing << (64 - amnt)) | (num.lo >> amnt),
		};
	}
	else if (amnt < 128) {
		return (u128) {
			.hi = 0,
			.lo = (num.hi >> (amnt - 64))
		};
	}

	return U128_ZERO;
}

u32 u128_eq(u128 a, u128 b) {
	return (a.hi == b.hi) && (a.lo == b.lo);
}

u32 u128_gt(u128 a, u128 b) {
	return (a.hi > b.hi) || (a.hi == b.hi && a.lo > b.lo);
}

u32 u128_ge(u128 a, u128 b) {
	return (a.hi > b.hi) || (a.hi == b.hi && a.lo >= b.lo);
}

u32 u128_eq0(u128 num) {
	return (num.hi == 0) && (num.lo == 0);
}

u128 u128_add(u128 a, u128 b) {
	while (!u128_eq0(b)) {
		u128 carry = u128_and(a, b);
		a = u128_xor(a, b);
		b = u128_shl(carry, 1);
	}

	return a;
}

u128 u128_sub(u128 a, u128 b) {
	while (!u128_eq0(b)) {
		u128 borrow = u128_and(u128_not(a), b);
		a = u128_xor(a, b);
		b = u128_shl(borrow, 1);
	}

	return a;
}

u128 u128_div(u128 a, u128 b) {
	if (u128_ge(b, a)) {
		return (u128) { .lo = u128_eq(a, b) };
	}

	u128 quotient = { .lo = 1 }, old_b = b;
	while (u128_ge(a, b)) {
		b = u128_shl(b, 1);
		quotient = u128_shl(quotient, 1);
	}

	if (u128_gt(b, a)) {
		b = u128_shr(b, 1);
		quotient = u128_shr(quotient, 1);
	}

	quotient = u128_add(quotient, u128_div(u128_sub(a, b), old_b));
	return quotient;
}

u128 u128_mod(u128 a, u128 b) {
	assert(!u128_eq0(b) && "error: modulo by zero");

	u128 half_a = u128_shr(a, 1), x = b;
	while (u128_ge(half_a, x)) {
		x = u128_shl(x, 1);
	}

	while (u128_ge(a, b)) {
		if (u128_ge(a, x)) {
			a = u128_sub(a, x);
		}
		x = u128_shr(x, 1);
	}

	return a;
}

u128 u128_neg(u128 num) {
	return u128_add(u128_not(num), (u128) { .lo = 1 });
}

/*
void u128_tostr(u128 num, char buf[U128_MAX_DIGITS + 1UL]) {
	char pow2[] = "000000000000000000000000000000000000001";
	for (u32 i = 0; i < 64; i++) {
		if ((num.lo & (1ul << i)) >> i) {
			add(buf, pow2);
		}
		add(pow2, pow2);
	}
	for (u32 i = 0; i < 64; i++) {
		if ((num.hi & (1ul << i)) >> i) {
			add(buf, pow2);
		}
		add(pow2, pow2);
	}
}

size_t slen(char *s, size_t max_len) {
	size_t len = 0;
	while (*s++ && len <= max_len) {
		len++;
	}
	assert(len <= max_len && "error: number is too large");

	return len;
}

void add(char *num1, char *num2) {
	size_t len1 = slen(num1, U128_MAX_DIGITS);
	size_t len2 = slen(num2, U128_MAX_DIGITS);
	if (len2 > len1) {
		len2 = len1;
	}
	u32 carry = 0;
	while (len2 != 0) {
		u32 res = (num1[--len1] + num2[--len2] - 2 * '0') + carry;
		num1[len1] = (res % 10) + '0';
		carry = res / 10;
	}

	while (len1 != 0) {
		u32 res = num1[--len1] + carry - '0';
		num1[len1] = (res % 10) + '0';
		carry = res / 10;
	}
}
*/

