#include "cigint.h"

void print2(uint128_t num) {
	printf("0b");
	int is_leading_zero = 1;
	for (int i = 63; i >= 0; --i) {
		uint8_t digit = (uint8_t) ((num.hi & (1UL << i)) >> i);
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

	for (int i = 63; i >= 0; --i) {
		uint8_t digit = (uint8_t) ((num.lo & (1UL << i)) >> i);
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

void print10(uint128_t num) {
	uint128_t p17 = from_u64(100000000000000000);
	uint64_t last_17_digits = u128_mod(num, p17).lo;
	uint128_t first_22_digits = u128_div(num, p17);
	if (first_22_digits.hi > 0) {
		uint64_t first_5_digits = u128_div(first_22_digits, p17).lo;
		uint64_t next_17_digits = u128_mod(first_22_digits, p17).lo;
		printf("%05"PRIu64"" "%017"PRIu64"" "%017"PRIu64"\n", first_5_digits, next_17_digits, last_17_digits);
		return;
	}
	printf("%022"PRIu64"" "%017"PRIu64"\n", first_22_digits.lo, last_17_digits);
}

uint128_t from_u64(uint64_t num) {
	return (uint128_t) {
		.lo = num,
	};
}

/* floor(log10(2**128 - 1)) + 1 = 39 */
#define uint128_len 39
void sprint10(uint128_t num, char buf[uint128_len + 1]) {
	char pow2[] = "000000000000000000000000000000000000001";
	for (int i = 0; i < 64; i++) {
		if ((num.lo & (1ul << i)) >> i) {
			add(buf, pow2);
		}
		add(pow2, pow2);
	}
	for (int i = 0; i < 64; i++) {
		if ((num.hi & (1ul << i)) >> i) {
			add(buf, pow2);
		}
		add(pow2, pow2);
	}
}

uint128_t u128_and(uint128_t a, uint128_t b) {
	return (uint128_t) {
		.hi = a.hi & b.hi,
		.lo = a.lo & b.lo,
	};
}

uint128_t u128_or(uint128_t a, uint128_t b) {
	return (uint128_t) {
		.hi = a.hi | b.hi,
		.lo = a.lo | b.lo,
	};
}

uint128_t u128_xor(uint128_t a, uint128_t b) {
	return (uint128_t) {
		.hi = a.hi ^ b.hi,
		.lo = a.lo ^ b.lo,
	};
}

uint128_t u128_not(uint128_t a) {
	return (uint128_t) {
		.hi = ~a.hi,
		.lo = ~a.lo,
	};
}

uint128_t u128_shl(uint128_t num, uint8_t amnt) {
	if (amnt == 0) {
		return num;
	}
	if (amnt < 64) {
		uint64_t lo_leading = ((num.lo & (((1ul << amnt) - 1) << (64 - amnt))) >> (64 - amnt));
		return (uint128_t) {
			.hi = (num.hi << amnt) | lo_leading,
			.lo = (num.lo << amnt)
		};
	}
	else if (amnt < 128) {
		return (uint128_t) {
			.hi = (num.lo << (amnt - 64)),
			.lo = 0
		};
	}

	return u128_zero;
}

uint128_t u128_shr(uint128_t num, uint8_t amnt) {
	if (amnt == 0) {
		return num;
	}

	if (amnt < 64) {
		uint64_t hi_trailing = (num.hi & ((1ul << amnt) - 1));
		return (uint128_t) {
			.hi = (num.hi >> amnt),
			.lo = (hi_trailing << (64 - amnt)) | (num.lo >> amnt),
		};
	}
	else if (amnt < 128) {
		return (uint128_t) {
			.hi = 0,
			.lo = (num.hi >> (amnt - 64))
		};
	}

	return u128_zero;
}

int u128_eq(uint128_t a, uint128_t b) {
	return (a.hi == b.hi) && (a.lo == b.lo);
}

int u128_gt(uint128_t a, uint128_t b) {
	return (a.hi > b.hi) || (a.hi == b.hi && a.lo > b.lo);
}

int u128_ge(uint128_t a, uint128_t b) {
	return (a.hi > b.hi) || (a.hi == b.hi && a.lo >= b.lo);
}

int is_zero(uint128_t num) {
	return (num.hi == 0) && (num.lo == 0);
}

uint128_t u128_add(uint128_t a, uint128_t b) {
	while (!is_zero(b)) {
		uint128_t carry = u128_and(a, b);
		a = u128_xor(a, b);
		b = u128_shl(carry, 1);
	}

	return a;
}

uint128_t u128_sub(uint128_t a, uint128_t b) {
	while (!is_zero(b)) {
		uint128_t borrow = u128_and(u128_not(a), b);
		a = u128_xor(a, b);
		b = u128_shl(borrow, 1);
	}

	return a;
}

uint128_t u128_div(uint128_t a, uint128_t b) {
	if (u128_ge(b, a)) {
		return (uint128_t) { .lo = u128_eq(a, b) };
	}

	uint128_t quotient = { .lo = 1 }, old_b = b;
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

uint128_t u128_mod(uint128_t a, uint128_t b) {
	assert(!is_zero(b) && "error: modulo by zero");

	uint128_t half_a = u128_shr(a, 1), x = b;
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

uint128_t u128_neg(uint128_t num) {
	return u128_add(u128_not(num), (uint128_t) { .lo = 1 });
}

size_t slen(char *s) {
	size_t len = 0;
	while (*s++) {
		len++;
	}

	return len;
}

void add(char *num1, char *num2) {
	size_t len1 = slen(num1);
	size_t len2 = slen(num2);
	if (len2 > len1) {
		len2 = len1;
	}
	int carry = 0;
	while (len2 != 0) {
		int res = (num1[--len1] + num2[--len2] - 2 * '0') + carry;
		num1[len1] = (res % 10) + '0';
		carry = res / 10;
	}

	while (len1 != 0) {
		int res = num1[--len1] + carry - '0';
		num1[len1] = (res % 10) + '0';
		carry = res / 10;
	}
}

