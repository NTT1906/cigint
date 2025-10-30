#ifndef CIGINT_H
#define CIGINT_H

#ifdef __cplusplus
#include <cassert>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <cstdint>
#else
#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <stdint.h>
#endif

#ifndef CIGINT_N
#define CIGINT_N 8
#endif

#ifdef __cplusplus
#define sassert static_assert
#else
#define sassert _Static_assert
#endif
sassert(CIGINT_N > 1, "CIGINT_N > 1");

typedef uint32_t u32;
typedef uint64_t u64;
#define SIZEOF_U32 (8 * sizeof(u32))
#define SIZEOF_U64 (8 * sizeof(u64))

typedef struct Cigint {
	u32 data[CIGINT_N];

#ifdef __cplusplus
	Cigint() : data{} {
		memset(this->data, 0, sizeof(this->data));
	}
	Cigint(const Cigint &rhs) : data{} {
		memcpy(this->data, rhs.data, sizeof(rhs.data));
	}
	Cigint &operator=(const Cigint &rhs) {
		if (this != &rhs) {
			memcpy(this->data, rhs.data, sizeof(rhs.data));
		}
		return *this;
	}
	Cigint(u32 rhs) : data{} {
		memset(this->data, 0, sizeof(this->data));
		this->data[CIGINT_N - 1] = rhs;
	}
#endif
} Cigint;

#ifdef __cplusplus
#define CIGINT_ZERO() Cigint{}
#else
#define CIGINT_ZERO() (Cigint){0}
#endif

#ifdef __cplusplus
#define FREF(type) type&
#define CFREF(type) const FREF(type)
#else
#define FREF(type) type
#define CFREF(type) FREF(type)
#endif

static inline u32 cigint_get_bit_ref(const Cigint *a, u32 pos);
u32 cigint_get_bit(CFREF(Cigint) a, u32 pos);
static inline Cigint *cigint_set_bit_ref(Cigint *a, u32 pos, u32 val);
Cigint cigint_set_bit(Cigint a, u32 pos, u32 val);
u32 cigint_print10(CFREF(Cigint) a);
u32 cigint_print2(CFREF(Cigint) a);
u32 cigint_print16(CFREF(Cigint) a);
u32 cigint_print16_upper(CFREF(Cigint) a);
int cigint_is0(CFREF(Cigint) a);
int cigint_cmp(CFREF(Cigint) lhs, CFREF(Cigint) rhs);
u32 cigint_highest_order(CFREF(Cigint) num);

inline void cigint_and_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_and(Cigint lhs, CFREF(Cigint) rhs);
void cigint_not_ref(Cigint *a);
Cigint cigint_not(Cigint a);
void cigint_xor_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_xor(Cigint lhs, CFREF(Cigint) rhs);
void cigint_or_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_or(Cigint lhs, CFREF(Cigint) rhs);

Cigint cigint_shl(CFREF(Cigint) lhs, u32 amnt);
Cigint cigint_shr(CFREF(Cigint) lhs, u32 amnt);
Cigint cigint_pow2(u32 amnt);

static inline void cigint_add_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_add(Cigint lhs, CFREF(Cigint) rhs);
static inline void cigint_sub_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_sub(Cigint lhs, CFREF(Cigint) rhs);
static inline void cigint_mul_ref(Cigint *lhs, const Cigint *rhs);
Cigint cigint_mul(Cigint lhs, CFREF(Cigint) rhs);
static inline void cigint_sqr_ref(Cigint *base);
static inline void cigint_pow_ref(Cigint *base, u32 exp);
Cigint cigint_pow(Cigint base, u32 exp);
static inline void cigint_divmod_ref(const Cigint *lhs, const Cigint *rhs, Cigint *q, Cigint *r);
void cigint_divmod(CFREF(Cigint) lhs, CFREF(Cigint) rhs, Cigint *q, Cigint *r);
Cigint cigint_div(CFREF(Cigint) lhs, CFREF(Cigint) rhs);
Cigint cigint_mod(CFREF(Cigint) lhs, CFREF(Cigint) rhs);
inline Cigint cigint_sqr(Cigint base);
u32 cigint_printf(const char *fmt, ...);

#ifdef CIGINT_STRIP_PREFIX
	#define get_bit_ref cigint_get_bit_ref
	#define get_bit cigint_get_bit
	#define set_bit cigint_set_bit

	/* not to be confused with C++ macros */
	#define cand cigint_and
	#define cor cigint_or
	#define cxor cigint_xor
	#define cnot cigint_not

	#define shl cigint_shl
	#define shr cigint_shr
	#define highest_order cigint_highest_order
	#define pow2 cigint_pow2
	#define cmp cigint_cmp
	#define is0 cigint_is0

	#define add cigint_add
	#define addr cigint_add_ref
	#define sub cigint_sub
	#define subr cigint_sub_ref
	#define mul cigint_mul
	#define mulr cigint_mul_ref

	#define divmod cigint_divmod
	#define divmodr cigint_divmod_ref
	#define div cigint_div
	#define mod cigint_mod

	#define pow cigint_pow
	#define powr cigint_pow_ref
	#define sqr cigint_sqr

	#define print2 cigint_print2
	#define print10 cigint_print10
	#define print16 cigint_print16
	#define print16U cigint_print16_upper
	#define cprintf cigint_printf
#endif

#ifdef CIGINT_IMPLEMENTATION
static u32 u1_get_bit(u32 num, u32 pos) { return (num >> pos) & (u32)1; }

static u32 u1_set_bit(u32 num, u32 pos, u32 val) {
	if (pos >= SIZEOF_U32) return num;
	u32 mask = (u32)1 << pos;
	return (num & ~mask) | ((val & 1u) ? mask : 0u);
}

// reverse bits by divide-and-conquer
static u32 u1_bit_reverse(u32 num) {
    num = ((num & 0x55555555U) << 1) | ((num >> 1) & 0x55555555U);
    num = ((num & 0x33333333U) << 2) | ((num >> 2) & 0x33333333U);
    num = ((num & 0x0F0F0F0FU) << 4) | ((num >> 4) & 0x0F0F0F0FU);
    num = ((num & 0x00FF00FFU) << 8) | ((num >> 8) & 0x00FF00FFU);
    return (num << 16) | (num >> 16);
}

static u32 u1_highest_order(u32 num) {
	u32 pos = 0;
	while (num > 0) {
		++pos;
		num >>= 1;
	}
	return pos;
}

static u32 u1_get_last_nbits(u32 num, u32 amnt) {
	if (amnt >= SIZEOF_U32) {
		return 0;
	}
	return num & ((1ul << amnt) - 1);
}

static inline u32 cigint_get_bit_ref(const Cigint *a, u32 pos) {
	assert(pos < CIGINT_N * SIZEOF_U32);
	size_t data_index = CIGINT_N - 1 - pos / SIZEOF_U32;
	return u1_get_bit(a->data[data_index], pos % SIZEOF_U32);
}

inline u32 cigint_get_bit(CFREF(Cigint) a, u32 pos) {
	return cigint_get_bit_ref(&a, pos);
}

static inline Cigint *cigint_set_bit_ref(Cigint *a, u32 pos, u32 val) {
	assert(pos < CIGINT_N * SIZEOF_U32);
	size_t data_index = CIGINT_N - 1 - pos / SIZEOF_U32;
	a->data[data_index] = u1_set_bit(a->data[data_index], pos % SIZEOF_U32, val);
	return a;
}

inline Cigint cigint_set_bit(Cigint a, u32 pos, u32 val) {
	return *cigint_set_bit_ref(&a, pos, val);
}

uint cigint_print2(Cigint a) {
	uint counter = printf("0b"), old_counter = counter;
	int bit_index = highest_order(a) - 1;

	while (bit_index >= 0) {
		/* TODO: use %2 */
		int digit = get_bit(a, bit_index);
		counter += printf("%d", digit);
		bit_index--;
	}
	if (counter == old_counter) {
		counter += putchar('0');
	}
	return counter;
}

inline void cigint_and_ref(Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		lhs->data[i] &= rhs->data[i];
	}
}

// TODO: Write doc
inline Cigint cigint_and(Cigint lhs, CFREF(Cigint) rhs) {
	cigint_and_ref(&lhs , &rhs);
	return lhs;
}

/**
 * @brief Performs a bitwise OR operation (lhs |= rhs) between two Cigint values.
 * @param lhs Pointer to the left-hand operand; stores the result.
 * @param rhs Pointer to the right-hand operand.
 */
inline void cigint_or_ref(Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		lhs->data[i] |= rhs->data[i];
	}
}

/**
 * @brief Returns the bitwise OR (r = lhs | rhs) of two Cigint values.
 * This is a copy wrapper of ::cigint_or()
 * @param lhs Left-hand operand (copied before modification).
 * @param rhs Right-hand operand.
 */
inline Cigint cigint_or(Cigint lhs, CFREF(Cigint) rhs) {
	cigint_or_ref(&lhs, &rhs);
	return lhs;
}

// TODO: Write doc
inline void cigint_not_ref(Cigint *a) {
	for (size_t i = 0; i < CIGINT_N; ++i)
		a->data[i] = ~a->data[i];
}

// TODO: Write doc
inline Cigint cigint_not(Cigint a) {
	cigint_not_ref(&a);
	return a;
}

/**
 * @brief Performs a bitwise XOR operation (lhs ^= rhs) between two Cigint values.
 * @param lhs Pointer to the left-hand operand; stores the result.
 * @param rhs Pointer to the right-hand operand.
 */
inline void cigint_xor_ref(Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		lhs->data[i] ^= rhs->data[i];
	}
}

/**
 * @brief Returns the bitwise XOR (r = lhs ^ rhs) of two Cigint values.
 * This is a copy wrapper of ::cigint_xor()
 * @param lhs Left-hand operand (copied before modification).
 * @param rhs Right-hand operand.
 */
inline Cigint cigint_xor(Cigint lhs, CFREF(Cigint) rhs) {
	cigint_xor_ref(&lhs, &rhs);
	return lhs;
}

/* Two-phase, MSW-first left shift: limb move plus intra-word stitch. */
inline Cigint cigint_shl(CFREF(Cigint) lhs, u32 amnt) {
	if (amnt == 0) return lhs;

	const size_t limb_off = amnt / SIZEOF_U32;
	const u32 bits = amnt % SIZEOF_U32;

	if (limb_off >= CIGINT_N) return CIGINT_ZERO(); // everything shifted out
	Cigint r = (Cigint){0};
	// Phase 1: limb-only move (toward MSW)
	for (size_t i = 0; i + limb_off < CIGINT_N; ++i)
		r.data[i] = lhs.data[i + limb_off];
	// Phase 2: intra-word stitch (only if bits != 0)
	if (bits) {
		u32 snapshot[CIGINT_N];
		// for (size_t i = 0; i < CIGINT_N; ++i) snapshot[i] = r.data[i];
		memcpy(snapshot, r.data, sizeof snapshot);
		for (size_t i = 0; i < CIGINT_N; ++i) {
			const u32 hi = snapshot[i] << bits;
			const u32 lo = i + 1 < CIGINT_N ? snapshot[i + 1] >> (SIZEOF_U32 - bits) : 0u;
			r.data[i] = hi | lo;
		}
	}
	return r;
}

/* Two-phase, MSW-first right shift: limb move plus intra-word stitch */
inline Cigint cigint_shr(CFREF(Cigint) lhs, u32 amnt) {
	if (amnt == 0) return lhs;
	const size_t limb_off = amnt / SIZEOF_U32;
	const u32 bits = amnt % SIZEOF_U32;
	if (limb_off >= CIGINT_N) return CIGINT_ZERO(); // everything shifted out
	Cigint r = CIGINT_ZERO();
	// Phase 1: limb-only move (toward LSW)
	for (size_t i = CIGINT_N; i-- > limb_off; )
		r.data[i] = lhs.data[i - limb_off];
	// Phase 2: intra-word stitch (only if bits != 0)
	if (bits) {
		u32 snapshot[CIGINT_N];
		memcpy(snapshot, r.data, sizeof snapshot);
		for (size_t i = 0; i < CIGINT_N; ++i) {
			const u32 lo = snapshot[i] >> bits;
			const u32 hi = i > 0 ? snapshot[i - 1] << (SIZEOF_U32 - bits) : 0u;
			r.data[i] = hi | lo;
		}
	}
	return r;
}

static inline u32 cigint_highest_order_ref(const Cigint *num) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		if (num->data[i] > 0) {
			return u1_highest_order(num->data[i]) + (CIGINT_N - i - 1) * SIZEOF_U32;
		}
	}
	return 0;
}

inline u32 cigint_highest_order(CFREF(Cigint) num) {
	return cigint_highest_order_ref(&num);
}

inline Cigint cigint_pow2(u32 amnt) {
	assert(amnt < CIGINT_N * SIZEOF_U32);
	Cigint r = CIGINT_ZERO();
	size_t limb = CIGINT_N - 1 - (amnt / SIZEOF_U32);
	r.data[limb] = (u32)(1u << (amnt % SIZEOF_U32));
	return r;
}

static inline int cigint_cmp_ref(const Cigint *lhs, const Cigint *rhs) {
	for (size_t i = 0; i < CIGINT_N; ++i) {
		if (lhs->data[i] != rhs->data[i]) {
			return lhs->data[i] > rhs->data[i] ? 1 : -1;
		}
	}
	return 0;
}

inline int cigint_cmp(CFREF(Cigint) lhs, CFREF(Cigint) rhs) {
	return cigint_cmp_ref(&lhs, &rhs);
}

static inline int cigint_is0_ref(const Cigint *a) {
	for (size_t i = 0; i < CIGINT_N; ++i)
		if (a->data[i] != 0) return 0;
	return 1;
}

inline int cigint_is0(CFREF(Cigint) a) {
	return cigint_is0_ref(&a);
}

static inline void cigint_add_ref(Cigint *lhs, const Cigint *rhs) {
	u64 sum = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		sum = (u64) lhs->data[i] + (u64) rhs->data[i] + (sum >> SIZEOF_U32);
		lhs->data[i] = (u32) sum;
	}
}

inline Cigint cigint_add(Cigint lhs, CFREF(Cigint) rhs) {
	cigint_add_ref(&lhs, &rhs);
	return lhs;
}

static inline void cigint_sub_ref(Cigint *lhs, const Cigint *rhs) {
	u64 borrow = 0;
	for (size_t i = CIGINT_N; i-- > 0;) {
		u64 a = lhs->data[i];
		u64 t = (u64)rhs->data[i] + borrow;
		lhs->data[i] = (uint32_t)(a - t);
		borrow = a < t;
	}
}

inline Cigint cigint_sub(Cigint lhs, CFREF(Cigint) rhs) {
	cigint_sub_ref(&lhs, &rhs);
	return lhs;
}

// void cigint_mul_ref(Cigint *a, const Cigint *b) {
// 	Cigint temp = CIGINT_ZERO();
// 	u64 carry = 0;
//
// 	// Compute LSW-first into temp
// 	for (size_t k = 0; k < CIGINT_N; ++k) {
// 		u64 acc = carry;
// 		for (size_t i = 0; i <= k; ++i) {
// 			acc += (u64)a->data[CIGINT_N - 1 - i] * (u64)b->data[CIGINT_N - 1 - (k - i)];
// 		}
// 		temp.data[k] = (uint32_t)acc;
// 		carry = acc >> 32;
// 	}
//
// 	// Copy temp back to a->data in MSW-first order
// 	for (size_t k = 0; k < CIGINT_N; ++k) {
// 		a->data[CIGINT_N - 1 - k] = temp.data[k];
// 	}
// }

static inline void cigint_mul_ref(Cigint *lhs, const Cigint *rhs) {
	Cigint tmp = CIGINT_ZERO();
	u64 carry = 0;

	for (size_t k = 0; k < CIGINT_N; ++k) {
		u64 acc = carry;
		for (size_t i = 0; i <= k; ++i) {
			acc += (u64) lhs->data[CIGINT_N - 1 - i] * (u64) rhs->data[CIGINT_N - 1 - (k - i)];
		}
		tmp.data[CIGINT_N - 1 - k] = (uint32_t) acc;
		carry = acc >> SIZEOF_U32;
	}
	*lhs = tmp;
}

static inline void cigint_mul_refex(const Cigint *lhs, const Cigint *rhs, Cigint *res) {
	u64 carry = 0;
	for (size_t k = 0; k < CIGINT_N; ++k) {
		u64 acc = carry;
		for (size_t i = 0; i <= k; ++i) {
			acc += (u64) lhs->data[CIGINT_N - 1 - i] * (u64) rhs->data[CIGINT_N - 1 - (k - i)];
		}
		res->data[CIGINT_N - 1 - k] = (uint32_t) acc;
		carry = acc >> SIZEOF_U32;
	}
}

inline Cigint cigint_mul(Cigint lhs, CFREF(Cigint) rhs) {
	cigint_mul_ref(&lhs, &rhs);
	return lhs;
}

static inline void cigint_sqr_ref(Cigint *base) {
	Cigint tmp = CIGINT_ZERO();
	for (size_t i = 0; i < CIGINT_N; ++i) {
		for (size_t j = 0; j <= i; ++j) {
			u64 p = (u64) base->data[i] * (u64) base->data[j];
			if (i != j) p <<= 1; // double off-diagonal
			size_t k = i + j;
			if (k < CIGINT_N) {
				u64 sum = (u64) tmp.data[k] + p;
				tmp.data[k] = (u32) sum; // ignore overflow beyond 32/64 bits of out[k]
			}
		}
	}
	*base = tmp;
}

inline Cigint cigint_sqr(Cigint base) {
	cigint_sqr_ref(&base);
	return base;
}

static inline void cigint_pow_ref(Cigint *base, u32 exp) {
	Cigint res = CIGINT_ZERO();
	res.data[CIGINT_N - 1] = 1;
	while (exp) {
		if (exp & 1u) cigint_mul_ref(&res, base);
		exp >>= 1;
		if (!exp) break;
		cigint_sqr_ref(base);
	}
	*base = res;
}

inline Cigint cigint_pow(Cigint base, u32 exp) {
	cigint_pow_ref(&base, exp);
	return base;
}

static inline Cigint cigint_from_u32(u32 x) {
	Cigint tmp = CIGINT_ZERO();
	tmp.data[CIGINT_N - 1] = x;
	return tmp;
}

/* bitwise restoring long division
 * q,r can be NULL independent
 */
static inline void cigint_divmod_ref(const Cigint *lhs, const Cigint *rhs, Cigint *q, Cigint *r) {
	assert(!cigint_is0_ref(rhs));
	int cmp = cigint_cmp_ref(lhs, rhs);
	if (cmp < 0) {
		if (q) *q = CIGINT_ZERO();
		if (r) *r = *lhs;
		return;
	}
	if (cmp == 0) {
		if (q) {
			Cigint one = CIGINT_ZERO();
			one.data[CIGINT_N - 1] = 1;
			*q = one;
		}
		if (r) *r = CIGINT_ZERO();
		return;
	}

	Cigint quotient = CIGINT_ZERO();
	Cigint rem = CIGINT_ZERO();

	int top = (int) cigint_highest_order_ref(lhs) - 1;
	for (int bit = top; bit >= 0; --bit) {
		u32 carry = cigint_get_bit_ref(lhs, (u32) bit);
		for (size_t i = CIGINT_N; i-- > 0; ) {
			u32 v = rem.data[i];
			rem.data[i] = (v << 1) | carry;
			carry = v >> 31;
		}

		if (cigint_cmp_ref(&rem, rhs) >= 0) {
			cigint_sub_ref(&rem, rhs);
			quotient = cigint_set_bit(quotient, (u32) bit, 1u);
		}
	}

	if (q) *q = quotient;
	if (r) *r = rem;
}

inline void cigint_divmod(CFREF(Cigint) lhs, CFREF(Cigint) rhs, Cigint *q, Cigint *r) {
	cigint_divmod_ref(&lhs, &rhs, q, r);
}

/* quotient only */
inline Cigint cigint_div(CFREF(Cigint) lhs, CFREF(Cigint) rhs) {
	Cigint q;
	cigint_divmod_ref(&lhs, &rhs, &q, NULL);
	return q;
}

/* remainder only */
inline Cigint cigint_mod(CFREF(Cigint) lhs, CFREF(Cigint) rhs) {
	Cigint r;
	cigint_divmod_ref(&lhs, &rhs, NULL, &r);
	return r;
}

/* single-limb divisor, fixed version */
static inline void cigint_sdivmod_ref(const Cigint *lhs, u32 rhs, Cigint *q, u32 *r) {
	assert(rhs != 0);
	u64 rem = 0;
	Cigint quo = CIGINT_ZERO();

	u32 hord = cigint_highest_order_ref(lhs);
	// walk bits from MSB -> LSB
	for (int bit = (int) hord - 1; bit >= 0; --bit) {
		rem = (rem << 1) | cigint_get_bit_ref(lhs, (u32) bit);
		if (rem >= rhs) {
			rem -= rhs;
			quo = cigint_set_bit(quo, (u32)bit, 1u);
		}
	}

	if (q) *q = quo;
	if (r) *r = rem;
}

inline void cigint_sdivmod(CFREF(Cigint) lhs, const u32 rhs, Cigint *q, u32 *r) {
	cigint_sdivmod_ref(&lhs, rhs, q, r);
}

inline u32 cigint_print2(CFREF(Cigint) a) {
	u32 counter = printf("0b");
	u32 ho = cigint_highest_order(a);
	if (ho == 0) {
		counter += (u32)putchar('0');
		return counter;
	}
	for (u32 bit = ho; bit-- > 0;) {
		int d = (int) cigint_get_bit_ref(&a, bit);
		counter += printf("%d", d);
	}
	return counter;
}

// u32 cigint_print2(CFREF(Cigint) a) {
// 	u32 counter = printf("0b"), old_counter = counter;
// 	int bit_index = cigint_highest_order(a) - 1;
//
// 	while (bit_index >= 0) {
// 		/* TODO: use %2 */
// 		int digit = cigint_get_bit_ref(&a, bit_index);
// 		counter += printf("%d", digit);
// 		--bit_index;
// 	}
// 	if (counter == old_counter) {
// 		counter += putchar('0');
// 	}
// 	return counter;
// }

// Each Cigint has CIGINT_N * 32 bits.
// Each 10^8 chunk holds ~26.6 bits (log2(10^8) ≈ 26.6). So max chunks = ceil(total_bits / 26.6)
#define CIGINT_PRINT10_CHUNKS ((CIGINT_N * SIZEOF_U32 + 26) / 27)

inline u32 cigint_print10(CFREF(Cigint) a) {
	if (cigint_is0(a)) {
		putchar('0');
		return 1;
	}
	u32 remainders[CIGINT_PRINT10_CHUNKS];
	size_t count = 0;
	Cigint q, n = a;
	while (!cigint_is0(n)) {
		u32 r;
		cigint_sdivmod(n, 100000000U, &q, &r);
		remainders[count++] = r;
		n = q;
	}

	u32 counter = 0;
	counter += printf("%u", remainders[count - 1]);
	for (size_t i = count - 1; i-- > 0;) {
		counter += printf("%08u", remainders[i]);
	}
	return counter;
}

static u32 cigint_print16_impl(CFREF(Cigint) a, int upper) {
	u32 counter = 0;
	counter += printf("0x");
	size_t i = 0;
	while (i < CIGINT_N && a.data[i] == 0u) ++i;
	if (i == CIGINT_N) {
		counter += putchar('0');
		return counter;
	}
	counter += printf(upper ? "%X" : "%x", a.data[i]);
	for (size_t j = i + 1; j < CIGINT_N; ++j) {
		counter += printf(upper ? "%08X" : "%08x", a.data[j]);
	}
	return counter;
}

inline u32 cigint_print16(CFREF(Cigint) a)       { return cigint_print16_impl(a, 0); }
inline u32 cigint_print16_upper(CFREF(Cigint) a) { return cigint_print16_impl(a, 1); }

inline u32 cigint_printf(const char *fmt, ...) {
	u32 counter = 0;
	va_list lst;
	va_start(lst, fmt);
	while (*fmt != '\0') {
		switch (*fmt) {
			case '%': {
				fmt++;
				if (*fmt == '%') {
					putchar('%');
					counter++;
				} else if (*fmt == 'C') {
					char next = *(fmt + 1);
					if (next == 'b' || next == 'd' || next == 'x' || next == 'X') {
						fmt++;
						Cigint num = va_arg(lst, Cigint);
						if (*fmt == 'b')      counter += cigint_print2(num);
						else if (*fmt == 'd') counter += cigint_print10(num);
						else if (*fmt == 'x') counter += cigint_print16(num);
						else                  counter += cigint_print16_upper(num); /* 'X' */
					}
				} else if (*fmt == 'c') {
					int ch = va_arg(lst, int);
					counter += putchar(ch);
				} else if (*fmt == 'd' || *fmt == 'i') {
					int num = va_arg(lst, int);
					counter += printf("%d", num);
				} else if (*fmt == 's') {
					char *str = (char*) va_arg(lst, char*);
					counter += printf("%s", str);
				}
				break;
			}
			default: {
				counter += putchar(*fmt);
			}
		}
		fmt++;
	}

	va_end(lst);
	return counter;
}

static inline int is_space_c(unsigned char c) {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c=='\v';
}

static inline int hex_val(unsigned char c) {
	if (c >= '0' && c <= '9') return c - '0';
	if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
	if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
	return -1;
}

inline Cigint cigint_from_dec(const char *s) {
	assert(s && "cigint_from_dec: null pointer");
	Cigint out = CIGINT_ZERO();

	// skip leading spaces and optional '+'
	while (is_space_c(*s)) ++s;
	if (*s == '+') ++s;
	assert(*s != '-' && "cigint_from_dec: negative not supported");

	// skip leading zeros, underscores, spaces
	const char *p = s;
	int any = 0;
	while (*p == '0' || *p == '_' || is_space_c(*p)) {
		if (*p == '0') any = 1;
		++p;
	}
	Cigint n10 = cigint_from_u32(10u);
	Cigint tmp = CIGINT_ZERO();
	for (; *p; ++p) {
		char c = *p;
		if (c == '_' || is_space_c(c)) continue;
		if (c < '0' || c > '9') break;
		any = 1;
		cigint_mul_ref(&out, &n10);
		tmp.data[CIGINT_N - 1] = c - '0';
		cigint_add_ref(&out, &tmp);
	}

	// trailing junk? allow only spaces/underscores
	while (*p && (is_space_c(*p) || *p == '_')) ++p;
	assert(any && "cigint_from_dec: no digits");
	return out;
}

inline Cigint cigint_from_hex(const char *s) {
	assert(s && "cigint_from_hex: null pointer");
	Cigint out = CIGINT_ZERO();

	while (is_space_c(*s)) ++s;
	if (*s == '+') ++s;
	assert(*s != '-' && "cigint_from_hex: negative not supported");

	if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;

	const char *p = s;
	int any = 0;

	// skip leading zeros/sep
	while (*p == '0' || *p == '_' || is_space_c(*p)) {
		if (*p == '0') any = 1;
		++p;
	}

	Cigint n16 = cigint_from_u32(16u);
	Cigint tmp = CIGINT_ZERO();
	for (; *p; ++p) {
		char c = *p;
		if (c == '_' || is_space_c(c)) continue;
		int d = hex_val(c);
		if (d < 0) break;
		any = 1;
		cigint_mul_ref(&out, &n16);
		tmp.data[CIGINT_N - 1] = d;
		cigint_add_ref(&out, &tmp);
	}

	while (*p && (is_space_c(*p) || *p == '_')) ++p;
	assert(any && "cigint_from_hex: no digits");
	return out;
}

inline Cigint cigint_from_bin(const char *s) {
	assert(s && "cigint_from_bin: null pointer");
	Cigint out = CIGINT_ZERO();
	while (is_space_c(*s)) ++s;
	if (s[0] == '0' && (s[1] == 'b' || s[1] == 'B')) s += 2;
	while (*s == '0' || *s == '_' || is_space_c(*s)) ++s;
	size_t k = 0;
	for (const char *p = s; *p; ++p) {
		if (*p == '0' || *p == '1') {
			cigint_set_bit_ref(&out, k++, *p == '1');
		} else if (*p != '_' && !is_space_c(*p)) {
			break; // stop at the 1st invalid chr
		}
	}
	assert(k && "cigint_from_bin: no digits");
	cigint_bit_reverse_n_ref(&out, k);
	return out;
}

inline Cigint cigint_from_str(const char *s) {
	assert(s && "cigint_from_str: null pointer");
	const char *p = s;
	while (is_space_c(*p)) ++p;
	if (*p == '+') ++p;
	if (*p == '-') {
		assert(0 && "cigint_from_str: negative not supported");
	}

	if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) return cigint_from_hex(p);
	if (p[0] == '0' && (p[1] == 'b' || p[1] == 'B')) return cigint_from_bin(p);
	return cigint_from_dec(p);
}

#endif

#ifdef __cplusplus
inline Cigint operator+(const Cigint &lhs, const Cigint &rhs) {
	return cigint_add(lhs, rhs);
}

inline const Cigint &operator+=(Cigint &lhs, const Cigint &rhs) {
	cigint_add_ref(&lhs, &rhs);
	return lhs;
}

/* TODO: find an ideal way when calculate with u32 */
inline Cigint operator+(const Cigint &lhs, u32 rhs) {
	Cigint tmp = cigint_from_u32(rhs);
	return cigint_add(lhs, tmp);
}

inline const Cigint &operator+=(Cigint &lhs, u32 rhs) {
	Cigint tmp = cigint_from_u32(rhs);
	cigint_add_ref(&lhs, &tmp);
	return lhs;
}

inline Cigint operator-(const Cigint &lhs, const Cigint &rhs) {
	return cigint_sub(lhs, rhs);
}

inline const Cigint &operator-=(Cigint &lhs, const Cigint &rhs) {
	cigint_sub_ref(&lhs, &rhs);
	return lhs;
}

inline Cigint operator*(const Cigint &lhs, const Cigint &rhs) {
	return cigint_mul(lhs, rhs);
}

inline const Cigint &operator*=(Cigint &lhs, const Cigint &rhs) {
	cigint_mul_ref(&lhs, &rhs);
	return lhs;
}

inline Cigint operator/(const Cigint &lhs, const Cigint &rhs) {
	return cigint_div(lhs, rhs);
}

inline const Cigint &operator/=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_div(lhs, rhs);
	return lhs;
}

inline bool operator==(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp_ref(&lhs, &rhs) == 0;
}

inline bool operator!=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp_ref(&lhs, &rhs) != 0;
}

inline bool operator>(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp_ref(&lhs, &rhs) > 0;
}

inline bool operator<(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp_ref(&lhs, &rhs) < 0;
}

inline bool operator>=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp_ref(&lhs, &rhs) >= 0;
}

inline bool operator<=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp_ref(&lhs, &rhs) <= 0;
}
#endif
#endif