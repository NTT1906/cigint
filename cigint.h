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

Cigint cigint_and(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		lhs.data[i] &= rhs.data[i];
		i++;
	}
	return lhs;
}

Cigint cigint_or(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		lhs.data[i] |= rhs.data[i];
		i++;
	}
	return lhs;
}

Cigint cigint_xor(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		lhs.data[i] ^= rhs.data[i];
		i++;
	}
	return lhs;
}

Cigint cigint_not(Cigint a) {
	size_t i = 0;
	while (i < CIGINT_N) {
		a.data[i] = ~a.data[i];
		i++;
	}
	return a;
}

Cigint cigint_shl(Cigint lhs, uint amnt) {
	Cigint res = lhs;
	size_t i = 0;
	size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;
	size_t rshift_amnt = SIZEOF_UINT - (amnt % SIZEOF_UINT);
	while (i < CIGINT_N - offset) {
		res.data[i] = u1_shl(lhs.data[i], amnt);
		res.data[i] |= u1_shr(lhs.data[i + offset], rshift_amnt);
		i++;
	}
	while (i < CIGINT_N) {
		res.data[i] = u1_shl(lhs.data[i], amnt);
		i++;
	}
	return res;
}

Cigint cigint_shr(Cigint lhs, uint amnt) {
	Cigint res = lhs;
	size_t i = 0;
	size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;
	size_t bits_amnt = amnt % SIZEOF_UINT;
	size_t lshift_amnt = SIZEOF_UINT - bits_amnt;
	while (i < CIGINT_N - offset) {
		res.data[CIGINT_N - 1 - i] = u1_shr(lhs.data[CIGINT_N - 1 - i], amnt);
		uint last_bits =
			u1_get_last_nbits(lhs.data[CIGINT_N - 1 - i - offset], bits_amnt);
		res.data[CIGINT_N - 1 - i] |= u1_shl(last_bits, lshift_amnt);
		i++;
	}
	while (i < CIGINT_N) {
		res.data[CIGINT_N - 1 - i] = u1_shr(lhs.data[CIGINT_N - 1 - i], amnt);
		i++;
	}
	return res;
}

uint cigint_highest_order(Cigint num) {
	size_t i = 0;
	while (i < CIGINT_N) {
		if (num.data[i] > 0) {
			return u1_highest_order(num.data[i]) + (CIGINT_N - i - 1) * SIZEOF_UINT;
		}
		i++;
	}
	return 0;
}

Cigint cigint_pow2(uint amnt) {
	assert(amnt < CIGINT_N * SIZEOF_UINT);
	Cigint res = {0};
	res.data[CIGINT_N - 1 - amnt / SIZEOF_UINT] = (1 << (amnt % SIZEOF_UINT));
	return res;
}

int cigint_cmp(Cigint lhs, Cigint rhs) {
	size_t i = 0;
	while (i < CIGINT_N) {
		if (lhs.data[i] != rhs.data[i]) {
			return lhs.data[i] > rhs.data[i] ? 1 : -1;
		}
		i++;
	}
	return 0;
}

int cigint_is0(Cigint a) {
	size_t i = 0;
	while (i < CIGINT_N) {
		if (a.data[i] != 0) {
			return 0;
		}
		i++;
	}
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

Cigint cigint_pow(Cigint lhs, uint amnt) {
	Cigint res = {0};
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
	res.data[CIGINT_N - 1] = 1;
	while (amnt > 0) {
		if (amnt % 2 == 1) {
			res = mul(res, lhs);
		}

		lhs = mul(lhs, lhs);
		amnt /= 2;
	}
	return res;
}

Cigint cigint_div(Cigint lhs, Cigint rhs) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		Cigint res = {0};
		res.data[CIGINT_N - 1] = comp == 0;
		return res;
	}
	Cigint quotient = {0}, r = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		r = cigint_shl(r, 1);
		r = set_bit(r, 0, get_bit(lhs, bit_index));
		if (cigint_cmp(r, rhs) >= 0) {
			r = cigint_sub(r, rhs);
			quotient = set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	return quotient;
}

Cigint cigint_mod(Cigint lhs, Cigint rhs) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		return lhs;
	}
	Cigint quotient = {0}, r = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		r = cigint_shl(r, 1);
		r = set_bit(r, 0, get_bit(lhs, bit_index));
		if (cigint_cmp(r, rhs) >= 0) {
			r = cigint_sub(r, rhs);
			quotient = set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	return r;
}

void cigint_divmod(Cigint lhs, Cigint rhs, Cigint *q, Cigint *r) {
	assert(!cigint_is0(rhs));
	int comp = cigint_cmp(lhs, rhs);
	if (comp <= 0) {
		if (q != NULL) {
			Cigint res = {0};
			res.data[CIGINT_N - 1] = comp == 0;
			*q = res;
		}
		if (r != NULL) {
			*r = lhs;
		}
		return;
	}
	Cigint quotient = {0}, remainder = quotient;
	int bit_index = cigint_highest_order(lhs) - 1;
	while (bit_index >= 0) {
		remainder = cigint_shl(remainder, 1);
		remainder = cigint_set_bit(remainder, 0, cigint_get_bit(lhs, bit_index));
		if (cigint_cmp(remainder, rhs) >= 0) {
			remainder = cigint_sub(remainder, rhs);
			quotient = set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	if (q != NULL) {
		*q = quotient;
	}
	if (r != NULL) {
		*r = remainder;
	}
}

void cigint_sdivmod(Cigint lhs, uint rhs, Cigint *q, uint *r) {
	assert(rhs != 0);
	uint hord = cigint_highest_order(lhs);
	if (hord < SIZEOF_UINT && lhs.data[CIGINT_N - 1] <= rhs) {
		if (q != NULL) {
			Cigint res = {0};
			res.data[CIGINT_N - 1] = lhs.data[CIGINT_N - 1] == rhs;
			*q = res;
		}
		if (r != NULL) {
			*r = lhs.data[CIGINT_N - 1];
		}
		return;
	}
	Cigint quotient = {0};
	uint remainder = 0;
	int bit_index = hord - 1;
	while (bit_index >= 0) {
		remainder = remainder << 1;
		remainder = u1_set_bit(remainder, 0, cigint_get_bit(lhs, bit_index));
		if (remainder >= rhs) {
			remainder -= rhs;
			quotient = set_bit(quotient, bit_index, 1);
		}
		bit_index--;
	}
	if (q != NULL) {
		*q = quotient;
	}
	if (r != NULL) {
		*r = remainder;
	}
}

/* TODO: stack overflow */
uint cigint_print10(Cigint a) {
	if (cigint_is0(a)) {
		return 0;
	}

	Cigint q;
	uint r;
	cigint_sdivmod(a, 100000000, &q, &r);

	uint counter = cigint_print10(q);
	if (counter == 0) {
		counter += printf("%u", r);
	}
	else {
		counter += printf("%0*u", 8, r);
	}
	return counter;
}

uint cigint_printf(const char *fmt, ...) {
	uint counter = 0;

	va_list lst;
	va_start(lst, fmt);
	while (*fmt != '\0') {
		switch (*fmt) {
			case '%': {
						  fmt++;
						  if (*fmt == '%') {
							  putchar('%');
							  counter++;
						  }
						  else if (*fmt == 'C') {
							  if (*(fmt + 1) == 'b' || *(fmt + 1) == 'd') {
								  fmt++;
								  Cigint num = (Cigint) va_arg(lst, Cigint);
								  if (*fmt == 'b') {
									  counter += cigint_print2(num);
								  }
								  else {
									  counter += cigint_print10(num);
								  }
							  }
						  }
						  else if (*fmt == 'c') {
							  int ch = va_arg(lst, int);
							  counter += putchar(ch);
						  }
						  else if (*fmt == 'd' || *fmt == 'i') {
							  int num = va_arg(lst, int);
							  counter += printf("%d", num);
						  }
						  else if (*fmt == 's') {
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
#endif

#ifdef __cplusplus
inline Cigint operator+(const Cigint &lhs, const Cigint &rhs) {
	return cigint_add(lhs, rhs);
}

inline const Cigint &operator+=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_add(lhs, rhs);
	return lhs;
}

/* TODO: find an ideal way when calculate with uint*/
inline Cigint operator+(const Cigint &lhs, uint rhs) {
	return cigint_add(lhs, rhs);
}

inline const Cigint &operator+=(Cigint &lhs, uint rhs) {
	lhs = cigint_add(lhs, rhs);
	return lhs;
}

inline Cigint operator-(const Cigint &lhs, const Cigint &rhs) {
	return cigint_sub(lhs, rhs);
}

inline const Cigint &operator-=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_sub(lhs, rhs);
	return lhs;
}

inline Cigint operator*(const Cigint &lhs, const Cigint &rhs) {
	return cigint_mul(lhs, rhs);
}

inline const Cigint &operator*=(Cigint &lhs, const Cigint &rhs) {
	lhs = cigint_mul(lhs, rhs);
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
	return cigint_cmp(lhs, rhs) == 0;
}

inline bool operator!=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) != 0;
}

inline bool operator>(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) > 0;
}

inline bool operator>=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) >= 0;
}

inline bool operator<=(const Cigint &lhs, const Cigint &rhs) {
	return cigint_cmp(lhs, rhs) <= 0;
}
#endif
#endif