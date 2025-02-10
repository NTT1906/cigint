#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>

#define u64 uint64_t
#define u32 uint32_t
typedef struct {
	u64 hi;
	u64 lo;
} u128;

#define U128_ZERO (u128) {0}
#define U128_MAX_DIGITS 39 /* floor(log10(pow(2,128) - 1)) + 1 */

void u128_print2(u128 num);
void u128_print10(u128 num);
void i128_print10(u128 num);
u128 u128_from_u64(uint64_t num);
u128 u128_and(u128 a, u128 b);
u128 u128_or(u128 a, u128 b);
u128 u128_xor(u128 a, u128 b);
u128 u128_not(u128 a);
u128 u128_shl(u128 num, uint32_t amnt);
u128 u128_shr(u128 num, uint32_t amnt);
u32 u128_eq(u128 a, u128 b);
u32 u128_gt(u128 a, u128 b);
u32 u128_ge(u128 a, u128 b);
u32 u128_eq0(u128 num);
u128 u128_add(u128 a, u128 b);
u128 u128_sub(u128 a, u128 b);
u128 u128_div(u128 a, u128 b);
u128 u128_mod(u128 a, u128 b);
u128 u128_neg(u128 num);

/*
void u128_tostr(u128 num, char buf[U128_MAX_DIGITS + 1UL]);
size_t slen(char *s, size_t max_len);
void add(char *num1, char *num2);
*/
