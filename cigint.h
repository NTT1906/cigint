#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
typedef struct {
	uint64_t hi;
	uint64_t lo;
} uint128_t;
#define u128_zero (uint128_t) {0}
#define uint128_len 39 /* floor(log10(pow(2,128) - 1)) + 1 = 39 */

void print2(uint128_t num);
void print10(uint128_t num);
uint128_t from_u64(uint64_t num);
uint128_t u128_and(uint128_t a, uint128_t b);
uint128_t u128_or(uint128_t a, uint128_t b);
uint128_t u128_xor(uint128_t a, uint128_t b);
uint128_t u128_not(uint128_t a);
uint128_t u128_shl(uint128_t num, uint8_t amnt);
uint128_t u128_shr(uint128_t num, uint8_t amnt);
int u128_eq(uint128_t a, uint128_t b);
int u128_gt(uint128_t a, uint128_t b);
int u128_ge(uint128_t a, uint128_t b);
int is_zero(uint128_t num);
uint128_t u128_add(uint128_t a, uint128_t b);
uint128_t u128_sub(uint128_t a, uint128_t b);
uint128_t u128_div(uint128_t a, uint128_t b);
uint128_t u128_mod(uint128_t a, uint128_t b);
uint128_t u128_neg(uint128_t num);

void sprint10(uint128_t num, char buf[uint128_len + 1]);
size_t slen(char *s);
void add(char *num1, char *num2);
