#include <assert.h>
#include <stddef.h>
#include <stdio.h>

typedef unsigned int uint;
#define SIZEOF_UINT (8 * sizeof(uint))
uint u1_get_bit(uint num, uint pos) {
  if (pos >= SIZEOF_UINT) {
    return 0;
  }

  return (num & (1UL << pos)) >> pos;
}
uint u1_set_bit(uint num, uint pos, uint val) {
  if (pos >= SIZEOF_UINT) {
    return 0;
  }

  return (num & ~(1UL << pos)) | (val << pos);
}
uint u1_shl(uint num, uint amnt) {
  if (amnt >= SIZEOF_UINT) {
    return 0;
  }

  return num << amnt;
}
uint u1_shr(uint num, uint amnt) {
  if (amnt >= SIZEOF_UINT) {
    return 0;
  }

  return num >> amnt;
}
uint u1_highest_order(uint num) {
  uint pos = 0;
  while (num > 0) {
    pos++;
    num >>= 1;
  }

  return pos;
}
uint u1_get_last_nbits(uint num, uint amnt) {
  if (amnt >= SIZEOF_UINT) {
    return 0;
  }

  return num & ((1ul << amnt) - 1);
}

#define concat(a, b) a##b
#define get_bit(N) concat(u##N, _get_bit)
#define set_bit(N) concat(u##N, _set_bit)
#define and(N) concat(u##N, _and)
#define or(N) concat(u##N, _or)
#define xor(N) concat(u##N, _xor)
#define not(N) concat(u##N, _not)
#define shl(N) concat(u##N, _shl)
#define shr(N) concat(u##N, _shr)
#define highest_order(N) concat(u##N, _highest_order)
#define pow2(N) concat(u##N, _pow2)
#define print2(N) concat(u##N, _print2)
#define cmp(N) concat(u##N, _cmp)
#define is0(N) concat(u##N, _is0)
#define add(N) concat(u##N, _add)
#define sub(N) concat(u##N, _sub)
#define mul(N) concat(u##N, _mul)
#define div(N) concat(u##N, _div)
#define mod(N) concat(u##N, _mod)
#define divmod(N) concat(u##N, _divmod)
#define print10(N) concat(u##N, _print10)

#define CIGINT(N)                                                              \
  _Static_assert(N > 1, "N > 1");                                              \
  typedef struct {                                                             \
    uint data[N];                                                              \
  } CIGINT##N;                                                                 \
  uint get_bit(N)(CIGINT##N a, uint pos) {                                     \
    return u1_get_bit(a.data[N - 1 - pos / SIZEOF_UINT], pos % SIZEOF_UINT);   \
  }                                                                            \
  CIGINT##N set_bit(N)(CIGINT##N a, uint pos, uint val) {                      \
    a.data[N - 1 - pos / SIZEOF_UINT] =                                        \
        u1_set_bit(a.data[N - 1 - pos / SIZEOF_UINT], pos % SIZEOF_UINT, val); \
    return a;                                                                  \
  }                                                                            \
  void print2(N)(CIGINT##N a) {                                                \
    printf("0b");                                                              \
    int is_leading_zero = 1;                                                   \
    size_t data_index = 0;                                                     \
    size_t data_bits_len = SIZEOF_UINT;                                        \
                                                                               \
    while (data_index < N) {                                                   \
      int bit_index = data_bits_len;                                           \
      while (bit_index-- > 0) {                                                \
        int digit = u1_get_bit(a.data[data_index], bit_index);                 \
        if (is_leading_zero) {                                                 \
          if (digit == 1) {                                                    \
            is_leading_zero = 0;                                               \
          } else {                                                             \
            continue;                                                          \
          }                                                                    \
        }                                                                      \
        printf("%d", digit);                                                   \
      }                                                                        \
      data_index++;                                                            \
    }                                                                          \
    if (is_leading_zero) {                                                     \
      printf("0");                                                             \
    }                                                                          \
  }                                                                            \
  CIGINT##N and(N)(CIGINT##N a, CIGINT##N b) {                                 \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      a.data[i] &= b.data[i];                                                  \
      i++;                                                                     \
    }                                                                          \
    return a;                                                                  \
  }                                                                            \
  CIGINT##N or(N)(CIGINT##N a, CIGINT##N b) {                                  \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      a.data[i] |= b.data[i];                                                  \
      i++;                                                                     \
    }                                                                          \
    return a;                                                                  \
  }                                                                            \
  CIGINT##N xor(N)(CIGINT##N a, CIGINT##N b) {                                 \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      a.data[i] ^= b.data[i];                                                  \
      i++;                                                                     \
    }                                                                          \
    return a;                                                                  \
  }                                                                            \
  CIGINT##N not(N)(CIGINT##N a) {                                              \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      a.data[i] = ~a.data[i];                                                  \
      i++;                                                                     \
    }                                                                          \
    return a;                                                                  \
  }                                                                            \
  CIGINT##N shl(N)(CIGINT##N a, uint amnt) {                                   \
    CIGINT##N res = a;                                                         \
    size_t i = 0;                                                              \
    size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;                    \
    size_t rshift_amnt = SIZEOF_UINT - (amnt % SIZEOF_UINT);                   \
    while (i < N - offset) {                                                   \
      res.data[i] = u1_shl(a.data[i], amnt);                                   \
      res.data[i] |= u1_shr(a.data[i + offset], rshift_amnt);                  \
      i++;                                                                     \
    }                                                                          \
    while (i < N) {                                                            \
      res.data[i] = u1_shl(a.data[i], amnt);                                   \
      i++;                                                                     \
    }                                                                          \
    return res;                                                                \
  }                                                                            \
  CIGINT##N shr(N)(CIGINT##N a, uint amnt) {                                   \
    CIGINT##N res = a;                                                         \
    size_t i = 0;                                                              \
    size_t offset = (amnt + SIZEOF_UINT - 1) / SIZEOF_UINT;                    \
    size_t bits_amnt = amnt % SIZEOF_UINT;                                     \
    size_t lshift_amnt = SIZEOF_UINT - bits_amnt;                              \
    while (i < N - offset) {                                                   \
      res.data[N - 1 - i] = u1_shr(a.data[N - 1 - i], amnt);                   \
      uint last_bits =                                                         \
          u1_get_last_nbits(a.data[N - 1 - i - offset], bits_amnt);            \
      res.data[N - 1 - i] |= u1_shl(last_bits, lshift_amnt);                   \
      i++;                                                                     \
    }                                                                          \
    while (i < N) {                                                            \
      res.data[N - 1 - i] = u1_shr(a.data[N - 1 - i], amnt);                   \
      i++;                                                                     \
    }                                                                          \
    return res;                                                                \
  }                                                                            \
  uint highest_order(N)(CIGINT##N num) {                                       \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      if (num.data[i] > 0) {                                                   \
        return u1_highest_order(num.data[i]) + (N - i - 1) * SIZEOF_UINT;      \
      }                                                                        \
      i++;                                                                     \
    }                                                                          \
    return 0;                                                                  \
  }                                                                            \
  CIGINT##N pow2(N)(uint amnt) {                                               \
    assert(amnt < N * SIZEOF_UINT);                                            \
    CIGINT##N res = {0};                                                       \
    res.data[amnt / SIZEOF_UINT] = (1 << (amnt % SIZEOF_UINT));                \
    return res;                                                                \
  }                                                                            \
  int cmp(N)(CIGINT##N a, CIGINT##N b) {                                       \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      if (a.data[i] != b.data[i]) {                                            \
        return a.data[i] > b.data[i] ? 1 : -1;                                 \
      }                                                                        \
      i++;                                                                     \
    }                                                                          \
    return 0;                                                                  \
  }                                                                            \
  int is0(N)(CIGINT##N a) {                                                    \
    size_t i = 0;                                                              \
    while (i < N) {                                                            \
      if (a.data[i] != 0) {                                                    \
        return 0;                                                              \
      }                                                                        \
      i++;                                                                     \
    }                                                                          \
    return 1;                                                                  \
  }                                                                            \
  CIGINT##N add(N)(CIGINT##N a, CIGINT##N b) {                                 \
    while (!is0(N)(b)) {                                                       \
      CIGINT##N carry = and(N)(a, b);                                          \
      a = xor(N)(a, b);                                                        \
      b = shl(N)(carry, 1);                                                    \
    }                                                                          \
    return a;                                                                  \
  }                                                                            \
  CIGINT##N sub(N)(CIGINT##N a, CIGINT##N b) {                                 \
    while (!is0(N)(b)) {                                                       \
      CIGINT##N borrow = and(N)(not(N)(a), b);                                 \
      a = xor(N)(a, b);                                                        \
      b = shl(N)(borrow, 1);                                                   \
    }                                                                          \
    return a;                                                                  \
  }                                                                            \
  CIGINT##N mul(N)(CIGINT##N a, CIGINT##N b) {                                 \
    CIGINT##N res = {0};                                                       \
    while (!is0(N)(b)) {                                                       \
      if (u1_get_bit(b.data[N - 1], 0) == 1) {                                 \
        res = add(N)(res, a);                                                  \
      }                                                                        \
      a = shl(N)(a, 1);                                                        \
      b = shr(N)(b, 1);                                                        \
    }                                                                          \
    return res;                                                                \
  }                                                                            \
  CIGINT##N div(N)(CIGINT##N a, CIGINT##N b) {                                 \
    assert(!is0(N)(b));                                                        \
    int comp = cmp(N)(a, b);                                                   \
    if (comp <= 0) {                                                           \
      CIGINT##N res = {0};                                                     \
      res.data[N - 1] = comp == 0;                                             \
      return res;                                                              \
    }                                                                          \
    CIGINT##N quotient = {0}, r = quotient;                                    \
    int bit_index = highest_order(N)(a) - 1;                                   \
    while (bit_index >= 0) {                                                   \
      r = shl(N)(r, 1);                                                        \
      r = set_bit(N)(r, 0, get_bit(N)(a, bit_index));                          \
      if (cmp(N)(r, b) >= 0) {                                                 \
        r = sub(N)(r, b);                                                      \
        quotient = set_bit(N)(quotient, bit_index, 1);                         \
      }                                                                        \
      bit_index--;                                                             \
    }                                                                          \
    return quotient;                                                           \
  }                                                                            \
  CIGINT##N mod(N)(CIGINT##N a, CIGINT##N b) {                                 \
    assert(!is0(N)(b));                                                        \
    int comp = cmp(N)(a, b);                                                   \
    if (comp <= 0) {                                                           \
      return a;                                                                \
    }                                                                          \
    CIGINT##N quotient = {0}, r = quotient;                                    \
    int bit_index = highest_order(N)(a) - 1;                                   \
    while (bit_index >= 0) {                                                   \
      r = shl(N)(r, 1);                                                        \
      r = set_bit(N)(r, 0, get_bit(N)(a, bit_index));                          \
      if (cmp(N)(r, b) >= 0) {                                                 \
        r = sub(N)(r, b);                                                      \
        quotient = set_bit(N)(quotient, bit_index, 1);                         \
      }                                                                        \
      bit_index--;                                                             \
    }                                                                          \
    return r;                                                                  \
  }                                                                            \
  void divmod(N)(CIGINT##N a, CIGINT##N b, CIGINT##N * q, CIGINT##N * r) {     \
    assert(!is0(N)(b));                                                        \
    int comp = cmp(N)(a, b);                                                   \
    if (comp <= 0) {                                                           \
      if (q != NULL) {                                                         \
        CIGINT##N res = {0};                                                   \
        res.data[N - 1] = comp == 0;                                           \
        *q = res;                                                              \
      }                                                                        \
      if (r != NULL) {                                                         \
        *r = a;                                                                \
      }                                                                        \
      return;                                                                  \
    }                                                                          \
    CIGINT##N quotient = {0}, remainder = quotient;                            \
    int bit_index = highest_order(N)(a) - 1;                                   \
    while (bit_index >= 0) {                                                   \
      remainder = shl(N)(remainder, 1);                                        \
      remainder = set_bit(N)(remainder, 0, get_bit(N)(a, bit_index));          \
      if (cmp(N)(remainder, b) >= 0) {                                         \
        remainder = sub(N)(remainder, b);                                      \
        quotient = set_bit(N)(quotient, bit_index, 1);                         \
      }                                                                        \
      bit_index--;                                                             \
    }                                                                          \
    if (q != NULL) {                                                           \
      *q = quotient;                                                           \
    }                                                                          \
    if (r != NULL) {                                                           \
      *r = remainder;                                                          \
    }                                                                          \
  }                                                                            \
  uint print10(N)(CIGINT##N a) {                                               \
    if (is0(N)(a)) {                                                           \
      return 0;                                                                \
    }                                                                          \
    CIGINT##N modulo = {0};                                                    \
    /* TODO:: calculate power of 10 based on given length*/                    \
    int num_len = 3;                                                           \
    modulo.data[N - 1] = 1000;                                                 \
    CIGINT##N r, q;                                                            \
    divmod(N)(a, modulo, &q, &r);                                              \
    if (print10(N)(q) == 0) {                                                  \
      printf("%u", r.data[N - 1]);                                             \
    } else {                                                                   \
      printf("%0*u", num_len, r.data[N - 1]);                                  \
    }                                                                          \
    return num_len;                                                            \
  }
