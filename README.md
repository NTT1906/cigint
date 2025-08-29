# Cigint - C library for computing with unsigned integers
### How to use

- Remember to define `CIGINT_IMPLEMENTATION` before including the library
``` c
#define CIGINT_IMPLEMENTATION
#include "cigint.h"
```

- There is a strip option to remove the prefix `cigint_` from function names by define `CIGINT_STRIP_PREFIX`.
Keep in mind that the stripped name of `cigint_and` has a letter `c` at the beginning, `cand`, to avoid conflicts with C++ macros.
The same applies to `cigint_or`, `cigint_xor` and `cigint_not`

- To specific the number of storage bytes, please define `CIGINT_N` as the result of dividing that number by 4. For example, if you need 32 bytes, then you define
``` c
#define CIGINT_N (32/4)
#include "cigint.h"
```
