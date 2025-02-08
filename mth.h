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

void mul2(char *num1) {
	size_t len1 = slen(num1);
	int carry = 0;
	while (len1 != 0) {
		int res = (num1[--len1] - '0') * 2;
		num1[len1] = (res % 10 + carry) + '0';
		carry = res / 10;
	}
}
