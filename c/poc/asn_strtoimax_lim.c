enum asn_strtox_result_e
asn_strtoimax_lim(const char *str, const char **end, intmax_t *intp) {
	int sign = 1;
	intmax_t value;

#define ASN1_INTMAX_MAX ((~(uintmax_t)0) >> 1)
    const intmax_t upper_boundary = ASN1_INTMAX_MAX / 10;
	intmax_t last_digit_max = ASN1_INTMAX_MAX % 10;
#undef  ASN1_INTMAX_MAX

	if(str >= *end) return ASN_STRTOX_ERROR_INVAL;

	switch(*str) {
	case '-':
		last_digit_max++;
		sign = -1;
		/* FALL THROUGH */
	case '+':
		str++;
		if(str >= *end) {
			*end = str;
			return ASN_STRTOX_EXPECT_MORE;
		}
	}

	for(value = 0; str < (*end); str++) {
		switch(*str) {
		case 0x30: case 0x31: case 0x32: case 0x33: case 0x34:
		case 0x35: case 0x36: case 0x37: case 0x38: case 0x39: {
			int d = *str - '0';
			if(value < upper_boundary) {
				value = value * 10 + d;
			} else if(value == upper_boundary) {
				if(d <= last_digit_max) {
					if(sign > 0) {
						value = value * 10 + d;
					} else {
						sign = 1;
						value = -value * 10 - d;
					}
				} else {
					*end = str;
					return ASN_STRTOX_ERROR_RANGE;
				}
			} else {
				*end = str;
				return ASN_STRTOX_ERROR_RANGE;
			}
		    }
		    continue;
		default:
		    *end = str;
		    *intp = sign * value;
		    return ASN_STRTOX_EXTRA_DATA;
		}
	}

	*end = str;
	*intp = sign * value;
	return ASN_STRTOX_OK;
}
