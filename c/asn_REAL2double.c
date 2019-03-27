/*-
 * Copyright (c) 2004-2017 Lev Walkin <vlm@lionet.info>. All rights reserved.
 * Redistribution and modifications are permitted subject to BSD license.
 */
#define	_ISOC99_SOURCE		/* For ilogb() and quiet NAN */
#ifndef _BSD_SOURCE
#define	_BSD_SOURCE		/* To reintroduce finite(3) */
#endif
#include <asn_internal.h>
#if	defined(__alpha)
#include <sys/resource.h>	/* For INFINITY */
#endif
#include <stdlib.h>	/* for strtod(3) */
#include <math.h>
#include <float.h>
#include <errno.h>
#include <REAL.h>
#include <OCTET_STRING.h>

#undef	INT_MAX
#define	INT_MAX	((int)(((unsigned int)-1) >> 1))

#if	!(defined(NAN) || defined(INFINITY))
static volatile double real_zero CC_NOTUSED = 0.0;
#endif
#ifndef	NAN
#define	NAN	(0.0/0.0)
#endif
#ifndef	INFINITY
#define	INFINITY	(1.0/0.0)
#endif

#if defined(__clang__)
/*
 * isnan() is defined using generic selections and won't compile in
 * strict C89 mode because of too fancy system's standard library.
 * However, prior to C11 the math had a perfectly working isnan()
 * in the math library.
 * Disable generic selection warning so we can test C89 mode with newer libc.
 */
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wc11-extensions"
static int asn_isnan(double d) {
    return isnan(d);
}
static int asn_isfinite(double d) {
#ifdef isfinite
    return isfinite(d);  /* ISO C99 */
#else
    return finite(d);    /* Deprecated on Mac OS X 10.9 */
#endif
}
#pragma clang diagnostic pop
#else   /* !clang */
#define asn_isnan(v)    isnan(v)
#ifdef isfinite
#define asn_isfinite(d)   isfinite(d)  /* ISO C99 */
#else
#define asn_isfinite(d)   finite(d)    /* Deprecated on Mac OS X 10.9 */
#endif
#endif  /* clang */

/*
 * REAL basic type description.
 */
static const ber_tlv_tag_t asn_DEF_REAL_tags[] = {
	(ASN_TAG_CLASS_UNIVERSAL | (9 << 2))
};
asn_TYPE_operation_t asn_OP_REAL = {
	ASN__PRIMITIVE_TYPE_free,
	REAL_print,
	REAL_compare,
	ber_decode_primitive,
	der_encode_primitive,
	REAL_decode_xer,
	REAL_encode_xer,
#ifdef	ASN_DISABLE_OER_SUPPORT
	0,
	0,
#else
	REAL_decode_oer,
	REAL_encode_oer,
#endif  /* ASN_DISABLE_OER_SUPPORT */
#ifdef	ASN_DISABLE_PER_SUPPORT
	0,
	0,
#else
	REAL_decode_uper,
	REAL_encode_uper,
#endif	/* ASN_DISABLE_PER_SUPPORT */
	REAL_random_fill,
	0	/* Use generic outmost tag fetcher */
};

char local_buf[64];
char *buf = local_buf;

int
asn_REAL2double(const REAL_t *st, double *dbl_value) {
	unsigned int octv;

	if(!st || !st->buf) {
		errno = EINVAL;
		return -1;
	}

	if(st->size == 0) {
		*dbl_value = 0;
		return 0;
	}

	octv = st->buf[0];	/* unsigned byte */

	

	/*
	 * Binary representation.
	 */
    {
	double m;
	int32_t expval;		/* exponent value */
	unsigned int elen;	/* exponent value length, in octets */
	int scaleF;
	int baseF;
	uint8_t *ptr;
	uint8_t *end;
	int sign;

	switch((octv & 0x30) >> 4) {
	case 0x00: baseF = 1; break;	/* base 2 */
	case 0x01: baseF = 3; break;	/* base 8 */
	case 0x02: baseF = 4; break;	/* base 16 */
	default:
		/* Reserved field, can't parse now. */
		errno = EINVAL;
		return -1;
	}

	sign = (octv & 0x40);	/* bit 7 */
	scaleF = (octv & 0x0C) >> 2;	/* bits 4 to 3 */

	if(st->size <= 1 + (octv & 0x03)) {
		errno = EINVAL;
		return -1;
	}

	elen = (octv & 0x03);	/* bits 2 to 1; 8.5.6.4 */
	if(elen == 0x03) {	/* bits 2 to 1 = 11; 8.5.6.4, case d) */
		elen = st->buf[1];	/* unsigned binary number */
		if(elen == 0 || st->size <= (2 + elen)) {
			errno = EINVAL;
			return -1;
		}
		/* FIXME: verify constraints of case d) */
		ptr = &st->buf[2];
	} else {
		ptr = &st->buf[1];
	}

	/* Fetch the multibyte exponent */
	expval = (int)(*(int8_t *)ptr);
	if(elen >= sizeof(expval)-1) {
		errno = ERANGE;
		return -1;
	}
	end = ptr + elen + 1;
	for(ptr++; ptr < end; ptr++)
		expval = (expval * 256) + *ptr;

	m = 0.0;	/* Initial mantissa value */

	/* Okay, the exponent is here. Now, what about mantissa? */
	end = st->buf + st->size;
	for(; ptr < end; ptr++)
		m = ldexp(m, 8) + *ptr;

	if(0)
	ASN_DEBUG("m=%.10f, scF=%d, bF=%d, expval=%d, ldexp()=%f, ldexp()=%f\n",
		m, scaleF, baseF, expval,
		ldexp(m, expval * baseF + scaleF),
		ldexp(m, scaleF) * pow(pow(2, baseF), expval)
	);

	/*
	 * (S * N * 2^F) * B^E
	 * Essentially:
	m = ldexp(m, scaleF) * pow(pow(2, baseF), expval);
	 */
	m = ldexp(m, expval * baseF + scaleF);
	if(asn_isfinite(m)) {
		*dbl_value = sign ? -m : m;
	} else {
		errno = ERANGE;
		return -1;
	}

    } /* if(binary_format) */

	return 0;
}
