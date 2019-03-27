/*-
 * Copyright (c) 2004-2017 Lev Walkin <vlm@lionet.info>. All rights reserved.
 * Redistribution and modifications are permitted subject to BSD license.
 */
#ifndef	ASN_TYPE_REAL_H
#define	ASN_TYPE_REAL_H

#include <asn_application.h>
#include <asn_codecs_prim.h> /* includes <asn_application.h> and <asn_codecs.h>, <asn_system.h> */

#ifdef __cplusplus
extern "C" {
#endif

typedef ASN__PRIMITIVE_TYPE_t REAL_t;

 
 /* Convert between native double type and REAL representation (DER).
 * RETURN VALUES:
 *  0: Value converted successfully
 * -1: An error occured while converting the value: invalid format.
 */
int asn_REAL2double(const REAL_t *real_ptr, double *d);
int asn_double2REAL(REAL_t *real_ptr, double d);



#ifdef __cplusplus
}
#endif

#endif	/* ASN_TYPE_REAL_H */
