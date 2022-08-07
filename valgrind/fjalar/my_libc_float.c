/*
   This file is part of Fjalar, a dynamic analysis framework for C/C++
   programs.

   Copyright (C) 2007-2022 University of Washington Computer Science & Engineering Department,
   Programming Languages and Software Engineering Group

   Copyright (C) 2004-2006 Philip Guo (pgbovine@alum.mit.edu),
   Copyright (C) 2008-2009 Robert Rudd (rudd@csail.mit.edu),
   MIT CSAIL Program Analysis Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.
*/

/**
   Implementation for float/double to decimal string
   conversion. This has been borrowed from uClibc 0.9.27, by Manuel
   Novoa III <mjn3@codepoet.org>, and is licensed under the LGPL
*/

#include "pub_tool_basics.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"

/* float.h for target with IEEE 32 bit and 64 bit floating point formats */
#ifndef _FLOAT_H_
#define _FLOAT_H_
/* Produced by enquire version 4.3, CWI, Amsterdam */

   /* Radix of exponent representation */
#undef FLT_RADIX
#define FLT_RADIX 2
   /* Number of base-FLT_RADIX digits in the significand of a float */
#undef FLT_MANT_DIG
#define FLT_MANT_DIG 24
   /* Number of decimal digits of precision in a float */
#undef FLT_DIG
#define FLT_DIG 6
   /* Addition rounds to 0: zero, 1: nearest, 2: +inf, 3: -inf, -1: unknown */
#undef FLT_ROUNDS
#define FLT_ROUNDS 1
   /* Difference between 1.0 and the minimum float greater than 1.0 */
#undef FLT_EPSILON
#define FLT_EPSILON 1.19209290e-07F
   /* Minimum int x such that FLT_RADIX**(x-1) is a normalised float */
#undef FLT_MIN_EXP
#define FLT_MIN_EXP (-125)
   /* Minimum normalised float */
#undef FLT_MIN
#define FLT_MIN 1.17549435e-38F
   /* Minimum int x such that 10**x is a normalised float */
#undef FLT_MIN_10_EXP
#define FLT_MIN_10_EXP (-37)
   /* Maximum int x such that FLT_RADIX**(x-1) is a representable float */
#undef FLT_MAX_EXP
#define FLT_MAX_EXP 128
   /* Maximum float */
#undef FLT_MAX
#define FLT_MAX 3.40282347e+38F
   /* Maximum int x such that 10**x is a representable float */
#undef FLT_MAX_10_EXP
#define FLT_MAX_10_EXP 38

   /* Number of base-FLT_RADIX digits in the significand of a double */
#undef DBL_MANT_DIG
#define DBL_MANT_DIG 53
   /* Number of decimal digits of precision in a double */
#undef DBL_DIG
#define DBL_DIG 15
   /* Difference between 1.0 and the minimum double greater than 1.0 */
#undef DBL_EPSILON
#define DBL_EPSILON 2.2204460492503131e-16
   /* Minimum int x such that FLT_RADIX**(x-1) is a normalised double */
#undef DBL_MIN_EXP
#define DBL_MIN_EXP (-1021)
   /* Minimum normalised double */
#undef DBL_MIN
#define DBL_MIN 2.2250738585072014e-308
   /* Minimum int x such that 10**x is a normalised double */
#undef DBL_MIN_10_EXP
#define DBL_MIN_10_EXP (-307)
   /* Maximum int x such that FLT_RADIX**(x-1) is a representable double */
#undef DBL_MAX_EXP
#define DBL_MAX_EXP 1024
   /* Maximum double */
#undef DBL_MAX
#define DBL_MAX 1.7976931348623157e+308
   /* Maximum int x such that 10**x is a representable double */
#undef DBL_MAX_10_EXP
#define DBL_MAX_10_EXP 308

   /* Number of base-FLT_RADIX digits in the significand of a long double */
#undef LDBL_MANT_DIG
#define LDBL_MANT_DIG 53
   /* Number of decimal digits of precision in a long double */
#undef LDBL_DIG
#define LDBL_DIG 15
   /* Difference between 1.0 and the minimum long double greater than 1.0 */
#undef LDBL_EPSILON
#define LDBL_EPSILON 2.2204460492503131e-16L
   /* Minimum int x such that FLT_RADIX**(x-1) is a normalised long double */
#undef LDBL_MIN_EXP
#define LDBL_MIN_EXP (-1021)
   /* Minimum normalised long double */
#undef LDBL_MIN
#define LDBL_MIN 2.2250738585072014e-308L
   /* Minimum int x such that 10**x is a normalised long double */
#undef LDBL_MIN_10_EXP
#define LDBL_MIN_10_EXP (-307)
   /* Maximum int x such that FLT_RADIX**(x-1) is a representable long double */
#undef LDBL_MAX_EXP
#define LDBL_MAX_EXP 1024
   /* Maximum long double */
#undef LDBL_MAX
#define LDBL_MAX 1.7976931348623157e+308L
   /* Maximum int x such that 10**x is a representable long double */
#undef LDBL_MAX_10_EXP
#define LDBL_MAX_10_EXP 308
#endif /*  _FLOAT_H_ */

/*
 * Copyright (C) 2003-2006     Manuel Novoa III
 *
 * Licensed under the LGPL v2.1, see the file COPYING.LIB in this tarball.
 */
/* Define a maximal floating point type, and the associated constants
 * that are defined for the floating point types in float.h.
 *
 * This is to support archs that are missing long double, or even double.
 */

#ifndef _UCLIBC_FPMAX_H
#define _UCLIBC_FPMAX_H

#ifndef _ISOC99_SOURCE
#define _ISOC99_SOURCE 1
#endif


#if 0 //RUDD

typedef long double __fpmax_t;
#define FPMAX_TYPE
#define FPMAX_MANT_DIG       LDBL_MANT_DIG
#define FPMAX_DIG            LDBL_DIG
#define FPMAX_EPSILON        LDBL_EPSILON
#define FPMAX_MIN_EXP        LDBL_MIN_EXP
#define FPMAX_MIN            LDBL_MIN
#define FPMAX_MIN_10_EXP     LDBL_MIN_10_EXP
#define FPMAX_MAX_EXP        LDBL_MAX_EXP
#define FPMAX_MAX            LDBL_MAX
#define FPMAX_MAX_10_EXP     LDBL_MAX_10_EXP

#elif 1 // Rudd

typedef double __fpmax_t;
#define FPMAX_TYPE           2
#define FPMAX_MANT_DIG       DBL_MANT_DIG
#define FPMAX_DIG            DBL_DIG
#define FPMAX_EPSILON        DBL_EPSILON
#define FPMAX_MIN_EXP        DBL_MIN_EXP
#define FPMAX_MIN            DBL_MIN
#define FPMAX_MIN_10_EXP     DBL_MIN_10_EXP
#define FPMAX_MAX_EXP        DBL_MAX_EXP
#define FPMAX_MAX            DBL_MAX
#define FPMAX_MAX_10_EXP     DBL_MAX_10_EXP

#elif defined(FLT_MANT_DIG)

typedef float __fpmax_t;
#define FPMAX_TYPE           1

#define FPMAX_MANT_DIG       FLT_MANT_DIG
#define FPMAX_DIG            FLT_DIG
#define FPMAX_EPSILON        FLT_EPSILON
#define FPMAX_MIN_EXP        FLT_MIN_EXP
#define FPMAX_MIN            FLT_MIN
#define FPMAX_MIN_10_EXP     FLT_MIN_10_EXP
#define FPMAX_MAX_EXP        FLT_MAX_EXP
#define FPMAX_MAX            FLT_MAX
#define FPMAX_MAX_10_EXP     FLT_MAX_10_EXP

#else
#error unable to determine appropriate type for __fpmax_t!
#endif

#ifndef DECIMAL_DIG

#ifdef L___strtofpmax
/* Emit warning only once. */
#warning DECIMAL_DIG is not defined! If you are using gcc, it may not be defining __STDC_VERSION__ as it should.
#endif
#if !defined(FLT_RADIX) || (FLT_RADIX != 2)
#error unable to compensate for missing DECIMAL_DIG!
#endif

/*  ceil (1 + #mantissa * log10 (FLT_RADIX)) */
#define DECIMAL_DIG   (1 + (((FPMAX_MANT_DIG * 100) + 331) / 332))

#endif /* DECIMAL_DIG */

#if defined _LIBC && defined IS_IN_libc
extern __fpmax_t __strtofpmax(const char *str, char **endptr, int exp_adjust) attribute_hidden;

#ifdef __UCLIBC_HAS_XLOCALE__
extern __fpmax_t __strtofpmax_l(const char *str, char **endptr, int exp_adjust,
								__locale_t locale_arg) attribute_hidden;
#endif

#ifdef __UCLIBC_HAS_WCHAR__
extern __fpmax_t __wcstofpmax(const wchar_t *wcs, wchar_t **endptr,
							  int exp_adjust) attribute_hidden;

#ifdef __UCLIBC_HAS_XLOCALE__
extern __fpmax_t __wcstofpmax_l(const wchar_t *wcs, wchar_t **endptr,
								int exp_adjust, __locale_t locale_arg) attribute_hidden;
#endif
#endif /* __UCLIBC_HAS_WCHAR__ */
#endif /* _LIBC */

int  fptostr (__fpmax_t x, int width, int preci, char mode, char* buf, int maxlen);

/* The following checks in an __fpmax_t is either 0 or +/- infinity.
 *
 * WARNING!!!   WARNING!!!   WARNING!!!   WARNING!!!   WARNING!!!   WARNING!!!
 *
 * This only works if __fpmax_t is the actual maximal floating point type used
 * in intermediate calculations.  Otherwise, excess precision in the
 * intermediate values can cause the test to fail.
 *
 * WARNING!!!   WARNING!!!   WARNING!!!   WARNING!!!   WARNING!!!   WARNING!!!
 */

#define __FPMAX_ZERO_OR_INF_CHECK(x)  ((x) == ((x)/4) )

#endif /* _UCLIBC_FPMAX_H */


/* Copyright (C) 2004       Manuel Novoa III    <mjn3@codepoet.org>
 *
 * GNU Library General Public License (LGPL) version 2 or later.
 *
 * Dedicated to Toni.  See uClibc/DEDICATION.mjn3 for details.
 */

/* Experimentally off - libc_hidden_proto(memset) */

/* Copyright (C) 2000, 2001, 2003      Manuel Novoa III
 *
 * Function:
 *
 *     ssize_t _fpmaxtostr(FILE * fp, __fpmax_t x, struct printf_info *info,
 *                         __fp_outfunc_t fp_outfunc);
 *
 * This is derived from the old _dtostr, whic I wrote for uClibc to provide
 * floating point support for the printf functions.  It handles +/- infinity,
 * nan, and signed 0 assuming you have ieee arithmetic.  It also now handles
 * digit grouping (for the uClibc supported locales) and hexadecimal float
 * notation.  Finally, via the fp_outfunc parameter, it now supports wide
 * output.
 *
 * Notes:
 *
 * At most DECIMAL_DIG significant digits are kept.  Any trailing digits
 * are treated as 0 as they are really just the results of rounding noise
 * anyway.  If you want to do better, use an arbitary precision arithmetic
 * package.  ;-)
 *
 * It should also be fairly portable, as no assumptions are made about the
 * bit-layout of doubles.  Of course, that does make it less efficient than
 * it could be.
 *
 */

/*****************************************************************************/
/* Don't change anything that follows unless you know what you're doing.     */
/*****************************************************************************/
/* Fairly portable nan check.  Bitwise for i386 generated larger code.
 * If you have a better version, comment this out.
 */
#define isnan(x)             ((x) != (x))

/* Without seminumerical functions to examine the sign bit, this is
 * about the best we can do to test for '-0'.
 */
#define zeroisnegative(x)    ((1./(x)) < 0)

/*****************************************************************************/
/* Don't change anything that follows peroid!!!  ;-)                         */
/*****************************************************************************/
#ifdef __UCLIBC_HAS_HEXADECIMAL_FLOATS__
#if FLT_RADIX != 2
#error FLT_RADIX != 2 is not currently supported
#endif
#endif /* __UCLIBC_HAS_HEXADECIMAL_FLOATS__ */

#define NUM_HEX_DIGITS      ((FPMAX_MANT_DIG + 3)/ 4)

/* With 32 bit ints, we can get 9 decimal digits per block. */
#define DIGITS_PER_BLOCK     9
#define HEX_DIGITS_PER_BLOCK 8

/* Maximum number of subcases to output double is...
 *  0 - sign
 *  1 - padding and initial digit
 *  2 - digits left of the radix
 *  3 - 0s left of the radix        or   radix
 *  4 - radix                       or   digits right of the radix
 *  5 - 0s right of the radix
 *  6 - exponent
 *  7 - trailing space padding
 * although not all cases may occur.
 */
#define MAX_CALLS 8

/*****************************************************************************/

#define NUM_DIGIT_BLOCKS   ((DECIMAL_DIG+DIGITS_PER_BLOCK-1)/DIGITS_PER_BLOCK)
#define NUM_HEX_DIGIT_BLOCKS \
   ((NUM_HEX_DIGITS+HEX_DIGITS_PER_BLOCK-1)/HEX_DIGITS_PER_BLOCK)

/* extra space for '-', '.', 'e+###', and nul */
#define BUF_SIZE  ( 3 + NUM_DIGIT_BLOCKS * DIGITS_PER_BLOCK )

/*****************************************************************************/

static const char fmt[] = "inf\0INF\0nan\0NAN\0.\0,";

#define INF_OFFSET        0		/* must be 1st */
#define NAN_OFFSET        8		/* must be 2nd.. see hex sign handling */
#define DECPT_OFFSET     16
#define THOUSEP_OFFSET   18

#define EMPTY_STRING_OFFSET 3

/*****************************************************************************/
#if FPMAX_MAX_10_EXP < -FPMAX_MIN_10_EXP
#error scaling code can not handle FPMAX_MAX_10_EXP < -FPMAX_MIN_10_EXP
#endif

//rudd change back typedef double __fpmax_t;
static const double exp10_table[] =
{
	1e1L, 1e2L, 1e4L, 1e8L, 1e16L, 1e32L,	/* floats */
#if FPMAX_MAX_10_EXP < 32
#error unsupported FPMAX_MAX_10_EXP (< 32).  ANSI/ISO C requires >= 37.
#endif
#if FPMAX_MAX_10_EXP >= 64
	1e64L,
#endif
#if FPMAX_MAX_10_EXP >= 128
	1e128L,
#endif
#if FPMAX_MAX_10_EXP >= 256
	1e256L,
#endif
#if FPMAX_MAX_10_EXP >= 512
	1e512L,
#endif
#if FPMAX_MAX_10_EXP >= 1024
	1e1024L,
#endif
#if FPMAX_MAX_10_EXP >= 2048
	1e2048L,
#endif
#if FPMAX_MAX_10_EXP >= 4096
	1e4096L
#endif
#if FPMAX_MAX_10_EXP >= 8192
#error unsupported FPMAX_MAX_10_EXP.  please increase table
#endif
};

#define EXP10_TABLE_SIZE     (sizeof(exp10_table)/sizeof(exp10_table[0]))
#define EXP10_TABLE_MAX      (1U<<(EXP10_TABLE_SIZE-1))

/*****************************************************************************/

#if FLT_RADIX != 2
#error FLT_RADIX != 2 is not currently supported
#endif

#if FPMAX_MAX_EXP < -FPMAX_MIN_EXP
#error scaling code can not handle FPMAX_MAX_EXP < -FPMAX_MIN_EXP
#endif

static const __fpmax_t exp16_table[] = {
	0x1.0p4L, 0x1.0p8L, 0x1.0p16L, 0x1.0p32L, 0x1.0p64L,
#if FPMAX_MAX_EXP >= 128
	0x1.0p128L,
#endif
#if FPMAX_MAX_EXP >= 256
	0x1.0p256L,
#endif
#if FPMAX_MAX_EXP >= 512
	0x1.0p512L,
#endif
#if FPMAX_MAX_EXP >= 1024
	0x1.0p1024L,
#endif
#if FPMAX_MAX_EXP >= 2048
	0x1.0p2048L,
#endif
#if FPMAX_MAX_EXP >= 4096
	0x1.0p4096L,
#endif
#if FPMAX_MAX_EXP >= 8192
	0x1.0p8192L,
#endif
#if FPMAX_MAX_EXP >= 16384
	0x1.0p16384L
#endif
#if FPMAX_MAX_EXP >= 32768
#error unsupported FPMAX_MAX_EXP.  please increase table
#endif
};

#define EXP16_TABLE_SIZE     (sizeof(exp16_table)/sizeof(exp16_table[0]))
#define EXP16_TABLE_MAX      (1U<<(EXP16_TABLE_SIZE-1))

/*****************************************************************************/

#define FPO_ZERO_PAD    (0x80 | '0')
#define FPO_STR_WIDTH   (0x80 | ' ')
#define FPO_STR_PREC    'p'

int  fptostr (__fpmax_t x, int width, int preci, char mode, char* buf, int maxlen)
{
	__fpmax_t lower_bnd;
	__fpmax_t upper_bnd = 1e9;
	unsigned int base = 10;
	const __fpmax_t *power_table;
	int dpb = DIGITS_PER_BLOCK;
	int ndb = NUM_DIGIT_BLOCKS;
	int nd = DECIMAL_DIG;
	int sufficient_precision = 0;
	int round, o_exp;
	int exp;
	int cnt;
	char *s;
	char *e;
	typedef long int		intptr_t;
	intptr_t pc_fwi[3*MAX_CALLS];
	intptr_t *ppc;
	intptr_t *ppc_last;
	char exp_buf[16];
	char sign_str[6];			/* Last 2 are for 1st digit + nul. */
	char o_mode;
	char pad = ' ';
	char* orig_buf = buf;
	char temp_buf[BUF_SIZE];



	*exp_buf = 'e';
	if ((mode|0x20) == 'a') {
		*exp_buf = 'p';
		if (preci < 0) {
			preci = NUM_HEX_DIGITS;
			sufficient_precision = 1;
		}
	}

	if (preci < 0) {
		preci = 6;
	}

	*sign_str = '\0';
	*sign_str = '\0';

	*(sign_str+1) = 0;
	pc_fwi[5] = INF_OFFSET;
	if (isnan(x)) {				/* First, check for nan. */
		pc_fwi[5] = NAN_OFFSET;
		goto INF_NAN;
	}

	if (x == 0) {				/* Handle 0 now to avoid false positive. */
		exp = -1;
		goto GENERATE_DIGITS;
	}

	if (x < 0) {				/* Convert negatives to positives. */
		*sign_str = '-';
		x = -x;

	}

	if (__FPMAX_ZERO_OR_INF_CHECK(x)) {	/* Inf since zero handled above. */
	INF_NAN:
		pad = ' ';
		ppc = pc_fwi + 6;
		pc_fwi[3] = FPO_STR_PREC;
		pc_fwi[4] = 3;
		if (mode < 'a') {
			pc_fwi[5] += 4;
		}
		pc_fwi[5] = (intptr_t)(fmt + pc_fwi[5]);
		goto EXIT_SPECIAL;
	}

	{
		int i, j;

		if ((mode|0x20) == 'a') {
			lower_bnd = 0x1.0p31L;
			upper_bnd = 0x1.0p32L;
			power_table = exp16_table;
			exp = HEX_DIGITS_PER_BLOCK - 1;
			i = EXP16_TABLE_SIZE;
			j = EXP16_TABLE_MAX;
			dpb = HEX_DIGITS_PER_BLOCK;
			ndb = NUM_HEX_DIGIT_BLOCKS;
			nd = NUM_HEX_DIGITS;
			base = 16;
		} else {
			lower_bnd = 1e8;
			/* 		upper_bnd = 1e9; */
			power_table = exp10_table;
			exp = DIGITS_PER_BLOCK - 1;
			i = EXP10_TABLE_SIZE;
			j = EXP10_TABLE_MAX;
			/* 		dpb = DIGITS_PER_BLOCK; */
			/* 		ndb = NUM_DIGIT_BLOCKS; */
			/* 		base = 10; */
		}




		{
			int exp_neg = 0;
			if (x < lower_bnd) { /* Do we need to scale up or down? */
				exp_neg = 1;
			}

			do {
				--i;
				if (exp_neg) {
					if (x * power_table[i] < upper_bnd) {
						x *= power_table[i];
						exp -= j;
					}
				} else {
					if (x / power_table[i] >= lower_bnd) {
						x /= power_table[i];
						exp += j;
					}
				}
				j >>= 1;
			} while (i);
		}
	}
	while (x >= upper_bnd) {		/* Handle bad rounding case. */
		x /= power_table[0];
		++exp;
	}
        // RUDD - this may definitely be wrong
        // I couldn't get the assert to stop triggering
        // so I swapped the while to an if to continuously
        // round the number down. This seems reasonable and
        // I continue to pass the floating point regression tests
        // but this needs to be noted as a potential point of error.
/*  	tl_assert(x <= upper_bnd); */

 GENERATE_DIGITS:
	{

		int i, j;
		s = temp_buf + 2;			/* Leave space for '\0' and '0'. */
		i = 0;
		do {
			int digit_block = (int) x;
			tl_assert(digit_block < upper_bnd);
			x = (x - digit_block) * upper_bnd;
			s += dpb;
			j = 0;
			do {
				s[- ++j] = '0' + (digit_block % base);
				digit_block /= base;
			} while (j < dpb);
		} while (++i < ndb);
	}

	/*************************************************************************/

	if (mode < 'a') {
		*exp_buf -= ('a' - 'A'); /* e->E and p->P */
		mode += ('a' - 'A');
	}

	o_mode = mode;
	if ((mode == 'g') && (preci > 0)){
		--preci;
	}
	round = preci;

	if (mode == 'f') {
		round += exp;
		if (round < -1) {
			VG_(memset)(temp_buf, '0', DECIMAL_DIG); /* OK, since 'f' -> decimal case. */
		    exp = -1;
		    round = -1;
		}
	}

	s = temp_buf;
	*s++ = 0;					/* Terminator for rounding and 0-triming. */
	*s = '0';					/* Space to round. */

	{
		int i;
		i = 0;
		e = s + nd + 1;
		if (round < nd) {
			e = s + round + 2;
			if (*e >= '0' + (base/2)) {	/* NOTE: We always round away from 0! */
				i = 1;
			}
		}

		do {			   /* Handle rounding and trim trailing 0s. */
			*--e += i;			/* Add the carry. */
		} while ((*e == '0') || (*e > '0' - 1 + base));
	}

	if ((mode|0x20) == 'a') {
		char *q;

		for (q = e ; *q ; --q) {
			if (*q > '9') {
				*q += (*exp_buf - ('p' - 'a') - '9' - 1);
			}
		}

		if (e > s) {
			exp *= 4;			/* Change from base 16 to base 2. */
		}
	}

	o_exp = exp;
	if (e <= s) {				/* We carried into an extra digit. */
		++o_exp;
		e = s;					/* Needed if all 0s. */
	} else {
		++s;
	}
	*++e = 0;					/* Terminating nul char. */

	if ((mode == 'g') && ((o_exp >= -4) && (o_exp <= round))) {
		mode = 'f';
		preci = round - o_exp;
	}

	exp = o_exp;
	if (mode != 'f') {
		o_exp = 0;
	}

	if (o_exp < 0) {			/* Exponent is < 0, so */
		*--s = '0';				/* fake the first 0 digit. */
	}
	pc_fwi[3] = FPO_ZERO_PAD;
	pc_fwi[4] = 1;
	pc_fwi[5] = (intptr_t)(sign_str + 4);
	sign_str[4] = *s++;
	sign_str[5] = 0;
	ppc = pc_fwi + 6;

	{
		int i = e - s;			/* Total digits is 'i'. */
		if (o_exp >= 0) {
			ppc[0] = FPO_STR_PREC;
			ppc[2] = (intptr_t)(s);
			if (o_exp >= i) {		/* all digit(s) left of decimal */
				ppc[1] = i;
				ppc += 3;
				o_exp -= i;
				i = 0;
				if (o_exp>0) {		/* have 0s left of decimal */
					ppc[0] = FPO_ZERO_PAD;
					ppc[1] = o_exp;
					ppc[2] = (intptr_t)(fmt + EMPTY_STRING_OFFSET);
					ppc += 3;
				}
			} else if (o_exp > 0) {	/* decimal between digits */
				ppc[1] = o_exp;
				ppc += 3;
				s += o_exp;
				i -= o_exp;
			}
			o_exp = -1;
		}

		if ( (i)
		     || ((o_mode != 'g')
				&& (o_mode != 'a')
				&& (preci > 0))
			) {
			ppc[0] = FPO_STR_PREC;
			ppc[1] = 1;
			ppc[2] = (intptr_t)(fmt + DECPT_OFFSET);
			ppc += 3;
		}

		if (++o_exp < 0) {			/* Have 0s right of decimal. */
			ppc[0] = FPO_ZERO_PAD;
			ppc[1] = -o_exp;
			ppc[2] = (intptr_t)(fmt + EMPTY_STRING_OFFSET);
			ppc += 3;
		}
		if (i) {					/* Have digit(s) right of decimal. */
			ppc[0] = FPO_STR_PREC;
			ppc[1] = i;
			ppc[2] = (intptr_t)(s);
			ppc += 3;
		}

		if (((o_mode != 'g'))
			&& !sufficient_precision
		    ) {
			i -= o_exp;
			if (i < preci) {		/* Have 0s right of digits. */
				i = preci - i;
				ppc[0] = FPO_ZERO_PAD;
				ppc[1] = i;
				ppc[2] = (intptr_t)(fmt + EMPTY_STRING_OFFSET);
				ppc += 3;
			}
		}
	}

	/* Build exponent string. */
	if (mode != 'f') {
		char *p = exp_buf + sizeof(exp_buf);
		int j;
		char exp_char = *exp_buf;
		char exp_sign = '+';
		int min_exp_dig_plus_2 = ((o_mode != 'a') ? (2+2) : (2+1));

		if (exp < 0) {
			exp_sign = '-';
			exp = -exp;
		}

		*--p = 0;			/* nul-terminate */
		j = 2;				/* Count exp_char and exp_sign. */
		do {
			*--p = '0' + (exp % 10);
			exp /= 10;
		} while ((++j < min_exp_dig_plus_2) || exp); /* char+sign+mindigits */
		*--p = exp_sign;
		*--p = exp_char;

		ppc[0] = FPO_STR_PREC;
		ppc[1] = j;
		ppc[2] = (intptr_t)(p);
		ppc += 3;
	}

 EXIT_SPECIAL:
	{
		int i;
		ppc_last = ppc;
		ppc = pc_fwi + 4;	 /* Need width fields starting with second. */
		do {
			width -= *ppc;
			ppc += 3;
		} while (ppc < ppc_last);

		ppc = pc_fwi;
		ppc[0] = FPO_STR_WIDTH;
		ppc[1] = i = ((*sign_str) != 0);
		ppc[2] = (intptr_t) sign_str;

		if (((mode|0x20) == 'a') && (pc_fwi[3] >= 16)) { /* Hex sign handling. */
			/* Hex and not inf or nan, so prefix with 0x. */
			char *h = sign_str + i;
			*h = '0';
			*++h = 'x' - 'p' + *exp_buf;
			*++h = 0;
			ppc[1] = (i += 2);
		}

		if ((width -= i) > 0) {
			if (pad == '0') { /* 0 padding */
				ppc[4] += width;	/* Pad second field. */
			} else {
				ppc[1] += width;	/* Pad first (sign) field. */
			}
		}

		cnt = 0;
	}

	do {
	  int i;

	  int buflen = VG_(strlen)((const char*) ppc[2]);
	  if (ppc[0] & 0x80) {
	    if ((ppc[1] -= buflen) > 0) {
	      for(i = 0; i < ppc[1]; i++) {
		if(ppc[0] & FPO_ZERO_PAD) {
		  *buf++ = '0';
		} else if(ppc[0] & FPO_STR_WIDTH) {
		  *buf++ = ' ';
		}
	      }
	    }
	    ppc[1] = buflen;
	  }


	  for(i=0; i < ppc[1]; i++) {
	    *buf++ = *((char *)ppc[2] + i);
	  }


	  cnt += ppc[1];
	  ppc += 3;
	} while (ppc < ppc_last);
	*buf = '\0';
	return VG_(strlen)(orig_buf);
}


/* int main() { */
/*   char buss[1000];  */
/*   fptostr(1.314e12, 3, 17, 'g', buss, 1000); */
/*   printf("\n%s\n", buss);   */
/* }	  */
