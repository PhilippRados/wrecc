/*
 * Wrecc implementation of standard C header-file as defined by:
 * C99 standard (5.2.4.2.1), adjusted for x8664
 * https://en.cppreference.com/w/c/header
 */

#ifndef _LIMITS_H_
#define _LIMITS_H_

#define CHAR_BIT 8

#define CHAR_MAX 127
#define SCHAR_MAX CHAR_MAX
#define CHAR_MIN (-128)
#define SCHAR_MIN CHAR_MIN

#define SHRT_MAX 32767
#define SHRT_MIN (-32768)

#define INT_MAX 2147483647
#define INT_MIN (-2147483647 - 1)

#define LONG_MAX 9223372036854775807
#define LONG_MIN (-9223372036854775807 - 1)

#define UCHAR_MAX (CHAR_MAX * 2 + 1)
#define USHRT_MAX (SHRT_MAX * 2 + 1)
#define UINT_MAX (INT_MAX * 2U + 1U)
#define ULONG_MAX (LONG_MAX * 2UL + 1UL)

#define LLONG_MAX LONG_MAX
#define LLONG_MIN LONG_MIN
#define ULLONG_MAX ULONG_MAX

#endif
