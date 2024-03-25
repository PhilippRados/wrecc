/*
 * Wrecc implementation of standard C header-file as defined by:
 * C99 standard (7.18)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _STDINT_H_
#define _STDINT_H_

// INFO: missing unsigned and short because it's unimplemented
typedef char int8_t;
typedef int int32_t;
typedef long int64_t;

typedef int8_t int_least8_t;
typedef int32_t int_least32_t;
typedef int64_t int_least64_t;

typedef int8_t int_fast8_t;
typedef int32_t int_fast32_t;
typedef int64_t int_fast64_t;

typedef long intmax_t;
typedef long intptr_t;

#define INT8_MAX 127
#define INT32_MAX 2147483647
#define INT64_MAX 9223372036854775807

#define INT8_MIN -128
#define INT32_MIN (-INT32_MAX - 1)
#define INT64_MIN (-INT64_MAX - 1)

#define INT_LEAST8_MIN INT8_MIN
#define INT_LEAST32_MIN INT32_MIN
#define INT_LEAST64_MIN INT64_MIN

#define INT_LEAST8_MAX INT8_MAX
#define INT_LEAST32_MAX INT32_MAX
#define INT_LEAST64_MAX INT64_MAX

#define INT_FAST8_MIN INT8_MIN
#define INT_FAST32_MIN INT32_MIN
#define INT_FAST64_MIN INT64_MIN

#define INT_FAST8_MAX INT8_MAX
#define INT_FAST32_MAX INT32_MAX
#define INT_FAST64_MAX INT64_MAX

#define INTPTR_MAX 9223372036854775807
#define INTPTR_MIN (-INTPTR_MAX - 1)

#define INTMAX_MAX 9223372036854775807
#define INTMAX_MIN (-INTMAX_MAX - 1)

#endif
