/*
 * Wrecc implementation of standard C header-file as defined by:
 * C99 standard (7.8)
 * https://en.cppreference.com/w/c/header
 */

#include <stdint.h>

#ifndef _INTTYPES_H_
#define _INTTYPES_H_

typedef struct {
  intmax_t quot;
  intmax_t rem;
} imaxdiv_t;

imaxdiv_t imaxdiv(intmax_t, intmax_t);
intmax_t imaxabs(intmax_t);
intmax_t strtoimax(char *, char **, int);

#endif
