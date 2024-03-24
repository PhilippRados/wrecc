/*
 * Wrecc implementation of standard C header-file as defined by:
 * C89 standard (7.10)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _STDLIB_H_
#define _STDLIB_H_

#include <stddef.h>

typedef struct {
  int quot;
  int rem;
} div_t;

typedef struct {
  long quot;
  long rem;
} ldiv_t;

#define EXIT_FAILURE 1
#define EXIT_SUCCESS 0

#define RAND_MAX 2147483647

void abort(void);
void exit(int);
int atexit(void (*func)(void));

int system(char *);

char *getenv(char *);

int atoi(char *);
long atol(char *);
long strtol(char *, char **, int);

void *malloc(size_t);
void *calloc(size_t, size_t);
void free(void *);
void *realloc(void *, size_t);

int rand(void);
void srand(int);

int abs(int);
long labs(long);
div_t div(int, int);
ldiv_t ldiv(long, long);

void *bsearch(void *, void *, size_t, size_t, int (*compar)(void *, void *));
void qsort(void *, size_t, size_t, int (*compar)(void *, void *));

#endif
