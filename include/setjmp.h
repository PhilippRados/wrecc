/*
 * Wrecc implementation of standard C header-file as defined by:
 * C99 standard (7.13)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _SETJMP_H_
#define _SETJMP_H_

#define _JBLEN ((9 * 2) + 3 + 16)
typedef int jmp_buf[_JBLEN];

int setjmp(jmp_buf);
void longjmp(jmp_buf, int);

#endif
