/*
 * Wrecc implementation of standard C header-file as defined by:
 * C89 standard (7.3)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _CTYPE_H_
#define _CTYPE_H_

int isalnum(int);
int isalpha(int);
int iscntrl(int);
int islower(int);
int isupper(int);
int isdigit(int);
int isxdigit(int);
int isgraph(int);
int isspace(int);
int isprint(int);
int ispunct(int);

int tolower(int);
int toupper(int);

//
int isascii(int);
int toascii(int);

#endif
