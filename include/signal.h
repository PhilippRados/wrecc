/*
 * Wrecc implementation of standard C header-file as defined by:
 * C89 standard (7.7)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _SIGNAL_H_
#define _SIGNAL_H_

#define SIG_DFL (void (*)(int))0
#define SIG_IGN (void (*)(int))1
#define SIG_ERR ((void (*)(int)) - 1)

#define SIGINT 2
#define SIGILL 4
#define SIGABRT 6
#define SIGFPE 8
#define SIGSEGV 11
#define SIGTERM 15

typedef int sig_atomic_t;

int raise(int);
void (*signal(int sig, void (*handler)(int)))(int);

#endif
