/*
 * Wrecc implementation of posix C header-file as defined by:
 */

#ifndef _FCNTL_H_
#define _FCNTL_H_

#define O_RDONLY 0
#define O_WRONLY 1
#define O_RDWR 2

typedef int mode_t;

int open(char *, int, ...);
int creat(char *, mode_t);
int fcntl(int, int, ...);

#endif
