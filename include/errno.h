#ifndef _ERRNO_H_
#define _ERRNO_H_

int *__error(void);
#define errno (*__error())

#define EPERM 1
#define ENOENT 2
#define ESRCH 3
#define EINTR 4
#define EIO 5
#define ENXIO 6
#define E2BIG 7
#define ENOEXEC 8
#define EBADF 9
#define ECHILD 10
#define EDEADLK 11

#define ENOMEM 12
#define EACCES 13
#define EFAULT 14

#endif
