/*
 * Wrecc implementation of standard C header-file as defined by:
 * C99 standard (7.5)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _ERRNO_H_
#define _ERRNO_H_

int *__error(void);
#define errno (*__error())

// standard constants
#define EDOM 33
#define ERANGE 34

// INFO: EILSEQ is platform dependant

// base posix constants
#define EPERM 1    /* Operation not permitted */
#define ENOENT 2   /* No such file or directory */
#define ESRCH 3    /* No such process */
#define EINTR 4    /* Interrupted system call */
#define EIO 5      /* Input/output error */
#define ENXIO 6    /* Device not configured */
#define E2BIG 7    /* Argument list too long */
#define ENOEXEC 8  /* Exec format error */
#define EBADF 9    /* Bad file descriptor */
#define ECHILD 10  /* No child processes */
#define EDEADLK 11 /* Resource deadlock avoided */
#define ENOMEM 12  /* Cannot allocate memory */
#define EACCES 13  /* Permission denied */
#define EFAULT 14  /* Bad address */
#define EBUSY 16   /* Device / Resource busy */
#define EEXIST 17  /* File exists */
#define EXDEV 18   /* Cross-device link */
#define ENODEV 19  /* Operation not supported by device */
#define ENOTDIR 20 /* Not a directory */
#define EISDIR 21  /* Is a directory */
#define EINVAL 22  /* Invalid argument */
#define ENFILE 23  /* Too many open files in system */
#define EMFILE 24  /* Too many open files */
#define ENOTTY 25  /* Inappropriate ioctl for device */
#define ETXTBSY 26 /* Text file busy */
#define EFBIG 27   /* File too large */
#define ENOSPC 28  /* No space left on device */
#define ESPIPE 29  /* Illegal seek */
#define EROFS 30   /* Read-only file system */
#define EMLINK 31  /* Too many links */
#define EPIPE 32   /* Broken pipe */

#endif
