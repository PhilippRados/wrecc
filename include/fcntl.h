#ifndef _FCNTL_H_
#define _FCNTL_H_

#define O_RDONLY 0
#define O_WRONLY 1
#define O_RDWR 2
#define O_ACCMODE 3

#define FREAD 1
#define FWRITE 2
#define O_NONBLOCK 4
#define O_APPEND 8

#define O_SHLOCK 16
#define O_EXLOCK 32
#define O_ASYNC 64
#define O_SYNC 128
#define O_FSYNC O_SYNC
#define O_NOFOLLOW 256
#define O_CREAT 512
#define O_TRUNC 1024
#define O_EXCL 2048

typedef int mode_t;

int open(char *, int, ...);
int creat(char *, mode_t);
int fcntl(int, int, ...);

#endif
