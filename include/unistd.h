#include <stddef.h>

typedef long ssize_t;
typedef long off_t;
typedef int pid_t;
typedef long gid_t;
typedef long uid_t;

void _exit(int);
int access(char *, int);
int alarm(int);
int chdir(char *);
int chown(char *, uid_t, gid_t);

int close(int);

int dup(int);
int dup2(int, int);
int execl(char *, char *, ...);
int execle(char *, char *, ...);
int execlp(char *, char *, ...);
int execv(char *, char **);
int execve(char *, char **, char **);
int execvp(char *, char **);
pid_t fork(void);
long fpathconf(int, int);
char *getcwd(char *, size_t);
gid_t getegid(void);
uid_t geteuid(void);
gid_t getgid(void);
int getgroups(int, gid_t[]);
char *getlogin(void);
pid_t getpgrp(void);
pid_t getpid(void);
pid_t getppid(void);
uid_t getuid(void);
int isatty(int);
int link(char *, char *);
off_t lseek(int, off_t, int);
long pathconf(char *, int);

int pause(void);

int pipe(int[2]);

ssize_t read(int, void *, size_t);

int rmdir(char *);
int setgid(gid_t);
int setpgid(pid_t, pid_t);
pid_t setsid(void);
int setuid(uid_t);

int sleep(int);

long sysconf(int);
pid_t tcgetpgrp(int);
int tcsetpgrp(int, pid_t);
char *ttyname(int);

int unlink(char *);

ssize_t write(int, void *, size_t);
