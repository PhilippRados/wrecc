/*
 * Wrecc implementation of standard C header-file as defined by:
 * C99 standard (7.23)
 * https://en.cppreference.com/w/c/header
 */

#ifndef _TIME_H_
#define _TIME_H_

#include <stddef.h>

#define CLOCKS_PER_SEC 1000000

typedef long time_t;
typedef long clock_t;
struct tm {
  int tm_sec;
  int tm_min;
  int tm_hour;
  int tm_mday;
  int tm_mon;
  int tm_year;
  int tm_wday;
  int tm_yday;
  int tm_isdst;
  long tm_gmtoff;
  char *tm_zone;
};

char *asctime(struct tm *);
clock_t clock(void);
char *ctime(time_t *);
struct tm *getdate(char *);
struct tm *gmtime(time_t *);
struct tm *localtime(time_t *);
time_t mktime(struct tm *);
size_t strftime(char *, size_t, char *, struct tm *);
char *strptime(char *, char *, struct tm *);
time_t time(time_t *);

#endif
