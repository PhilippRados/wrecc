#ifndef _STRING_H_
#define _STRING_H_

#include <stddef.h>

void *memchr(void *, int, size_t);
int memcmp(void *, void *, size_t);
void *memcpy(void *, void *, size_t);
void *memmove(void *, void *, size_t);
void *memset(void *, int, size_t);
char *strcat(char *, char *);
char *strchr(char *, int);
int strcmp(char *, char *);
int strcoll(char *, char *);
char *strcpy(char *, char *);
size_t strcspn(char *, char *);
char *strerror(int);
size_t strlen(char *);
char *strncat(char *, char *, size_t);
int strncmp(char *, char *, size_t);
char *strncpy(char *, char *, size_t);
char *strpbrk(char *, char *);
char *strrchr(char *, int);
size_t strspn(char *, char *);
char *strstr(char *, char *);
char *strtok(char *, char *);
size_t strxfrm(char *, char *, size_t);

#endif
