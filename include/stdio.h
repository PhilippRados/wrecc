#ifndef _STDIO_H_
#define _STDIO_H_

#include <stddef.h>

typedef char *FILE;
typedef long fpos_t;

#define stdin *FILE
#define stdout *FILE
#define stderr *FILE

#define _IOFBF 0
#define _IOLBF 1
#define _IONBF 2

#define BUFSIZ 1024
#define EOF (-1)

#define FOPEN_MAX 20
#define FILENAME_MAX 1024

#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2

#define TMP_MAX 308915776

#define L_tmpnam 1024

void clearerr(FILE *);
int fclose(FILE *);
int feof(FILE *);
int ferror(FILE *);
int fflush(FILE *);
int fgetc(FILE *);
int fgetpos(FILE *, fpos_t *);
char *fgets(char *, int, FILE *);
FILE *fopen(char *, char *);

int fprintf(FILE *, char *, ...);
int fputc(int, FILE *);
int fputs(char *, FILE *);
size_t fread(void *, size_t, size_t, FILE *);
FILE *freopen(char *, char *, FILE *);
int fscanf(FILE *, char *, ...);
int fseek(FILE *, long, int);
int fsetpos(FILE *, fpos_t *);
long ftell(FILE *);
size_t fwrite(void *, size_t, size_t, FILE *);
int getc(FILE *);
int getchar(void);
char *gets(char *);
void perror(char *);
int printf(char *, ...);
int putc(int, FILE *);
int putchar(int);
int puts(char *);
int remove(char *);
int rename(char *, char *);
void rewind(FILE *);
int scanf(char *, ...);
void setbuf(FILE *, char *);
int setvbuf(FILE *, char *, int, size_t);
int sprintf(char *, char *, ...);
int sscanf(char *, char *, ...);
FILE *tmpfile(void);

char *tmpnam(char *);
int ungetc(int, FILE *);

#endif
