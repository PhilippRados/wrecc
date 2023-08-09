typedef char *FILE;
typedef long fpos_t;
typedef long size_t;

// void clearerr(FILE *);
// int fclose(FILE *);
// int feof(FILE *);
// int ferror(FILE *);
// int fflush(FILE *);
// int fgetc(FILE *);
// int fgetpos(FILE *__restrict, fpos_t *);
// char *fgets(char *__restrict, int, FILE *);
// FILE *fopen(char *filename, char *mode);

// int fprintf(FILE *__restrict, const char *__restrict, ...);
// int fputc(int, FILE *);
// int fputs(const char *__restrict, FILE *__restrict);
// size_t fread(void *__restrict __ptr, size_t __size, size_t __nitems,
//              FILE *__restrict __stream);
// FILE *freopen(const char *__restrict, const char *__restrict, FILE
// *__restrict); int fscanf(FILE *__restrict, const char *__restrict, ...); int
// fseek(FILE *, long, int); int fsetpos(FILE *, const fpos_t *); long
// ftell(FILE *); size_t fwrite(const void *__restrict __ptr, size_t __size,
// size_t __nitems,
//               FILE *__restrict __stream);
// int getc(FILE *);
// int getchar(void);
// char *gets(char *);
// void perror(const char *);
int printf(char *s, ...);
int putc(int c, FILE *f);
// int putchar(int);
// int puts(const char *);
// int remove(const char *);
// int rename(const char *__old, const char *__new);
// void rewind(FILE *);
// int scanf(const char *__restrict, ...);
// void setbuf(FILE *__restrict, char *__restrict);
// int setvbuf(FILE *__restrict, char *__restrict, int, size_t);
// int sprintf(char *__restrict, const char *__restrict, ...);
// int sscanf(const char *__restrict, const char *__restrict, ...);
// FILE *tmpfile(void);

// char *tmpnam(char *);
// int ungetc(int, FILE *);
// // int vfprintf(FILE *__restrict, const char *__restrict, va_list);
// // int vprintf(const char *__restrict, va_list);
// // int vsprintf(char *__restrict, const char *__restrict, va_list);

// FILE *fdopen(int, const char *);

// int fileno(FILE *);

// int pclose(FILE *);

// FILE *popen(const char *, const char *);
