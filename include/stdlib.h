#include <stddef.h>

typedef struct {
  int quot;
  int rem;
} div_t;

typedef struct {
  long quot;
  long rem;
} ldiv_t;

#define EXIT_FAILURE 1
#define EXIT_SUCCESS 0

#define RAND_MAX 2147483647

void abort(void);
void exit(int);

int system(char *);

char *getenv(char *);

int atoi(char *);
long atol(char *);
long strtol(char *, char **, int);

void *malloc(size_t);
void *calloc(size_t, size_t);
void free(void *);
void *realloc(void *, size_t);

int rand(void);
int abs(int);
long labs(long);
