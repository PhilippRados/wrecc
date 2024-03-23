#ifndef _SETJMP_H_
#define _SETJMP_H_

#define _JBLEN ((9 * 2) + 3 + 16)
typedef int jmp_buf[_JBLEN];

int setjmp(jmp_buf);
void longjmp(jmp_buf, int);

#endif
