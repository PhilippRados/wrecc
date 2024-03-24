#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

void sigint_handler(int signum) { printf("Caught SIGINT signal\n"); }
void sigabrt_handler(int signum) { printf("Caught SIGABRT signal\n"); }

int main() {
  if (signal(SIGINT, sigint_handler) == SIG_ERR) {
    printf("SIG_ERR");
    return 1;
  }

  if (signal(SIGABRT, sigabrt_handler) == SIG_ERR) {
    printf("SIG_ERR");
    return 1;
  }

  raise(SIGINT);

  return 0;
}
