#include <stdio.h>

typedef struct {
  void (*print)(char *);
} Printer;

void printToConsole(char *message) { printf("Console: %s\n", message); }
void printToRemote(char *message) { printf("Remote: %s\n", message); }

int main() {
  Printer consolePrinter = {.print = printToConsole};
  consolePrinter.print("Hello, world!");

  Printer remotePrinter = {.print = printToRemote};
  remotePrinter.print("Hello, everybody!");

  Printer *ref = &remotePrinter;
  ref->print("Hej");

  return 0;
}
