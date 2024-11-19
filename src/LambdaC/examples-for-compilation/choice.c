#include <assert.h>
#include <stdbool.h>

typedef bool (*flip)(void);
typedef void (*fail)(void);

int choice(flip flip, fail fail, int n) {
  if (n < 1) {
    fail();
    return 0; // unreachable
  } else {
    if (flip()) {
      return n;
    }
    return choice(flip, fail, n - 1);
  }
}

bool flip_handler(void) { return rand() < 0.5; }

[[noreturn]] void fail_handler(void) { exit(0); }

int handledChoice(int n) { return choice(flip_handler, fail_handler, n); }
