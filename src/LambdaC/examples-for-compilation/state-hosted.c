struct get_closure {
  int (*fun)(int *);
  int *env;
};

struct set_closure {
  void (*fun)(int *, int);
  int *env;
};

struct state {
  struct get_closure get;
  struct set_closure set;
};

int handle_get(int *env) { return *env; }

void handle_set(int *env, int val) { *env = val; }

int main(void) {
  int store = 0;
  struct state handler = {.get = (struct get_closure){handle_get, &store},
                          .set = (struct set_closure){handle_set, &store}};
  putstr(itoa(handler.get.fun(handler.get.env)));
  handler.set.fun(handler.set.env, handler.get.fun(handler.get.env) + 5);
  putstr(itoa(handler.get.fun(handler.get.env)));
}
