#include <stdlib.h>

struct LL {
  size_t handle;
  struct LL* next;
};

void remove_target(struct LL** curr_target, struct LL* target) {
  while (*curr_target != target) {
    curr_target = &(*curr_target)->next;
  }
  *curr_target = target->next;
}