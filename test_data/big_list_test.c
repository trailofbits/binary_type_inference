#include <stdlib.h>

struct LL {
  struct LL* next;
  int handle;
};

int close_last(struct LL* list) {
  while (list->next != NULL) {
    list = list->next;
  }
  return close(list->handle);
}

int top_level(struct LL* list1, struct LL* list2) {
  int res = close_last(list1);
  if (res >= 0) {
    return close_last(list2);
  }

  return res;
}
