#include <stdio.h>
#include <stdlib.h>

struct LL {
  struct LL* next;
  int handle;
  char* name;
};

int print_name(struct LL* list) { return puts(list->name); }

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
  } else {
    print_name(list1);
  }

  return res;
}
