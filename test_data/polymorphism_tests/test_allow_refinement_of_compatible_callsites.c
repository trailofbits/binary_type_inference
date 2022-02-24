#include <stdlib.h>

struct partially_accessed {
  size_t f1;
  size_t f2;
};

size_t caller1(struct partially_accessed in) { return field_access1(in); }

size_t caller2(struct partially_accessed in) { return field_access2(in); }

size_t field_access1(struct partially_accessed in) { return in.f1; }

size_t field_access2(struct partially_accessed in) { return in.f2; }