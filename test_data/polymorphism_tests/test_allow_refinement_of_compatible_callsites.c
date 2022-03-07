#include <stdlib.h>

struct partially_accessed {
  size_t f1;
  size_t f2;
};

// So the point here is field_access1 is polymorphic and can admit any structure
// with a size_t field at offset 0. field_access2 can admit any structure that
// has a field at offset 8 of size_t. caller1 and caller2 delegate to these and
// so should have similar polymorphic types. Finally, destructure calles both
// caller1 and caller2, revealing the complete structure. Heuristics should
// realize that the callsite caller1, caller2, fieldaccess1, fieldaccess2 are
// all compatible meaning we can instantiate a single type.


// so a more precise thing to think about here re 

size_t __attribute__((noinline)) field_access1(struct partially_accessed* in) {
  return in->f1;
}

size_t __attribute__((noinline)) field_access2(struct partially_accessed* in) {
  return in->f2;
}

size_t __attribute__((noinline)) caller1(struct partially_accessed* in) {
  return field_access1(in);
}

size_t __attribute__((noinline)) caller2(struct partially_accessed* in) {
  return field_access2(in);
}

size_t destructure(struct partially_accessed* in) {
  size_t f1 = caller1(in);
  size_t f2 = caller2(in);
  return f1 + f2;
}
