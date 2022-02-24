
// So the test here is if we add the additional constraint (only on in params),
// the out param types should be correct but no info should flow between c1 and
// c2
int* caller1(int* in) { return alias_id(in); }
char** caller2(char** in) { return alias_id(in); }

void* alias_id(void* p1) {
  void* out = id(p1);
  (void)out;
  return out;
}
void* id(void* p1) { return p1; }