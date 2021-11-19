typedef struct {
  int x;
  int y;
} point;

typedef struct {
  point f;
  point s;
} line_segment;

point compute_delta(line_segment ls) {
  point np = {ls.f.x - ls.s.x, ls.f.y - ls.s.y};
  return np;
}

int main() {
  point x = {1, 2};
  point y = {3, 4};
  line_segment l = {x, y};

  return compute_delta(l).x;
}
