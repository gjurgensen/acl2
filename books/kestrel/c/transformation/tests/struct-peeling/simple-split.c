// Simplest possible struct peeling test
// Split Pair into first and second

struct Pair {
  int first;
  int second;
};

int main(void) {
  struct Pair p;
  p.first = 10;
  p.second = 20;

  return p.first + p.second;
}
