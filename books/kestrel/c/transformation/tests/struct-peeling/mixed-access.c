// Mixed access patterns to different fields
// Split Data into group A (a, b) and group B (c, d, e)

struct Data {
  int a;
  int b;
  int c;
  int d;
  int e;
};

int main(void) {
  struct Data data;

  // Initialize group A fields
  data.a = 1;
  data.b = 2;

  // Initialize group B fields
  data.c = 3;
  data.d = 4;
  data.e = 5;

  // Mixed access
  int sum_a = data.a + data.b;
  int sum_b = data.c + data.d + data.e;

  return sum_a * sum_b;
}
