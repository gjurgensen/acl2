// Nested structs (marked as potentially illegal in notes)
// This tests whether we can peel the inner struct

struct Inner {
  int a;
  int b;
  int c;
};

struct Outer {
  struct Inner inner;
  int x;
};

int main(void) {
  struct Outer out;

  out.inner.a = 1;
  out.inner.b = 2;
  out.inner.c = 3;
  out.x = 10;

  return out.inner.a + out.inner.b + out.x;
}
