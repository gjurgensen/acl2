// struct Pair {
//   int first;
//   int second;
// };
struct Pair {
  int first;
};
struct Pair_0 {
  int second;
};

int main(void) {
  // struct Pair p;
  // We see that the declared object has type `struct uid@Pair`. We therefore begin
  // unmotivated transformation, which creates two declarations.
  // We add `uid@p` ↦ `(uid@p, uid@p_0)`
  struct Pair p;
  struct Pair_0 p_0;

  // p.first = 10;
  // In the LHS expression of the simple assignment, we see that the struct type
  // is `struct uid@Pair`. We therefore perform a motivated transformation. In
  // this case, the transformation is the identity.
  p.first = 10;

  // p.second = 20;
  // We do as in the above, but in this case the member "second" gives us a
  // motivation of `struct uid@Pair_0` (instead of `struct uid@Pair`). So we end
  // up with `p_0` instead of `p`.
  p_0.second = 20;

  // return p.first + p.second;
  // We again do motivated transformation of the member expressions.
  // What "mode" are we in to begin with? Perhaps there is no mode (no
  // motivated/unmotivated distinction) at the statement level.
  return p.first + p_0.second;
}
