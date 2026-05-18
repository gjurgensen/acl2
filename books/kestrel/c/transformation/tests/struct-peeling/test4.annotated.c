// struct Rectangle {
//   int x;
//   int y;
//   int width;
//   int height;
// };
struct Position {
  int x;
  int y;
};
struct Dimensions {
  int width;
  int height;
};

// int compute_area(struct Rectangle rect) {
// The unmotivated xform of `struct Rectangle rect` produces:
// { effects = nil,
//   split1 = `struct Position pos`,
//   split2 = `struct Dimensions dim`,
//   object_map ∪= `uid@rect` ↦ `(uid@pos, uid@dim)`
// }
// Obviously, effects has to be nil here. It should always be (I think), but we
// should check it anyway and fail if non-nil.
// We shouldn't need to store any information about this change to
// `compute_area`. In future uses of the function, we can look up the type, see
// the struct argument, and act accordingly.
int compute_area(struct Position pos, struct Dimensions dim) {

  // return rect.width * rect.height;
  // Straightforward
  return dim.width * pos.height;

  // Note that a separate transformation could come and remove the pos
  // parameter.
}

// int compute_perimeter(struct Rectangle rect) {
//   return 2 * (rect.width + rect.height);
// }
// Same as above.
int compute_perimeter(struct Position pos, struct Dimensions dim) {
  return 2 * (dim.width + dim.height);
}

int main(void) {
  // struct Rectangle r;
  struct Position pos;
  struct Dimensions dim;

  // r.x = 10;
  // r.y = 20;
  // r.width = 100;
  // r.height = 50;
  pos.x = 10;
  pos.y = 20;
  dim.width = 100;
  dim.height = 50;

  // int area = compute_area(r);
  // int perim = compute_perimeter(r);
  int area = compute_area(pos, dim);
  int perim = compute_perimeter(pos, dim);

  return area + perim;
}
