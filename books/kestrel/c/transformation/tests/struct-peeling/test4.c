// Function parameter with struct type
// Split Rectangle into dimensions (width, height) and position (x, y)

struct Rectangle {
  int x;
  int y;
  int width;
  int height;
};

int compute_area(struct Rectangle rect) {
  return rect.width * rect.height;
}

int compute_perimeter(struct Rectangle rect) {
  return 2 * (rect.width + rect.height);
}

int main(void) {
  struct Rectangle r;
  r.x = 10;
  r.y = 20;
  r.width = 100;
  r.height = 50;

  int area = compute_area(r);
  int perim = compute_perimeter(r);

  return area + perim;
}
