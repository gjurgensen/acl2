// Function using position members (x, y)
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

int distance_squared_from_origin(struct Rectangle rect) {
  return rect.x * rect.x + rect.y * rect.y;
}

int distance_squared_to_center(struct Rectangle rect) {
  int center_x = rect.x + rect.width / 2;
  int center_y = rect.y + rect.height / 2;
  return center_x * center_x + center_y * center_y;
}

int main(void) {
  struct Rectangle r;
  r.x = 10;
  r.y = 20;
  r.width = 100;
  r.height = 50;

  int area = compute_area(r);
  int dist = distance_squared_from_origin(r);
  int center_dist = distance_squared_to_center(r);

  return area + dist + center_dist;
}
