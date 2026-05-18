// Basic struct peeling test
// Split Point struct into two: position (x,y) and color (r,g,b)

struct Point {
  int x;
  int y;
  int r;
  int g;
  int b;
};

int main(void) {
  struct Point p;
  p.x = 10;
  p.y = 20;
  p.r = 255;
  p.g = 128;
  p.b = 0;

  return p.x + p.y + p.r;
}
