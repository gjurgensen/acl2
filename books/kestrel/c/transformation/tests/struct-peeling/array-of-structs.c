// Array of structs (may be illegal per design notes)
// Split Pixel into position (x, y) and color (r, g, b, a)

struct Pixel {
  int x;
  int y;
  int r;
  int g;
  int b;
  int a;
};

int main(void) {
  struct Pixel pixels[3];

  pixels[0].x = 0;
  pixels[0].y = 0;
  pixels[0].r = 255;

  pixels[1].x = 1;
  pixels[1].y = 1;
  pixels[1].g = 255;

  pixels[2].x = 2;
  pixels[2].y = 2;
  pixels[2].b = 255;

  return pixels[0].r + pixels[1].g + pixels[2].b;
}
