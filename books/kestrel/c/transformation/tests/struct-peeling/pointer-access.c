// Pointer member access (memberp operator)
// Split Node into data (value) and metadata (id, flags)

struct Node {
  int id;
  int value;
  int flags;
};

int main(void) {
  struct Node n;
  struct Node *ptr = &n;

  ptr->id = 42;
  ptr->value = 100;
  ptr->flags = 0xFF;

  int result = ptr->id + ptr->value;

  return result;
}
