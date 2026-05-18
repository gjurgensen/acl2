// struct Node {
//   int id;
//   int value;
//   int flags;
// };
struct Node {
  int value;
};
struct Node_0 {
  int id;
  int flags;
};

int main(void) {
  // struct Node n;
  // The unmotivated transformation of the declaration returns:
  // { effects = nil,
  //   split1 = `struct Node n`,
  //   split2 = `struct Node_0 n_0`,
  //   object_map = object_map ∪ `uid@n` ↦ `(uid@n, uid@n_0)`
  // }
  struct Node n;
  struct Node_0 n_0;

  // struct Node *ptr = &n;
  // The unmotivated transformation of the declaration returns:
  // { effects = nil,
  //   split1 = `struct Node *ptr = &n`,
  //   split2 = `struct Node *ptr_0 = &n_0`,
  //   object_map = object_map ∪ `uid@ptr` ↦ `(uid@ptr, uid@ptr_0)`
  // }
  struct Node *ptr = &n;
  struct Node *ptr_0 = &n_0;

  // The rest is straightforward.

  ptr_0->id = 42;
  ptr->value = 100;
  ptr_0->flags = 0xFF;

  int result = ptr_0->id + ptr->value;

  return result;
}
