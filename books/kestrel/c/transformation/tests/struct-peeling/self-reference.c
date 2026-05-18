// Self-referencing struct (marked as illegal in design notes)
// Split ListNode into data (value) and link (next)
// This is challenging because 'next' is a pointer to the same struct type

struct ListNode {
  int value;
  struct ListNode *next;
};

int main(void) {
  struct ListNode node1;
  struct ListNode node2;

  node1.value = 10;
  node1.next = &node2;

  node2.value = 20;
  node2.next = (struct ListNode *)0;

  return node1.value + node1.next->value;
}
