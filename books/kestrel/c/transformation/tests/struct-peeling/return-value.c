// Function returning struct (complex case)
// Split Result into status (code, message_id) and data (value, timestamp)

struct Result {
  int code;
  int message_id;
  int value;
  int timestamp;
};

struct Result create_result(int val) {
  struct Result r;
  r.code = 200;
  r.message_id = 1;
  r.value = val;
  r.timestamp = 1234567890;
  return r;
}

int main(void) {
  struct Result res = create_result(42);

  if (res.code == 200) {
    return res.value;
  } else {
    return res.message_id;
  }
}
