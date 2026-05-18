// Designated initializers with struct peeling
// Split Stats into counts (success, failure) and metrics (avg_time, max_time)

struct Stats {
  int success;
  int failure;
  int avg_time;
  int max_time;
};

int main(void) {
  struct Stats s1 = {
    .success = 100,
    .failure = 5,
    .avg_time = 250,
    .max_time = 1000
  };

  // Partial initialization
  struct Stats s2 = {
    .success = 50,
    .avg_time = 300
  };

  int total_requests = s1.success + s1.failure + s2.success + s2.failure;

  return total_requests;
}
