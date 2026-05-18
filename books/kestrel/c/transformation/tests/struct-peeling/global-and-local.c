// Both global and local struct variables
// Split Config into network (ip, port) and system (threads, timeout)

struct Config {
  int ip;
  int port;
  int threads;
  int timeout;
};

static struct Config global_config = {
  .ip = 192168001,
  .port = 8080,
  .threads = 4,
  .timeout = 30
};

int main(void) {
  struct Config local_config;

  local_config.ip = 127001;
  local_config.port = 3000;
  local_config.threads = 2;
  local_config.timeout = 60;

  int global_sum = global_config.ip + global_config.threads;
  int local_sum = local_config.port + local_config.timeout;

  return global_sum + local_sum;
}
