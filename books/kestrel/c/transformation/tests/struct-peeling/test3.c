// Multiple instances of the same struct
// Split Sensor into readings (temp, humidity) and metadata (id, status)

struct Sensor {
  int id;
  int temp;
  int humidity;
  int status;
};

struct Sensor sensor1;
struct Sensor sensor2;

int main(void) {
  sensor1.id = 1;
  sensor1.temp = 72;
  sensor1.humidity = 45;
  sensor1.status = 1;

  sensor2.id = 2;
  sensor2.temp = 68;
  sensor2.humidity = 50;
  sensor2.status = 1;

  int avg_temp = (sensor1.temp + sensor2.temp) / 2;
  return avg_temp;
}
