// Struct peeling with initializers
// Split Person into personal data and statistics

struct Person {
  int id;
  int age;
  int salary;
  int years_employed;
};

static struct Person employee = {
  .id = 1001,
  .age = 35,
  .salary = 75000,
  .years_employed = 10
};

int main(void) {
  int total_cost = employee.salary * employee.years_employed;
  return employee.id + total_cost;
}
