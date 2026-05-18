// Multiple functions using the struct
// Split Account into identity (id, account_num) and balance (current, available)

struct Account {
  int id;
  int account_num;
  int current;
  int available;
};

int get_id(struct Account acc) {
  return acc.id;
}

int get_balance(struct Account acc) {
  return acc.current;
}

void deposit(struct Account *acc, int amount) {
  acc->current = acc->current + amount;
  acc->available = acc->available + amount;
}

int main(void) {
  struct Account my_account;

  my_account.id = 1;
  my_account.account_num = 12345;
  my_account.current = 1000;
  my_account.available = 1000;

  deposit(&my_account, 500);

  int id = get_id(my_account);
  int balance = get_balance(my_account);

  return id + balance;
}
