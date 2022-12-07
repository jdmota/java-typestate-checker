import jatyc.lib.Typestate;

@Typestate("BaseAccount")
public class BaseAccount {

  protected int balance = 0;
  protected int money = 0;

  public void deposit(int amount) {
    balance += amount;
  }

  public boolean canWithdraw(int amount) {
    money = amount;
    return amount <= balance;
  }

  public void withdraw() {
    balance -= money;
  }
}
