import jatyc.lib.Typestate;

@Typestate("BaseAccount")
public class BaseAccount {

  protected int balance = 0;
  protected int toWithdraw = 0;

  public void login() {}

  public void deposit(int amount) {balance += amount;}

  public boolean canWithdraw(int amount) {
    toWithdraw = amount;
    return amount <= balance;
  }

  public void withdraw() {balance -= toWithdraw;}
}
