import jatyc.lib.Typestate;
import jatyc.lib.Requires;

@Typestate("ProAccount")
public class ProAccount extends BaseAccount {

  private final int transferFee = 5;
  private final int proAccountFee = 2;

  public void deposit(int amount) {
    this.balance += amount - proAccountFee;
  }

  public boolean canWithdraw(int amount) {
    money = amount;
    return amount+proAccountFee <= balance;
  }

  public void withdraw() {
    balance -= proAccountFee + money;
  }

  public boolean canTransfer(int amount) {
    money = amount;
    return amount+transferFee <= balance;
  }

  public void transfer(@Requires({"Init", "Attempt"}) BaseAccount target) {
    target.deposit(money);
    balance -= transferFee + money;
  }
}
