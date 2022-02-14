import jatyc.lib.Typestate;
import jatyc.lib.Requires;

@Typestate("ProAccount")
public class ProAccount extends BaseAccount {

  private final int transferFee = 5;
  private final int proAccountFee = 2;

  public void deposit(int amount) {this.balance += (amount - proAccountFee);}

  public boolean canWithdraw(int amount) {
    toWithdraw = amount + proAccountFee;
    return amount+proAccountFee <= balance;
  }

  public boolean canTransfer(int amount) {
    toWithdraw = amount + transferFee;
    return amount+transferFee <= balance;
  }

  public void transfer(@Requires("Init") BaseAccount receiver) {
    balance -= toWithdraw;
    receiver.deposit(toWithdraw);
  }
}
