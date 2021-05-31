import java.util.ArrayList;
import java.util.List;
import mungo.lib.Typestate;

@Typestate("Bank.protocol")
public class Bank {

  public boolean openAccount(String name, String password) {
    return true;
  }

  public FunnyMoney closeAccount() {
    return new FunnyMoney(0);
  }

  public boolean deposit(FunnyMoney money) {
    return true;
  }

  public boolean withdraw(int amount) {
    return true;
  }

  public int getBalance() {
    return 0;
  }

}
