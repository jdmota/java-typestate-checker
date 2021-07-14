import jatyc.lib.Requires;
import jatyc.lib.Ensures;

public class Bank {
  public void deposit(@Requires("Active") Money money) {
    // :: warning: (money: State{Money, Active})
    money.close();
  }

  public @Ensures("Active") Money withdraw() {
    return new Money();
  }

  public void touch(@Requires("Active") @Ensures("Active") final Money money) {

  }
}
