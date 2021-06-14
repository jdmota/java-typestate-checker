import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.State;

public class Bank {
  public void deposit(@Requires("Active") Money money) {
    // :: warning: (money: State{Money, Active})
    money.close();
  }

  public @State("Active") Money withdraw() {
    return new Money();
  }

  public void touch(@Requires("Active") @Ensures("Active") final Money money) {

  }
}
