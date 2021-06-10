import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Ensures;
import org.checkerframework.checker.jtc.lib.State;

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
