import jatyc.lib.Requires;
import jatyc.lib.Ensures;

public class ExtendedBank extends Bank {
  // :: error: (Parameter [money] should require a supertype of State{Money, Active} (found: Shared{Money}))
  public void deposit(Money money) {

  }

  // :: error: (Return value should be a subtype of State{Money, Active} (found: Shared{Money}))
  public Money withdraw() {
    // :: error: (Incompatible return value: cannot cast from State{Money, Active} to Shared{Money})
    return new Money();
  }

  // :: error: ([money] did not complete its protocol (found: State{Money, Active}))
  // :: error: (Parameter [money] should ensure a subtype of State{Money, Active} (found: Shared{Money}))
  public void touch(@Requires("Active") Money money) {

  }
}
