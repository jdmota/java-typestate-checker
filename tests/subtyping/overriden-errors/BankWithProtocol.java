import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;

@Typestate("BankWithProtocol")
// :: error: (Method [deposit] that is always available should not appear in the protocol)
public class BankWithProtocol extends Bank {
  // Ensure that anytime methods remain anytime
  // No matter if they are overriden or not

  // :: error: (Method should be available anytime since the overridden method is available anytime)
  public @Ensures("Active") Money withdraw() {
    return new Money();
  }
}
