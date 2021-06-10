import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Ensures;
import org.checkerframework.checker.jtc.lib.State;

@Typestate("BankWithProtocol")
// :: error: (Method [deposit] should be available anytime since it is available anytime in the super type)
public class BankWithProtocol extends Bank {
  // Ensure that anytime methods remain anytime
  // No matter if they are overriden or not

  // :: error: (Method should be available anytime since the overridden method is available anytime)
  public @State("Active") Money withdraw() {
    return new Money();
  }
}
