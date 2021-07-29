import jatyc.lib.Typestate;

@Typestate("ExtendedBank")
public class ExtendedBank extends Bank {
  public FunnyMoney withdrawAll() {
    return new FunnyMoney(0);
  }
}
