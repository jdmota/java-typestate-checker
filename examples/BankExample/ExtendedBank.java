import mungo.lib.Typestate;

@Typestate("ExtendedBank.protocol")
public class ExtendedBank extends Bank {
  public FunnyMoney withdrawAll() {
    return new FunnyMoney(0);
  }
}
