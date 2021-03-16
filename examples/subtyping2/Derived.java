import java.util.Random;

import mungo.lib.Typestate;
@Typestate("Derived.protocol")

public class Derived extends Base{

  private Random rd;

  public Derived() {
    this.rd = new Random();
  }

  public RestrictedStatus offer1() {
    return RestrictedStatus.NO;
  }

  public Status offer2() {
    return rd.nextBoolean() ? Status.OK : Status.NO;
  }

  public void done(){}
}
