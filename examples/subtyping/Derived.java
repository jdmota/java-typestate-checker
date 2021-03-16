import java.util.Random;

import mungo.lib.Typestate;
@Typestate("Derived.protocol")

public class Derived{

  private Random rd;

  public Derived() {
    this.rd = new Random();
  }

  public Status_NO offer1() {
    return Status_NO.NO;
  }

  public Status offer2() {
    return rd.nextBoolean() ? Status.OK : Status.NO;
  }

  public void done(){}
}
