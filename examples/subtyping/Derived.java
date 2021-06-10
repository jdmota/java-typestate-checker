import java.util.Random;
import mungo.lib.Typestate;

@Typestate("Derived")
public class Derived extends Base {
  private Random rd;

  public Derived() {
    this.rd = new Random();
  }

  public Status offer1() {
    return Status.NO;
  }

  public Status offer2() {
    return rd.nextBoolean() ? Status.OK : Status.NO;
  }

  public void done() {

  }
}
