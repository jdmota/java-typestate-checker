import java.util.Random;
import mungo.lib.Typestate;
@Typestate("Base.protocol")
public class Base {

  private Random rd;

  public Base() {
    this.rd = new Random();
  }

  public Status offer1() {
     return rd.nextBoolean() ? Status.OK : Status.NO;
  }

  public Status offer2() {
    return rd.nextBoolean() ? Status.OK : Status.NO;
  }

  public void done(){}
}
