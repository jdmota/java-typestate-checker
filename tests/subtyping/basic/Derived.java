import mungo.lib.Typestate;
import java.util.Random;

@Typestate("Derived.protocol")
// :: error: ([this.rd] did not complete its protocol (found: Shared{java.util.Random} | NoProtocol{java.util.Random, exact=false}))
public class Derived extends Base {
  private Random rd = new Random();

  public boolean hasNext() {
    // :: warning: (this.rd: Shared{java.util.Random} | NoProtocol{java.util.Random, exact=false})
    return rd.nextBoolean();
  }

  public void next() {
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    System.out.println("Base calls next");
  }

  public void remove() {
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    System.out.println("Derived calls remove");
  }
}
