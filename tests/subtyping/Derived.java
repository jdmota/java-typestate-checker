import mungo.lib.Typestate;
import java.util.Random;

@Typestate("Derived.protocol")
public class Derived extends Base {
  private Random rd = new Random();

  public boolean hasNext() {
    return rd.nextBoolean();
  }

  public void next() {
    System.out.println("Derived calls next");
  }

  public void remove() {
    System.out.println("Derived calls remove");
  }
}
