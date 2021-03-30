import mungo.lib.Typestate;
import java.util.Random;

@Typestate("Base.protocol")
public class Base {
  private Random rd = new Random();

  public boolean hasNext() {
    return rd.nextBoolean();
  }

  public void next() {
    System.out.println("Base calls next");
  }
}
