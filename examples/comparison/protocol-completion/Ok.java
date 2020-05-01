import java.util.*;
import java.util.function.Supplier;

public class Ok {
  public static void main1() {
    File f = new File();
    System.out.println(f.read());
    f.close();
  }

  public static void main2() {
    File f = new File();
    use(f);
  }

  public static void use(File f) {
    System.out.println(f.read());
    f.close();
  }
}
