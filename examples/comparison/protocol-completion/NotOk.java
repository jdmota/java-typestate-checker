import java.util.*;
import java.util.function.Supplier;

public class NotOk {
  public static void main1() {
    File f = new File();
  }

  public static void main2() {
    File f = new File();
    System.out.println(f);
  }

  public static void main3() {
    File f = new File();
    use(f);
  }

  public static void main4() {
    File f = new File();
    Supplier<String> fn = () -> {
      return f.read();
    };
    fn.get();
  }

  public static void use(File f) {

  }
}
