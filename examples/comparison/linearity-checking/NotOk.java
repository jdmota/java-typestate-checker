import java.util.*;
import java.util.function.Supplier;

public class NotOk {
  public static void main1() {
    File f = new File();
    use(f);
    f.read();
  }

  public static void main2() {
    File f = new File();
    use(f);
    use(f);
  }

  public static void main3() {
    File f = new File();
    File f2 = f;
    use(f2);
    f.read();
  }

  public static void main4() {
    File f = new File();
    File f2 = f;
    use(f2);
    use(f);
  }

  public static void main5() {
    File f = new File();
    Supplier<String> fn = () -> {
      return f.read();
    };
    f.close();
    fn.get();
  }

  public static void use(File f) {
    System.out.println(f.read());
    f.close();
  }
}
