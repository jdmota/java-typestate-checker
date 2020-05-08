import java.util.function.Supplier;

public class NotOk {
  public static void main1() {
    File f = new File();
  }

  public static void main2() {
    File f = new File();
    use(f);
  }

  public static void use(File f) {

  }
}
