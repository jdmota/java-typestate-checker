import java.util.*;

public class Ok {
  public static void main1() {
    File f = new File();
    use(f);
  }

  public static void main2() {
    File f = new File();
    File f2 = f;
    use(f2);
  }

  public static void use(File f) {
    System.out.println(f.read());
    f.close();
  }
}
