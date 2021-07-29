import java.util.*;

public class NotOk {
  public static void main1() {
    List<File> list = new LinkedList<>();
    list.add(new File());
    File f1 = list.get(0);
    File f2 = list.get(0);
    f1.read();
    f1.close();
    f2.read();
    f2.close();
  }
}
