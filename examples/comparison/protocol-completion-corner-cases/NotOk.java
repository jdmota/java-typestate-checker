import java.util.*;

public class NotOk {
  public static void main1() {
    List<File> list = new LinkedList<>();
    list.add(new File());
  }
  
  public static class FileWrapper {
    public File file = new File();
  }
  
  public static void main2() {
    FileWrapper file = new FileWrapper();
  }
}
