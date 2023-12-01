import java.util.*;

public class Util {
  public static List<Object> toList(String[] array) {
    List<Object> list = new ArrayList<Object>();
    for (String item : array) {
      list.add(item);
    }
    return list;
  }
}
