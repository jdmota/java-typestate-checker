import java.util.*;

import jatyc.lib.Nullable;

public class Main {
  public static void main1(String[] args) {
    Iterator<String> it = Arrays.asList(args).iterator();
    @Nullable String value = it.next();
    // :: warning: (value: NoProtocol | Null)
    // :: error: (argument.type.incompatible)
    System.out.println(value);
  }

  public static void main2(String[] args) {
    Iterator<String> it = Arrays.asList(args).iterator();
    // :: error: (assignment.type.incompatible)
    String value = it.next();
    System.out.println(value);
  }
}
