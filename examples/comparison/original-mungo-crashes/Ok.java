import java.util.*;
import java.util.function.Supplier;

public class Ok {
  public static void main1() {
    Supplier<String> fn = () -> {
      File f = new File();
      f.read();
      f.close();
      return "";
    };
  }
}
