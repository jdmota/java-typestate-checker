import java.util.function.Supplier;

public class Main {
  public static void main() {
    Supplier<String> fn = () -> {
      File f = new File();
      f.read();
      f.close();
      return "";
    };
  }
}
