import jatyc.lib.Requires;

public class WrongClientCode {
  public static void example1() {
    FunnyBulb f = new FunnyBulb();
    f.switchMode(); // The tool should report an error here about protocol compliance
  }

  public static void example2() { // The tool should report an error here about protocol completion
    FunnyBulb f = new FunnyBulb();
    while (!f.connect()) { System.out.println("connecting..."); }
  }
}
