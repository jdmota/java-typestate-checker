import jatyc.lib.Utils;

public class ClientCode {

  public static void main(String[] args) {
    int x = 5;
    Car[] cars = new Car[x];
    for (int i = 0; i < 5; i++) {
      cars[i] = new Car();
      assert Utils.loopInvariant(cars, "null", i, "OFF") : "";
    }
  }
}

