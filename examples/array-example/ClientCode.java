import jatyc.lib.Utils;

public class ClientCode {

  public static void main(String[] args) {
    int x = 5;
    Car[] cars = new Car[x];
    int i = 0;
    for (i = 0; i < 2; i++) {
      assert Utils.loopInvariant(cars, "OFF", i, "null") : "";
      cars[i] = new Car();
    }
    cars[0].turnOn();
  }
}

