import jatyc.lib.Utils;

public class ClientCode {
  public static void main(String[] args) {
    /*int x = 5;
    Car[] cars = new Car[x];
    int i = 0;
    for (i = 0; i < 2; i++) {
      // assert Utils.loopInvariant(cars, "OFF", i, "null") : "";
      cars[i] = new Car();
    }
    cars[0].turnOn();
    Car[] cars2 = cars;*/

    int x = 5;
    Car[] cars = new Car[x];
    for (int i = 0; i < x; i++) {
      cars[i] = new Car();
      while (!cars[i].turnOn()) {
        System.out.println("turning on...");
      }
    }
    Car[] cars2 = cars;
  }
}
