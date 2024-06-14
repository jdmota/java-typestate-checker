import jatyc.lib.Utils;

public class ClientCode {

  public static void main(String[] args) {
    int x = 5;
    Car[] cars = new Car[x];
    for (int i = 0; i < 5; i++) {
      // cars[i] = new Car();
      System.out.println(i);
    }
    Car[] cars2 = cars;
  }

  public static void main2() {
    int i = 2;
    boolean cond = true;
    if (cond) i = 5;
    Car[] cars = new Car[7];
    Car c = new Car();
    cars[i] = c;
    c = cars[i];

    while (true) {
      Car[] x = new Car[7];
      assert Utils.loopInvariant(x, "Off", i, "null") : "";
    }
  }
}
