public class ClientCode {

  public static void main(String[] args) {
    int n = 5;
    Car[] cars = new Car[n];
    Car c = new Car();
    Car[] cars2 = new Car[]{c, new SUV(), new Car()};
    Car[][] cars3 = new Car[n][n];
    Car[] cars4 = new Car[5];
    Car[][] cars5 = new Car[5][5];
    c.turnOn();
  }
}
