public class ClientCode {

  public static void main(String[] args) {
    Car[] cars = new Car[5];
    Car c = new Car();
    // Car[] cars2 = new Car[]{ c, new SUV(), new Car() };
    Car[][] cars3 = new Car[4][2];
    Car[] cars4 = new Car[5];
    Car[][] cars5 = new Car[5][5];
    c.turnOn();
    Car[][] matrix = new Car[][]{ new Car[]{ c, new SUV(), new Car() }, new Car[]{ c, new SUV(), new Car() }, new Car[]{ c, new SUV(), new Car() } };
  }
}
