public class ClientCode {

  public static void main(String[] args) {
    Car[] cars = new Car[1];
    Car c = new Car();
    cars[0] = c;
    cars[0].turnOn();
    cars[1] = new Car();
  }
}
