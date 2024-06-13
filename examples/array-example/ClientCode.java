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
}
