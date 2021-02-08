public class Main {
  public static void main(String[] args) {
    Producer producer = new Producer();
    Consumer consumer = new Consumer();
    
    producer.init(consumer);
    producer.produce("Hello World!");
  }
}
