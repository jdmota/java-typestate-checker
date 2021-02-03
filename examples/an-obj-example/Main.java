import java.lang.Thread;

public class Main {
  public static void example1() throws InterruptedException {
    Obj obj = new Obj();
    obj.init("Hello World!");
    
    Thread t1 = new Thread(() -> {
      System.out.println(obj.read());
    });
    
    Thread t2 = new Thread(() -> {
      System.out.println(obj.read());
    });
    
    t1.start();
    t2.start();
    
    t1.join();
    t2.join();
    
    obj.close();
  }
}
